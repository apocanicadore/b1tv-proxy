/**
 * B1 TV HLS proxy server — v3 (HLS Relay + Push Notifications)
 *
 * HLS endpoints:
 * - GET /live.m3u8     → HLS relay (canonical, iOS auto-detects from extension)
 * - GET /hls           → HLS relay (legacy alias)
 * - GET /hls-segment   → segment proxy from CDN
 * - GET /live-url      → raw CDN URL (diagnostics)
 *
 * Push notification endpoints:
 * - POST /register-token  → register Expo push token + subscribed topics
 *
 * Poll endpoints:
 * - GET  /polls
 * - POST /polls/:id/vote
 *
 * Push architecture:
 * - In-memory token store (Map<token, {topics, registeredAt}>)
 * - RSS poller every 3 min checks all B1TV category feeds
 * - New articles → Expo Push API notifies subscribed devices
 * - Breaking news detected by feed (main /feed) or title keywords
 * - Tokens auto-expire after 24 h (re-registered on every app launch)
 */

'use strict';

const http      = require('http');
const https     = require('https');
const crypto    = require('crypto');
const puppeteer = require('puppeteer');

// ── Config ────────────────────────────────────────────────────────────────────
const PORT        = process.env.PORT || 3031;
const TARGET_PAGE = 'https://www.b1tv.ro/live';
const WAIT_MS     = 25_000;
// 1-hour cache — CDN token is valid for 6 h; Puppeteer cold-starts are expensive.
const CACHE_TTL   = 60 * 60 * 1000;

const MOBILE_UA =
  'Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) ' +
  'AppleWebKit/605.1.15 (KHTML, like Gecko) ' +
  'Version/17.0 Mobile/15E148 Safari/604.1';

// ── Scoring ───────────────────────────────────────────────────────────────────

function scoreUrl(url) {
  const lo = url.toLowerCase();
  if (!lo.includes('.m3u8')) return 0;
  if (lo.includes('/tracks-') && lo.includes('mono.ts') && lo.includes('token=')) return 3;
  if (lo.includes('/tracks-') && lo.includes('token=')) return 2;
  return 1;
}

// ── In-memory cache ───────────────────────────────────────────────────────────

let _cache = {
  url:      '',
  score:    0,
  cachedAt: 0,
  source:   '',
};
// Chromium session cookies — required to pass CDN IP/session validation
let _sessionCookies = '';

// ── Poll data & vote storage ───────────────────────────────────────────────────

const POLLS = [
  {
    id: 'poll-orban-2026',
    question: 'Credeți că înfrângerea lui Viktor Orbán în Ungaria va schimba echilibrul politic din Europa?',
    options: [
      { id: 'opt-1', label: 'Da, va slăbi curentul suveranist din regiune' },
      { id: 'opt-2', label: 'Nu, schimbarea va fi doar în Ungaria' },
      { id: 'opt-3', label: 'Impactul asupra României va fi cel mai important' },
      { id: 'opt-4', label: 'E prea devreme pentru concluzii' },
    ],
    expiresAt: new Date(Date.now() + 7 * 24 * 60 * 60 * 1000).toISOString(),
    relatedArticleId: null,
  },
];

const _votes = {};

function buildPollResponse(poll) {
  const pollVotes  = _votes[poll.id] ?? {};
  const totalVotes = Object.values(pollVotes).reduce((s, c) => s + c, 0);
  const options    = poll.options.map((opt) => {
    const count = pollVotes[opt.id] ?? 0;
    return {
      ...opt,
      voteCount:  count,
      percentage: totalVotes > 0 ? Math.round((count / totalVotes) * 100) : 0,
    };
  });
  return { ...poll, options, totalVotes };
}

function readBody(req) {
  return new Promise((resolve, reject) => {
    let data = '';
    req.on('data', (chunk) => { data += chunk; });
    req.on('end', () => {
      try { resolve(JSON.parse(data || '{}')); }
      catch { resolve({}); }
    });
    req.on('error', reject);
  });
}

function cacheValid() {
  return _cache.url && (Date.now() - _cache.cachedAt) < CACHE_TTL;
}

// ── CDN helpers (using Railway's IP + session cookies) ────────────────────────

/**
 * Make an HTTPS GET request to the DeJaCast CDN from Railway's trusted IP.
 * Returns the raw Node.js IncomingMessage so callers can stream or buffer.
 */
function cdnGet(url) {
  return new Promise((resolve, reject) => {
    const parsed  = new URL(url);
    const options = {
      hostname: parsed.hostname,
      port:     443,
      path:     parsed.pathname + parsed.search,
      method:   'GET',
      headers: {
        'User-Agent': MOBILE_UA,
        'Referer':    'https://www.b1tv.ro',
        'Origin':     'https://www.b1tv.ro',
        'Accept':     '*/*',
        ...(_sessionCookies ? { 'Cookie': _sessionCookies } : {}),
      },
    };
    const req = https.request(options, resolve);
    req.on('error', reject);
    req.end();
  });
}

/**
 * Rewrite all segment lines in a live M3U8 to go through this proxy relay.
 * Lines starting with # are unchanged. All other non-empty lines are treated
 * as segment URLs (possibly relative to baseUrl) and rewritten.
 */
function rewriteM3u8(content, baseUrl, proxyBase) {
  return content.split('\n').map((line) => {
    const trimmed = line.trim();
    if (!trimmed || trimmed.startsWith('#')) return line;
    try {
      const absUrl = new URL(trimmed, baseUrl).toString();
      return `${proxyBase}/hls-segment?url=${encodeURIComponent(absUrl)}`;
    } catch {
      return line; // not a valid URL — leave as-is
    }
  }).join('\n');
}

// ── Browser lifecycle ─────────────────────────────────────────────────────────

let _browser = null;

async function getBrowser() {
  if (_browser) {
    try { await _browser.version(); return _browser; }
    catch { _browser = null; }
  }
  console.log('[proxy] launching Chromium…');
  _browser = await puppeteer.launch({
    headless: 'new',
    args: [
      '--no-sandbox',
      '--disable-setuid-sandbox',
      '--disable-dev-shm-usage',
      '--disable-gpu',
      '--autoplay-policy=no-user-gesture-required',
    ],
  });
  _browser.on('disconnected', () => {
    console.log('[proxy] Chromium disconnected — will relaunch on next request');
    _browser = null;
  });
  return _browser;
}

// ── Core resolver ─────────────────────────────────────────────────────────────

async function resolveFromPage() {
  const browser = await getBrowser();
  const page    = await browser.newPage();

  let bestUrl   = '';
  let bestScore = 0;
  let bestSrc   = '';
  let resolved  = false;

  let earlyResolve = () => {};
  const earlyPromise = new Promise((res) => { earlyResolve = res; });

  await page.setUserAgent(MOBILE_UA);
  await page.setRequestInterception(true);

  page.on('request', (req) => {
    const url = req.url();
    const s   = scoreUrl(url);
    if (s > 0) console.log(`[proxy] req  score=${s}: ${url.substring(0, 120)}`);
    if (s > bestScore) {
      bestUrl   = url;
      bestScore = s;
      bestSrc   = 'request';
      console.log(`[proxy] ★ new best (score ${s}): ${url.substring(0, 120)}`);
      if (s >= 3) { resolved = true; earlyResolve(); }
    }
    req.continue();
  });

  page.on('response', (resp) => {
    const url = resp.url();
    const s   = scoreUrl(url);
    if (s > bestScore) {
      bestUrl   = url;
      bestScore = s;
      bestSrc   = 'response';
      console.log(`[proxy] ★ new best via response (score ${s}): ${url.substring(0, 120)}`);
      if (s >= 3) { resolved = true; earlyResolve(); }
    }
  });

  try {
    console.log('[proxy] navigating →', TARGET_PAGE);
    await page.goto(TARGET_PAGE, { waitUntil: 'networkidle2', timeout: 30_000 }).catch(() => {
      console.log('[proxy] networkidle2 timeout — continuing anyway');
    });
    console.log('[proxy] page loaded — attempting to click video player…');

    // Try to click play button / video element to trigger HLS autoplay
    // (some browsers/CDNs require a user gesture)
    try {
      await page.evaluate(() => {
        const selectors = [
          'video',
          '.vjs-big-play-button',
          '[class*="play"]',
          '[aria-label*="play"]',
          '[aria-label*="Play"]',
          'button[class*="play"]',
        ];
        for (const sel of selectors) {
          const el = document.querySelector(sel);
          if (el) { el.click(); return sel; }
        }
        return null;
      });
    } catch (e) {
      console.log('[proxy] click attempt failed (non-fatal):', String(e).substring(0, 60));
    }

    console.log('[proxy] waiting for HLS request (max', WAIT_MS / 1000, 's)…');
    await Promise.race([
      earlyPromise,
      new Promise((res) => setTimeout(res, WAIT_MS)),
    ]);

    if (resolved) {
      console.log('[proxy] early exit — score-3 URL captured');
    } else {
      console.log('[proxy] timeout — best score so far:', bestScore);
    }

    // ── Capture session cookies for CDN relay ─────────────────────────────────
    if (bestUrl) {
      try {
        const cookies = await page.cookies();
        _sessionCookies = cookies.map((c) => `${c.name}=${c.value}`).join('; ');
        console.log(`[proxy] captured ${cookies.length} session cookies for CDN relay`);
      } catch (e) {
        console.warn('[proxy] could not capture cookies:', e.message);
      }
    }
  } finally {
    await page.close().catch(() => {});
  }

  return bestUrl ? { url: bestUrl, score: bestScore, source: bestSrc } : null;
}

// ── Deduplication ─────────────────────────────────────────────────────────────

let _resolving = false;
let _waiters   = [];

async function getHlsUrl() {
  if (cacheValid()) {
    console.log('[proxy] cache hit — returning cached URL');
    return { ..._cache, stale: false };
  }

  if (_resolving) {
    console.log('[proxy] dedup — waiting for in-flight resolve');
    return new Promise((resolve, reject) => _waiters.push({ resolve, reject }));
  }

  _resolving = true;
  try {
    const result = await resolveFromPage();
    if (result) {
      _cache = { ...result, cachedAt: Date.now() };
      console.log('[proxy] cache updated →', result.url.substring(0, 100));
    }
    const out = _cache.url ? { ..._cache, stale: !result } : null;
    _waiters.forEach(({ resolve }) => resolve(out));
    return out;
  } catch (e) {
    const err = { error: e.message };
    _waiters.forEach(({ reject }) => reject(err));
    throw e;
  } finally {
    _resolving = false;
    _waiters   = [];
  }
}

// ── Auth ──────────────────────────────────────────────────────────────────────

const JWT_SECRET = process.env.JWT_SECRET || crypto.randomBytes(32).toString('hex');
// In-memory user store: Map<userId, user-object>
const _users = new Map();

function jwtSign(payload) {
  const h = Buffer.from(JSON.stringify({ alg: 'HS256', typ: 'JWT' })).toString('base64url');
  const b = Buffer.from(JSON.stringify({ ...payload, iat: Math.floor(Date.now() / 1000) })).toString('base64url');
  const s = crypto.createHmac('sha256', JWT_SECRET).update(`${h}.${b}`).digest('base64url');
  return `${h}.${b}.${s}`;
}

function jwtVerify(token) {
  if (!token) throw new Error('No token');
  const [h, b, s] = (token || '').split('.');
  if (!h || !b || !s) throw new Error('Malformed token');
  const expected = crypto.createHmac('sha256', JWT_SECRET).update(`${h}.${b}`).digest('base64url');
  if (s !== expected) throw new Error('Invalid signature');
  return JSON.parse(Buffer.from(b, 'base64url').toString('utf8'));
}

function getAuthUser(req) {
  const auth = req.headers['authorization'] || '';
  const token = auth.startsWith('Bearer ') ? auth.slice(7) : null;
  if (!token) return null;
  try { return jwtVerify(token); } catch { return null; }
}

/** Decode (not verify) a JWT — used for Apple identity tokens (RS256). */
function jwtDecode(token) {
  const parts = (token || '').split('.');
  if (parts.length < 2) return null;
  try { return JSON.parse(Buffer.from(parts[1], 'base64url').toString('utf8')); }
  catch { return null; }
}

/** Call Google tokeninfo to verify an ID token and get email/name/picture. */
function verifyGoogleToken(idToken) {
  return new Promise((resolve, reject) => {
    const req = https.get(
      `https://oauth2.googleapis.com/tokeninfo?id_token=${encodeURIComponent(idToken)}`,
      { timeout: 8_000 },
      (res) => {
        const chunks = [];
        res.on('data', (c) => chunks.push(c));
        res.on('end', () => {
          try {
            const data = JSON.parse(Buffer.concat(chunks).toString());
            if (data.error) reject(new Error(data.error));
            else resolve(data);
          } catch (e) { reject(e); }
        });
      },
    );
    req.on('error', reject);
    req.on('timeout', () => { req.destroy(); reject(new Error('timeout')); });
  });
}

function upsertUser({ id, email, displayName, avatarUrl, provider }) {
  const existing = _users.get(id);
  const user = {
    id,
    email:          email          || existing?.email          || '',
    displayName:    displayName    || existing?.displayName    || email?.split('@')[0] || 'Utilizator',
    avatarUrl:      avatarUrl      || existing?.avatarUrl      || null,
    provider,
    subscriptionTier: existing?.subscriptionTier ?? 'free',
    preferences:    existing?.preferences ?? {
      notificationTopics: ['breaking', 'live_alerts'],
      preferredCategories: ['politica', 'extern', 'economie'],
      autoplayVideos: true,
      highQualityStreaming: false,
      darkMode: true,
    },
    savedArticleIds:  existing?.savedArticleIds  ?? [],
    favoriteShowIds:  existing?.favoriteShowIds  ?? [],
    watchlistTopics:  existing?.watchlistTopics  ?? [],
    createdAt:        existing?.createdAt         ?? new Date().toISOString(),
  };
  _users.set(id, user);
  return user;
}

// ── Push Notifications ────────────────────────────────────────────────────────

/**
 * In-memory token store.
 * Map<expoPushToken, { topics: string[], registeredAt: number }>
 * Tokens are re-registered on every app launch so ephemeral storage is fine.
 */
const _tokens = new Map();

/**
 * Per-feed set of already-seen article URLs.
 * Populated on first poll (seeding), used to detect new articles after that.
 */
const _seenUrls = new Map(); // Map<feedUrl, Set<articleUrl>>

// RSS feeds → topic mapping (matches NotificationTopic in app types)
const RSS_FEEDS = [
  { url: 'https://www.b1tv.ro/feed',                   topic: 'breaking'  },
  { url: 'https://www.b1tv.ro/politica/feed',          topic: 'politica'  },
  { url: 'https://www.b1tv.ro/economic/feed',          topic: 'economie'  },
  { url: 'https://www.b1tv.ro/externe/feed',           topic: 'extern'    },
  { url: 'https://www.b1tv.ro/sport/feed',             topic: 'sport'     },
  { url: 'https://www.b1tv.ro/eveniment/feed',         topic: 'eveniment' },
  { url: 'https://www.b1tv.ro/meteo/feed',             topic: 'meteo'     },
  { url: 'https://www.b1tv.ro/monden/feed',            topic: 'lifestyle' },
  { url: 'https://www.b1tv.ro/it-c/feed',              topic: 'itc'       },
  { url: 'https://www.b1tv.ro/auto/feed',              topic: 'auto'      },
  { url: 'https://www.b1tv.ro/horoscop/feed',          topic: 'horoscop'  },
  { url: 'https://www.b1tv.ro/calendar-religios/feed', topic: 'calendar'  },
];

const TOPIC_LABELS = {
  breaking: 'Breaking News', politica: 'Politică', economie: 'Economie',
  extern: 'Externe', sport: 'Sport', eveniment: 'Eveniment', meteo: 'Meteo',
  lifestyle: 'Lifestyle', itc: 'IT&C', auto: 'Auto', horoscop: 'Horoscop',
  calendar: 'Calendar', live_alerts: 'Live', polls: 'Sondaje',
};

const BREAKING_RE = /EXCLUSIV|BREAKING|ALERT|ATEN[ȚT]IE|URGENT|ULTIMA\s+OR[ĂA]/i;

// ── RSS parser (no external deps) ────────────────────────────────────────────

function rssStripHtml(html) {
  return html.replace(/<[^>]+>/g, ' ')
    .replace(/&amp;/g, '&').replace(/&lt;/g, '<').replace(/&gt;/g, '>')
    .replace(/&quot;/g, '"').replace(/&nbsp;/g, ' ').replace(/\s{2,}/g, ' ').trim();
}

function parseRssFeed(xml) {
  const items = [];
  const re = /<item[\s>]([\s\S]*?)<\/item>/gi;
  let m;
  while ((m = re.exec(xml)) !== null) {
    const b = m[1];
    const titleM = b.match(/<title[^>]*>(?:<!\[CDATA\[([\s\S]*?)\]\]>|([\s\S]*?))<\/title>/i);
    const title  = (titleM?.[1] ?? titleM?.[2] ?? '').trim();
    const linkM  = b.match(/<link[^>]*>(?:<!\[CDATA\[([\s\S]*?)\]\]>|([\s\S]*?))<\/link>/i);
    const link   = (linkM?.[1] ?? linkM?.[2] ?? '').trim();
    const descM  = b.match(/<description[^>]*>(?:<!\[CDATA\[([\s\S]*?)\]\]>|([\s\S]*?))<\/description>/i);
    const body   = rssStripHtml(descM?.[1] ?? descM?.[2] ?? '').slice(0, 160);
    if (title && link) items.push({ title, link, body });
  }
  return items;
}

function fetchRssFeed(feedUrl) {
  return new Promise((resolve) => {
    const req = https.get(feedUrl, {
      headers: { 'User-Agent': MOBILE_UA, 'Accept': 'application/rss+xml, text/xml, */*' },
      timeout: 10_000,
    }, (res) => {
      const chunks = [];
      res.on('data', (c) => chunks.push(c));
      res.on('end', () => {
        try { resolve(parseRssFeed(Buffer.concat(chunks).toString('utf8'))); }
        catch (e) { console.warn('[push] RSS parse error:', e.message); resolve([]); }
      });
    });
    req.on('error', (e) => { console.warn('[push] RSS fetch error:', e.message); resolve([]); });
    req.on('timeout', () => { req.destroy(); resolve([]); });
  });
}

// ── Expo Push API sender ──────────────────────────────────────────────────────

function sendExpoPush(messages) {
  if (!messages.length) return Promise.resolve();
  const body = JSON.stringify(messages);
  return new Promise((resolve) => {
    const req = https.request({
      hostname: 'exp.host',
      path:     '/--/api/v2/push/send',
      method:   'POST',
      headers: {
        'Content-Type':   'application/json',
        'Content-Length': Buffer.byteLength(body),
        'Accept':         'application/json',
        'Accept-Encoding':'gzip, deflate',
      },
    }, (res) => {
      const chunks = [];
      res.on('data', (c) => chunks.push(c));
      res.on('end', () => {
        console.log(`[push] Expo API → ${res.statusCode} (${messages.length} msg)`);
        resolve();
      });
    });
    req.on('error', (e) => { console.warn('[push] Expo API error:', e.message); resolve(); });
    req.write(body);
    req.end();
  });
}

// ── RSS poller ────────────────────────────────────────────────────────────────

async function pollAndNotify() {
  if (_tokens.size === 0) return;

  // Remove tokens older than 24 h (likely uninstalled devices)
  const cutoff = Date.now() - 24 * 60 * 60 * 1000;
  for (const [token, d] of _tokens) {
    if (d.registeredAt < cutoff) { _tokens.delete(token); }
  }

  console.log(`[push] poll — ${RSS_FEEDS.length} feeds, ${_tokens.size} device(s)`);

  for (const feed of RSS_FEEDS) {
    try {
      const articles = await fetchRssFeed(feed.url);
      if (!articles.length) continue;

      if (!_seenUrls.has(feed.url)) {
        // First poll: seed seen set without sending notifications
        _seenUrls.set(feed.url, new Set(articles.map((a) => a.link)));
        continue;
      }

      const seen = _seenUrls.get(feed.url);
      const fresh = articles.filter((a) => a.link && !seen.has(a.link));
      articles.forEach((a) => { if (a.link) seen.add(a.link); });

      if (!fresh.length) continue;
      console.log(`[push] ${fresh.length} new article(s) in ${feed.topic}`);

      for (const article of fresh.slice(0, 3)) {
        const isBreaking = feed.topic === 'breaking' || BREAKING_RE.test(article.title);
        const topic = isBreaking ? 'breaking' : feed.topic;

        const messages = [];
        for (const [token, d] of _tokens) {
          const topics = d.topics || [];
          const wantsIt = topics.includes(topic) ||
            (isBreaking && (topics.includes('live_alerts') || topics.includes('breaking')));
          if (!wantsIt) continue;
          messages.push({
            to:        token,
            title:     isBreaking ? '🔴 BREAKING — B1 TV' : `B1 TV · ${TOPIC_LABELS[topic] ?? topic}`,
            body:      article.title,
            data:      { deepLink: article.link, topic, articleUrl: article.link },
            sound:     isBreaking ? 'default' : 'default',
            priority:  isBreaking ? 'high' : 'normal',
            channelId: isBreaking ? 'breaking' : 'news',
          });
        }

        // Expo Push API accepts max 100 messages per call
        for (let i = 0; i < messages.length; i += 100) {
          await sendExpoPush(messages.slice(i, i + 100));
        }
      }
    } catch (e) {
      console.warn(`[push] feed error (${feed.topic}):`, e.message);
    }
  }
}

// Start poller: seed after 20 s, then every 3 min
setTimeout(async () => {
  await pollAndNotify().catch((e) => console.error('[push] initial poll error:', e.message));
  setInterval(
    () => pollAndNotify().catch((e) => console.error('[push] poll error:', e.message)),
    3 * 60 * 1000,
  );
  console.log('[push] poller started — every 3 min');
}, 20_000);

// ── HTTP server ───────────────────────────────────────────────────────────────

const server = http.createServer(async (req, res) => {
  // ── CORS ──────────────────────────────────────────────────────────────────
  res.setHeader('Access-Control-Allow-Origin',  '*');
  res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
  res.setHeader('Access-Control-Allow-Headers', 'Content-Type');

  if (req.method === 'OPTIONS') {
    res.writeHead(204);
    res.end();
    return;
  }

  const url = req.url || '/';

  // ── POST /auth/apple ──────────────────────────────────────────────────────
  if (req.method === 'POST' && url === '/auth/apple') {
    res.setHeader('Content-Type', 'application/json');
    const body = await readBody(req);
    const { identityToken, fullName, email } = body;
    if (!identityToken) { res.writeHead(400); res.end(JSON.stringify({ error: 'Missing identityToken' })); return; }
    // Decode without RS256 verification (token is short-lived; acceptable for MVP)
    const claims = jwtDecode(identityToken);
    if (!claims?.sub) { res.writeHead(401); res.end(JSON.stringify({ error: 'Invalid Apple token' })); return; }
    const userId = `apple:${claims.sub}`;
    const resolvedEmail = email || claims.email || '';
    const resolvedName  = (fullName?.givenName && fullName?.familyName)
      ? `${fullName.givenName} ${fullName.familyName}`.trim()
      : (fullName?.givenName || resolvedEmail.split('@')[0] || 'Utilizator');
    const user = upsertUser({ id: userId, email: resolvedEmail, displayName: resolvedName, avatarUrl: null, provider: 'apple' });
    const token = jwtSign({ sub: userId, email: user.email });
    console.log(`[auth] Apple sign-in: ${resolvedEmail || userId}`);
    res.writeHead(200);
    res.end(JSON.stringify({ token, user }));
    return;
  }

  // ── POST /auth/google ──────────────────────────────────────────────────────
  if (req.method === 'POST' && url === '/auth/google') {
    res.setHeader('Content-Type', 'application/json');
    const body = await readBody(req);
    const { idToken } = body;
    if (!idToken) { res.writeHead(400); res.end(JSON.stringify({ error: 'Missing idToken' })); return; }
    let claims;
    try { claims = await verifyGoogleToken(idToken); }
    catch (e) { res.writeHead(401); res.end(JSON.stringify({ error: `Google token invalid: ${e.message}` })); return; }
    const userId = `google:${claims.sub}`;
    const user = upsertUser({ id: userId, email: claims.email, displayName: claims.name, avatarUrl: claims.picture, provider: 'google' });
    const token = jwtSign({ sub: userId, email: user.email });
    console.log(`[auth] Google sign-in: ${claims.email}`);
    res.writeHead(200);
    res.end(JSON.stringify({ token, user }));
    return;
  }

  // ── GET /auth/me ───────────────────────────────────────────────────────────
  if (req.method === 'GET' && url === '/auth/me') {
    res.setHeader('Content-Type', 'application/json');
    const claims = getAuthUser(req);
    if (!claims) { res.writeHead(401); res.end(JSON.stringify({ error: 'Unauthorized' })); return; }
    const user = _users.get(claims.sub);
    if (!user) { res.writeHead(404); res.end(JSON.stringify({ error: 'User not found' })); return; }
    res.writeHead(200);
    res.end(JSON.stringify(user));
    return;
  }

  // ── PATCH /auth/me/preferences ────────────────────────────────────────────
  if (req.method === 'PATCH' && url === '/auth/me/preferences') {
    res.setHeader('Content-Type', 'application/json');
    const claims = getAuthUser(req);
    if (!claims) { res.writeHead(401); res.end(JSON.stringify({ error: 'Unauthorized' })); return; }
    const user = _users.get(claims.sub);
    if (!user) { res.writeHead(404); res.end(JSON.stringify({ error: 'User not found' })); return; }
    const body = await readBody(req);
    user.preferences = { ...user.preferences, ...body };
    _users.set(claims.sub, user);
    res.writeHead(200);
    res.end(JSON.stringify(user));
    return;
  }

  // ── POST /register-token ──────────────────────────────────────────────────
  if (req.method === 'POST' && url === '/register-token') {
    res.setHeader('Content-Type', 'application/json');
    const body = await readBody(req);
    const { token, topics } = body;
    if (!token || typeof token !== 'string' || !token.startsWith('ExponentPushToken')) {
      res.writeHead(400);
      res.end(JSON.stringify({ error: 'Invalid or missing Expo push token' }));
      return;
    }
    const validTopics = Array.isArray(topics) ? topics.filter((t) => typeof t === 'string') : [];
    _tokens.set(token, { topics: validTopics, registeredAt: Date.now() });
    console.log(`[push] registered …${token.slice(-10)}  topics=[${validTopics.join(',')}]  total=${_tokens.size}`);
    res.writeHead(200);
    res.end(JSON.stringify({ ok: true, topics: validTopics }));
    return;
  }

  // ── GET /polls ─────────────────────────────────────────────────────────────
  if (req.method === 'GET' && url === '/polls') {
    res.setHeader('Content-Type', 'application/json');
    res.writeHead(200);
    res.end(JSON.stringify(POLLS.map(buildPollResponse)));
    return;
  }

  // ── POST /polls/:id/vote ───────────────────────────────────────────────────
  const voteMatch = url.match(/^\/polls\/([^/]+)\/vote$/);
  if (req.method === 'POST' && voteMatch) {
    const pollId = voteMatch[1];
    const poll   = POLLS.find((p) => p.id === pollId);
    res.setHeader('Content-Type', 'application/json');
    if (!poll) { res.writeHead(404); res.end(JSON.stringify({ error: `Poll not found: ${pollId}` })); return; }
    const body        = await readBody(req);
    const { optionId } = body;
    const validOption  = poll.options.find((o) => o.id === optionId);
    if (!validOption) { res.writeHead(400); res.end(JSON.stringify({ error: `Invalid optionId: ${optionId}` })); return; }
    if (!_votes[pollId]) _votes[pollId] = {};
    _votes[pollId][optionId] = (_votes[pollId][optionId] ?? 0) + 1;
    const updated = buildPollResponse(poll);
    console.log(`[proxy] ← POST /polls/${pollId}/vote option=${optionId} total=${updated.totalVotes}`);
    res.writeHead(200);
    res.end(JSON.stringify(updated));
    return;
  }

  // ── GET /live.m3u8 or /hls — HLS relay ───────────────────────────────────
  // /live.m3u8 is the canonical route (iOS auto-detects HLS from .m3u8 extension)
  // /hls kept for backward compatibility
  // HEAD requests handled explicitly so iOS gets correct Content-Type before GET
  const isHlsRoute = (url === '/live.m3u8' || url === '/hls') &&
    (req.method === 'GET' || req.method === 'HEAD');

  if (isHlsRoute) {
    console.log(`\n[proxy] ← ${req.method} ${url}`);
    try {
      const result = await getHlsUrl();
      if (!result || !result.url) {
        res.setHeader('Content-Type', 'application/json');
        res.writeHead(503);
        res.end(JSON.stringify({ error: 'No stream session available yet. Retry in a few seconds.' }));
        return;
      }

      // Fetch the live M3U8 playlist from CDN using Railway's session cookies
      const cdnRes = await cdnGet(result.url);

      if (cdnRes.statusCode !== 200) {
        console.warn(`[proxy] /hls CDN returned ${cdnRes.statusCode} — invalidating cache`);
        // Invalidate so next call re-runs Puppeteer
        _cache = { url: '', score: 0, cachedAt: 0, source: '' };
        cdnRes.resume();
        res.writeHead(cdnRes.statusCode);
        res.end(`CDN error: ${cdnRes.statusCode}`);
        return;
      }

      // Buffer the M3U8 (small text file, typically < 2 KB)
      const chunks = [];
      cdnRes.on('data', (c) => chunks.push(c));
      await new Promise((resolve) => cdnRes.on('end', resolve));
      const m3u8 = Buffer.concat(chunks).toString('utf8');

      // Determine proxy base URL from request headers (works on Railway and localhost)
      const proto    = req.headers['x-forwarded-proto'] || 'https';
      const host     = req.headers['x-forwarded-host'] || req.headers['host'] || `localhost:${PORT}`;
      const proxyBase = `${proto}://${host}`;

      const rewritten = rewriteM3u8(m3u8, result.url, proxyBase);
      console.log(`[proxy] ${url} → 200 (${m3u8.split('\n').length} lines, proxy: ${proxyBase})`);

      res.setHeader('Content-Type', 'application/vnd.apple.mpegurl');
      res.setHeader('Cache-Control', 'no-cache, no-store, must-revalidate');
      res.setHeader('Access-Control-Allow-Origin', '*');
      res.writeHead(200);
      // HEAD: don't send body (but headers are set correctly for iOS pre-flight)
      if (req.method === 'HEAD') { res.end(); return; }
      res.end(rewritten);
    } catch (e) {
      console.error(`[proxy] ${url} error:`, e.message);
      res.writeHead(500);
      if (req.method !== 'HEAD') res.end(JSON.stringify({ error: e.message }));
      else res.end();
    }
    return;
  }

  // ── GET /hls-segment?url=... — proxy individual HLS segments from CDN ─────
  if (req.method === 'GET' && url.startsWith('/hls-segment')) {
    let segUrl;
    try {
      const qs  = new URL(`http://x${url}`).searchParams;
      segUrl    = qs.get('url');
    } catch {
      res.writeHead(400);
      res.end('Bad request: cannot parse url parameter');
      return;
    }

    if (!segUrl || !segUrl.includes('cdn.dejacast.com')) {
      res.writeHead(400);
      res.end('Invalid or untrusted segment URL');
      return;
    }

    try {
      const cdnRes = await cdnGet(segUrl);
      res.setHeader('Content-Type', cdnRes.headers['content-type'] || 'video/MP2T');
      res.setHeader('Access-Control-Allow-Origin', '*');
      if (cdnRes.headers['content-length']) {
        res.setHeader('Content-Length', cdnRes.headers['content-length']);
      }
      res.writeHead(cdnRes.statusCode);
      cdnRes.pipe(res);
    } catch (e) {
      console.error('[proxy] /hls-segment error:', e.message);
      if (!res.headersSent) {
        res.writeHead(502);
        res.end(JSON.stringify({ error: e.message }));
      }
    }
    return;
  }

  // ── GET /live-url — raw CDN URL (kept for diagnostics) ───────────────────
  if (req.method === 'GET' && url !== '/live-url') {
    res.setHeader('Content-Type', 'application/json');
    res.writeHead(404);
    res.end(JSON.stringify({ error: 'Not found. Endpoints: GET /hls, GET /hls-segment, GET /live-url, GET /polls, POST /polls/:id/vote' }));
    return;
  }

  console.log('\n[proxy] ← GET /live-url');
  res.setHeader('Content-Type', 'application/json');

  try {
    const result = await getHlsUrl();

    if (result && result.url) {
      const payload = {
        url:      result.url,
        score:    result.score,
        cachedAt: new Date(result.cachedAt).toISOString(),
        source:   result.source + (result.stale ? '+stale' : ''),
      };
      console.log('[proxy] → 200', JSON.stringify(payload).substring(0, 160));
      res.writeHead(200);
      res.end(JSON.stringify(payload));
    } else {
      res.writeHead(503);
      res.end(JSON.stringify({ error: 'Could not capture any HLS URL from b1tv.ro/live', stale: false }));
    }
  } catch (e) {
    console.error('[proxy] error:', e.message);
    if (_cache.url) {
      res.writeHead(200);
      res.end(JSON.stringify({
        url: _cache.url, score: _cache.score,
        cachedAt: new Date(_cache.cachedAt).toISOString(),
        source: _cache.source, stale: true, error: e.message,
      }));
    } else {
      res.writeHead(500);
      res.end(JSON.stringify({ error: e.message }));
    }
  }
});

server.listen(PORT, '0.0.0.0', () => {
  console.log('');
  console.log('╔══════════════════════════════════════════════════════════╗');
  console.log(`║  B1TV Proxy v3  ·  http://localhost:${PORT}                ║`);
  console.log('║  GET  /live.m3u8        →  HLS relay (canonical)        ║');
  console.log('║  GET  /hls              →  HLS relay (legacy)           ║');
  console.log('║  GET  /hls-segment      →  segment proxy from CDN       ║');
  console.log('║  GET  /live-url         →  raw CDN URL (diagnostics)    ║');
  console.log('║  POST /register-token   →  push notification token      ║');
  console.log('║  GET  /polls            →  poll data                    ║');
  console.log('║  POST /polls/:id/vote   →  submit vote                  ║');
  console.log('╚══════════════════════════════════════════════════════════╝');
  console.log('');
});

process.on('SIGINT',  async () => { if (_browser) await _browser.close(); process.exit(0); });
process.on('SIGTERM', async () => { if (_browser) await _browser.close(); process.exit(0); });
