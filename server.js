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
const { Pool }  = require('pg');

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

// ── Rate limiter ──────────────────────────────────────────────────────────────
// Sliding-window counters per IP. No external dependencies.
const _rateLimitStore = new Map(); // ip -> { count, windowStart }

function rateLimit(req, res, { maxRequests = 20, windowMs = 60_000 } = {}) {
  const ip = req.headers['x-forwarded-for']?.split(',')[0]?.trim() || req.socket.remoteAddress || 'unknown';
  const now = Date.now();
  const entry = _rateLimitStore.get(ip);

  if (!entry || now - entry.windowStart > windowMs) {
    _rateLimitStore.set(ip, { count: 1, windowStart: now });
    return false; // allowed
  }

  entry.count += 1;
  if (entry.count > maxRequests) {
    res.setHeader('Retry-After', Math.ceil(windowMs / 1000));
    res.writeHead(429, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({ error: 'Too many requests' }));
    return true; // blocked
  }
  return false; // allowed
}

// Clean stale entries every 5 minutes to avoid memory leaks
setInterval(() => {
  const cutoff = Date.now() - 5 * 60_000;
  for (const [ip, entry] of _rateLimitStore) {
    if (entry.windowStart < cutoff) _rateLimitStore.delete(ip);
  }
}, 5 * 60_000);

const MAX_BODY_BYTES = 64 * 1024; // 64 KB

function readBody(req) {
  return new Promise((resolve, reject) => {
    let data = '';
    let size = 0;
    req.on('data', (chunk) => {
      size += chunk.length;
      if (size > MAX_BODY_BYTES) {
        req.destroy();
        return reject(new Error('Request body too large'));
      }
      data += chunk;
    });
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
      // Encode CDN URL as base64url path to avoid Railway/Fastly WAF blocking
      // requests that contain "token=" in the query string.
      const encoded = Buffer.from(absUrl).toString('base64url');
      return `${proxyBase}/seg/${encoded}`;
    } catch {
      return line;
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

// ── PostgreSQL ────────────────────────────────────────────────────────────────

const _pool = process.env.DATABASE_URL
  ? new Pool({ connectionString: process.env.DATABASE_URL, ssl: { rejectUnauthorized: process.env.DB_REJECT_UNAUTHORIZED !== 'false' } })
  : null;

async function dbQuery(sql, params = []) {
  if (!_pool) return null;
  const client = await _pool.connect();
  try { return await client.query(sql, params); }
  finally { client.release(); }
}

async function initSchema() {
  if (!_pool) { console.log('[db] No DATABASE_URL — email/password auth unavailable'); return; }
  await dbQuery(`
    CREATE TABLE IF NOT EXISTS users (
      id           TEXT PRIMARY KEY,
      email        TEXT UNIQUE,
      password_hash TEXT,
      display_name TEXT,
      avatar_url   TEXT,
      provider     TEXT    DEFAULT 'email',
      subscription_tier TEXT DEFAULT 'free',
      preferences  JSONB   DEFAULT '{}',
      saved_article_ids  TEXT[] DEFAULT ARRAY[]::TEXT[],
      favorite_show_ids  TEXT[] DEFAULT ARRAY[]::TEXT[],
      watchlist_topics   TEXT[] DEFAULT ARRAY[]::TEXT[],
      created_at   TIMESTAMPTZ DEFAULT NOW(),
      updated_at   TIMESTAMPTZ DEFAULT NOW()
    );
    CREATE TABLE IF NOT EXISTS password_reset_tokens (
      id         UUID PRIMARY KEY DEFAULT gen_random_uuid(),
      user_id    TEXT REFERENCES users(id) ON DELETE CASCADE,
      token      TEXT UNIQUE NOT NULL,
      expires_at TIMESTAMPTZ NOT NULL,
      used       BOOLEAN DEFAULT FALSE,
      created_at TIMESTAMPTZ DEFAULT NOW()
    );
  `);
  console.log('[db] Schema ready');
}

initSchema().catch((e) => console.error('[db] Schema init error:', e.message));

// ── Password helpers ──────────────────────────────────────────────────────────

function hashPassword(password) {
  const salt = crypto.randomBytes(16).toString('hex');
  const hash = crypto.pbkdf2Sync(password, salt, 100_000, 64, 'sha512').toString('hex');
  return `${salt}:${hash}`;
}

function verifyPassword(password, stored) {
  const [salt, hash] = stored.split(':');
  if (!salt || !hash) return false;
  const attempt = crypto.pbkdf2Sync(password, salt, 100_000, 64, 'sha512').toString('hex');
  try {
    return crypto.timingSafeEqual(Buffer.from(hash, 'hex'), Buffer.from(attempt, 'hex'));
  } catch { return false; }
}

// ── Email (Resend) ────────────────────────────────────────────────────────────

const RESEND_API_KEY = process.env.RESEND_API_KEY;
const FROM_EMAIL     = process.env.FROM_EMAIL || 'onboarding@resend.dev';

async function sendEmail({ to, subject, html }) {
  if (!RESEND_API_KEY) { console.warn('[email] No RESEND_API_KEY set'); return; }
  try {
    const res = await fetch('https://api.resend.com/emails', {
      method:  'POST',
      headers: { 'Authorization': `Bearer ${RESEND_API_KEY}`, 'Content-Type': 'application/json' },
      body:    JSON.stringify({ from: FROM_EMAIL, to: [to], subject, html }),
    });
    if (!res.ok) console.warn('[email] Send failed:', await res.text());
    else console.log('[email] Sent to', to);
  } catch (e) { console.warn('[email] Error:', e.message); }
}

// ── Auth ──────────────────────────────────────────────────────────────────────

if (!process.env.JWT_SECRET) {
  if (process.env.NODE_ENV === 'production') {
    console.error('[FATAL] JWT_SECRET environment variable is required in production. Set it in Railway Variables.');
    process.exit(1);
  } else {
    console.warn('[WARN] JWT_SECRET not set — using ephemeral key. All sessions will be invalidated on restart. Set JWT_SECRET for persistent sessions.');
  }
}
const JWT_SECRET = process.env.JWT_SECRET || crypto.randomBytes(32).toString('hex');
// In-memory user store: Map<userId, user-object>
const _users = new Map();

const JWT_TTL_SECONDS = 30 * 24 * 60 * 60; // 30 days

function jwtSign(payload) {
  const now = Math.floor(Date.now() / 1000);
  const h = Buffer.from(JSON.stringify({ alg: 'HS256', typ: 'JWT' })).toString('base64url');
  const b = Buffer.from(JSON.stringify({ ...payload, iat: now, exp: now + JWT_TTL_SECONDS })).toString('base64url');
  const s = crypto.createHmac('sha256', JWT_SECRET).update(`${h}.${b}`).digest('base64url');
  return `${h}.${b}.${s}`;
}

function jwtVerify(token) {
  if (!token) throw new Error('No token');
  const [h, b, s] = (token || '').split('.');
  if (!h || !b || !s) throw new Error('Malformed token');
  const expected = crypto.createHmac('sha256', JWT_SECRET).update(`${h}.${b}`).digest('base64url');
  if (s !== expected) throw new Error('Invalid signature');
  const payload = JSON.parse(Buffer.from(b, 'base64url').toString('utf8'));
  if (payload.exp && Math.floor(Date.now() / 1000) > payload.exp) throw new Error('Token expired');
  return payload;
}

function getAuthUser(req) {
  const auth = req.headers['authorization'] || '';
  const token = auth.startsWith('Bearer ') ? auth.slice(7) : null;
  if (!token) return null;
  try { return jwtVerify(token); } catch { return null; }
}

// ── Apple Sign-In JWKS verification ───────────────────────────────────────────
// Apple public keys are cached for 24 h; token signature is verified with RS256.
let _appleJwks = null;
let _appleJwksCachedAt = 0;
const APPLE_JWKS_TTL_MS = 24 * 60 * 60 * 1000;

function fetchAppleJwks() {
  if (_appleJwks && Date.now() - _appleJwksCachedAt < APPLE_JWKS_TTL_MS) {
    return Promise.resolve(_appleJwks);
  }
  return new Promise((resolve, reject) => {
    const req = https.get(
      'https://appleid.apple.com/auth/keys',
      { timeout: 8_000 },
      (res) => {
        const chunks = [];
        res.on('data', (c) => chunks.push(c));
        res.on('end', () => {
          try {
            const data = JSON.parse(Buffer.concat(chunks).toString());
            _appleJwks = data.keys;
            _appleJwksCachedAt = Date.now();
            resolve(_appleJwks);
          } catch (e) { reject(e); }
        });
        res.on('error', reject);
      },
    );
    req.on('error', reject);
    req.on('timeout', () => { req.destroy(); reject(new Error('Apple JWKS fetch timeout')); });
  });
}

/**
 * Verify an Apple identityToken (RS256 JWT).
 * Checks: signature (JWKS), iss, aud, exp.
 * Requires Node >=18 (crypto.createPublicKey accepts JWK natively).
 */
async function verifyAppleToken(identityToken) {
  const parts = (identityToken || '').split('.');
  if (parts.length !== 3) throw new Error('Malformed Apple token');

  let header, payload;
  try {
    header  = JSON.parse(Buffer.from(parts[0], 'base64url').toString('utf8'));
    payload = JSON.parse(Buffer.from(parts[1], 'base64url').toString('utf8'));
  } catch { throw new Error('Cannot parse Apple token'); }

  // 1. Expiry
  const now = Math.floor(Date.now() / 1000);
  if (payload.exp && now > payload.exp) throw new Error('Apple token expired');

  // 2. Issuer
  if (payload.iss !== 'https://appleid.apple.com') throw new Error('Invalid Apple token issuer');

  // 3. Audience (must match iOS bundle ID; also allow Service ID for web flows)
  const BUNDLE_ID = process.env.APPLE_BUNDLE_ID || 'ro.b1tv.app';
  if (payload.aud !== BUNDLE_ID) {
    throw new Error(`Invalid Apple token audience: ${payload.aud} (expected ${BUNDLE_ID})`);
  }

  // 4. Find matching public key by kid
  const keys = await fetchAppleJwks();
  const jwk  = keys.find((k) => k.kid === header.kid);
  if (!jwk) throw new Error(`Apple signing key not found (kid: ${header.kid})`);

  // 5. Verify RS256 signature using Node.js built-in crypto
  const publicKey    = crypto.createPublicKey({ key: jwk, format: 'jwk' });
  const signingInput = `${parts[0]}.${parts[1]}`;
  const signature    = Buffer.from(parts[2], 'base64url');
  const verifier     = crypto.createVerify('RSA-SHA256');
  verifier.update(signingInput);
  const valid = verifier.verify(publicKey, signature);
  if (!valid) throw new Error('Apple token signature invalid');

  return payload;
}

// ── Google Sign-In JWKS verification ─────────────────────────────────────────
// Replaces the deprecated tokeninfo endpoint with local RS256 verification.
let _googleJwks = null;
let _googleJwksCachedAt = 0;
const GOOGLE_JWKS_TTL_MS = 6 * 60 * 60 * 1000; // 6 h (Google rotates keys ~daily)

function fetchGoogleJwks() {
  if (_googleJwks && Date.now() - _googleJwksCachedAt < GOOGLE_JWKS_TTL_MS) {
    return Promise.resolve(_googleJwks);
  }
  return new Promise((resolve, reject) => {
    const req = https.get(
      'https://www.googleapis.com/oauth2/v3/certs',
      { timeout: 8_000 },
      (res) => {
        const chunks = [];
        res.on('data', (c) => chunks.push(c));
        res.on('end', () => {
          try {
            const data = JSON.parse(Buffer.concat(chunks).toString());
            _googleJwks = data.keys;
            _googleJwksCachedAt = Date.now();
            resolve(_googleJwks);
          } catch (e) { reject(e); }
        });
        res.on('error', reject);
      },
    );
    req.on('error', reject);
    req.on('timeout', () => { req.destroy(); reject(new Error('Google JWKS fetch timeout')); });
  });
}

/**
 * Verify a Google ID token (RS256 JWT) locally.
 * Checks: signature (JWKS), iss, aud (client IDs), exp.
 * Returns the verified payload with sub, email, name, picture, etc.
 */
async function verifyGoogleToken(idToken) {
  const parts = (idToken || '').split('.');
  if (parts.length !== 3) throw new Error('Malformed Google token');

  let header, payload;
  try {
    header  = JSON.parse(Buffer.from(parts[0], 'base64url').toString('utf8'));
    payload = JSON.parse(Buffer.from(parts[1], 'base64url').toString('utf8'));
  } catch { throw new Error('Cannot parse Google token'); }

  // 1. Expiry
  const now = Math.floor(Date.now() / 1000);
  if (payload.exp && now > payload.exp) throw new Error('Google token expired');

  // 2. Issuer
  if (payload.iss !== 'accounts.google.com' && payload.iss !== 'https://accounts.google.com') {
    throw new Error(`Invalid Google token issuer: ${payload.iss}`);
  }

  // 3. Audience — must match one of our configured client IDs
  const allowedAuds = [
    process.env.GOOGLE_WEB_CLIENT_ID,
    process.env.GOOGLE_IOS_CLIENT_ID,
    process.env.GOOGLE_ANDROID_CLIENT_ID,
  ].filter(Boolean);

  if (allowedAuds.length > 0 && !allowedAuds.includes(payload.aud)) {
    throw new Error(`Invalid Google token audience: ${payload.aud}`);
  }

  // 4. Find matching public key by kid
  const keys = await fetchGoogleJwks();
  const jwk  = keys.find((k) => k.kid === header.kid);
  if (!jwk) throw new Error(`Google signing key not found (kid: ${header.kid})`);

  // 5. Verify RS256 signature (Node 18+ crypto supports JWK natively)
  const publicKey    = crypto.createPublicKey({ key: jwk, format: 'jwk' });
  const signingInput = `${parts[0]}.${parts[1]}`;
  const signature    = Buffer.from(parts[2], 'base64url');
  const verifier     = crypto.createVerify('RSA-SHA256');
  verifier.update(signingInput);
  const valid = verifier.verify(publicKey, signature);
  if (!valid) throw new Error('Google token signature invalid');

  if (!payload.email_verified) throw new Error('Google email not verified');

  return payload;
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

  // Persist to PostgreSQL asynchronously (non-blocking)
  if (_pool) {
    const prefs = JSON.stringify(user.preferences);
    dbQuery(`
      INSERT INTO users (id, email, display_name, avatar_url, provider, subscription_tier, preferences)
      VALUES ($1, $2, $3, $4, $5, $6, $7)
      ON CONFLICT (id) DO UPDATE SET
        email         = COALESCE(EXCLUDED.email, users.email),
        display_name  = COALESCE(EXCLUDED.display_name, users.display_name),
        avatar_url    = COALESCE(EXCLUDED.avatar_url, users.avatar_url),
        updated_at    = NOW()
    `, [id, user.email, user.displayName, user.avatarUrl, provider, user.subscriptionTier, prefs])
      .catch((e) => console.warn('[db] upsertUser error:', e.message));
  }

  return user;
}

/** Load a user from PostgreSQL into the in-memory cache. */
async function loadUserFromDb(id) {
  const res = await dbQuery('SELECT * FROM users WHERE id = $1', [id]);
  if (!res || !res.rows.length) return null;
  const row = res.rows[0];
  const user = {
    id: row.id,
    email: row.email,
    displayName: row.display_name,
    avatarUrl: row.avatar_url,
    provider: row.provider,
    subscriptionTier: row.subscription_tier,
    preferences: row.preferences ?? {
      notificationTopics: ['breaking', 'live_alerts'],
      preferredCategories: ['politica', 'extern', 'economie'],
      autoplayVideos: true,
      highQualityStreaming: false,
      darkMode: true,
    },
    savedArticleIds: row.saved_article_ids ?? [],
    favoriteShowIds: row.favorite_show_ids ?? [],
    watchlistTopics: row.watchlist_topics  ?? [],
    createdAt: row.created_at,
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
      // Add new links to seen set; cap at 500 entries to prevent unbounded growth
      articles.forEach((a) => {
        if (!a.link) return;
        seen.add(a.link);
        if (seen.size > 500) {
          // Delete the oldest entry (Sets preserve insertion order)
          const oldest = seen.values().next().value;
          seen.delete(oldest);
        }
      });

      if (!fresh.length) continue;
      console.log(`[push] ${fresh.length} new article(s) in ${feed.topic}`);

      for (const article of fresh.slice(0, 3)) {
        // For the main /feed (mapped to 'breaking'), only notify if the title
        // actually contains breaking-news keywords — otherwise it would fire
        // for every monden/lifestyle/sport article published on the main feed.
        const isMainFeed = feed.url.endsWith('/feed') && !feed.url.includes('/monden') &&
          !feed.url.includes('/sport') && !feed.url.includes('/politic') &&
          feed.url === 'https://www.b1tv.ro/feed';
        if (isMainFeed && !BREAKING_RE.test(article.title)) continue;

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

// ── AI News Summary ───────────────────────────────────────────────────────────

const AI_FEEDS = [
  { url: 'https://www.b1tv.ro/feed',              category: 'breaking' },
  { url: 'https://www.b1tv.ro/politica/feed',     category: 'politica' },
  { url: 'https://www.b1tv.ro/externe/feed',      category: 'extern' },
  { url: 'https://www.b1tv.ro/economic/feed',     category: 'economie' },
  { url: 'https://www.b1tv.ro/eveniment/feed',    category: 'eveniment' },
];

const SUMMARY_CACHE_TTL_MS = 15 * 60 * 1000; // 15 minutes
let _summaryCache = null;
let _summaryCachedAt = 0;

function fetchFeedXml(url) {
  return new Promise((resolve, reject) => {
    const req = https.get(url, {
      timeout: 8_000,
      headers: {
        'User-Agent': 'Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) AppleWebKit/605.1.15 Mobile/15E148',
        'Accept': 'application/rss+xml, application/xml, text/xml, */*',
      },
    }, (res) => {
      const chunks = [];
      res.on('data', (c) => chunks.push(c));
      res.on('end', () => resolve(Buffer.concat(chunks).toString('utf8')));
    });
    req.on('error', reject);
    req.on('timeout', () => { req.destroy(); reject(new Error('timeout')); });
  });
}

function parseRssItems(xml) {
  const items = [];
  const re = /<item[\s>]([\s\S]*?)<\/item>/gi;
  let m;
  while ((m = re.exec(xml)) !== null) {
    const block = m[1];
    const titleMatch = block.match(/<title[^>]*>(?:<!\[CDATA\[)?([\s\S]*?)(?:\]\]>)?<\/title>/i);
    const title = (titleMatch?.[1] ?? '').trim().replace(/&amp;/g, '&').replace(/&lt;/g, '<').replace(/&gt;/g, '>');
    const pubDateMatch = block.match(/<pubDate[^>]*>([\s\S]*?)<\/pubDate>/i);
    const pubDate = pubDateMatch?.[1]?.trim() ?? '';
    const linkMatch = block.match(/<link[^>]*>([\s\S]*?)<\/link>/i);
    const link = linkMatch?.[1]?.trim() ?? '';
    if (title && pubDate) items.push({ title, pubDate: new Date(pubDate), link });
  }
  return items;
}

async function buildAISummary() {
  const threeHoursAgo = new Date(Date.now() - 3 * 60 * 60 * 1000);

  // Fetch all feeds in parallel
  const feedResults = await Promise.allSettled(
    AI_FEEDS.map(async ({ url, category }) => {
      const xml = await fetchFeedXml(url);
      return parseRssItems(xml).map((item) => ({ ...item, category }));
    }),
  );

  const allItems = feedResults
    .flatMap((r) => r.status === 'fulfilled' ? r.value : [])
    .filter((item) => item.pubDate >= threeHoursAgo)
    .sort((a, b) => b.pubDate - a.pubDate);

  // Deduplicate by title similarity
  const seen = new Set();
  const unique = allItems.filter((item) => {
    const key = item.title.toLowerCase().replace(/\s+/g, ' ').slice(0, 60);
    if (seen.has(key)) return false;
    seen.add(key);
    return true;
  });

  if (unique.length === 0) {
    return { summary: 'Nu există știri noi în ultimele 3 ore.', articles: [], generatedAt: new Date().toISOString(), articleCount: 0 };
  }

  const sourcesSlice = unique.slice(0, 25);
  const headlines = sourcesSlice
    .map((item, i) => `${i + 1}. [${item.category}] ${item.title}`)
    .join('\n');

  const prompt = `Ești un jurnalist senior la B1 TV România. Ai în față ${sourcesSlice.length} titluri de știri publicate în ultimele 3 ore.

Identifică cel mult 6 subiecte principale și pentru fiecare scrie:
- un titlu scurt și clar (max 8 cuvinte)
- un rezumat de 2-3 propoziții în română, obiectiv și profesional
- numărul știrii din lista de mai jos care este cea mai relevantă sursă pentru acel subiect

Răspunde EXCLUSIV cu un obiect JSON valid, fără text suplimentar, fără markdown, fără backtick-uri:
{"topics":[{"title":"...","body":"...","article_index":N}]}

Titlurile:
${headlines}`;

  const openaiRes = await fetch('https://api.openai.com/v1/chat/completions', {
    method: 'POST',
    headers: {
      'Authorization': `Bearer ${process.env.OPENAI_API_KEY}`,
      'Content-Type': 'application/json',
    },
    body: JSON.stringify({
      model: 'gpt-4o-mini',
      messages: [{ role: 'user', content: prompt }],
      max_tokens: 700,
      temperature: 0.3,
      response_format: { type: 'json_object' },
    }),
  });

  if (!openaiRes.ok) {
    const err = await openaiRes.text();
    throw new Error(`OpenAI error ${openaiRes.status}: ${err.slice(0, 200)}`);
  }

  const openaiData = await openaiRes.json();
  const raw = openaiData.choices?.[0]?.message?.content?.trim() ?? '{"topics":[]}';
  let parsed;
  try { parsed = JSON.parse(raw); } catch { parsed = { topics: [] }; }

  const topics = (parsed.topics ?? []).slice(0, 6).map((t) => {
    const src = sourcesSlice[t.article_index - 1];
    return {
      title: t.title ?? '',
      body: t.body ?? '',
      article: src ? {
        index: t.article_index,
        title: src.title,
        link: src.link,
        category: src.category,
        publishedAt: src.pubDate.toISOString(),
      } : null,
    };
  });

  return {
    topics,
    generatedAt: new Date().toISOString(),
    articleCount: unique.length,
  };
}

// ── HTTP server ───────────────────────────────────────────────────────────────

// Allowed CORS origins: Expo Go, local dev, and production Railway domain
const ALLOWED_ORIGINS = (process.env.ALLOWED_ORIGINS || '')
  .split(',')
  .map(o => o.trim())
  .filter(Boolean);

const DEFAULT_ALLOWED_ORIGINS = [
  'https://b1tv.up.railway.app',
  'exp://',          // Expo Go (prefix match handled below)
  'http://localhost',
];

function corsOrigin(req) {
  const origin = req.headers['origin'] || '';
  if (!origin) return null; // native app requests have no Origin header
  const allowed = [...DEFAULT_ALLOWED_ORIGINS, ...ALLOWED_ORIGINS];
  if (allowed.some(o => origin === o || origin.startsWith(o))) return origin;
  return null;
}

const server = http.createServer(async (req, res) => {
  // ── CORS ──────────────────────────────────────────────────────────────────
  const allowedOrigin = corsOrigin(req) || (process.env.NODE_ENV !== 'production' ? '*' : null);
  if (allowedOrigin) {
    res.setHeader('Access-Control-Allow-Origin',  allowedOrigin);
    res.setHeader('Access-Control-Allow-Methods', 'GET, POST, PATCH, DELETE, OPTIONS');
    res.setHeader('Access-Control-Allow-Headers', 'Content-Type, Authorization');
    res.setHeader('Vary', 'Origin');
  }

  if (req.method === 'OPTIONS') {
    res.writeHead(204);
    res.end();
    return;
  }

  // Normalize URL: strip query string for route matching to avoid bypasses
  const url = (req.url || '/').split('?')[0].split('#')[0];

  // ── Rate limiting on sensitive endpoints ──────────────────────────────────
  const isAuthRoute = url.startsWith('/auth/');
  const isSensitive = isAuthRoute || url === '/ai-summary' || /^\/polls\/[^/]+\/vote$/.test(url);
  if (isSensitive) {
    const limits = isAuthRoute
      ? { maxRequests: 10, windowMs: 60_000 }   // 10 auth calls / min
      : { maxRequests: 30, windowMs: 60_000 };   // 30 calls / min for others
    if (rateLimit(req, res, limits)) return;
  }

  // ── GET /ai-summary ───────────────────────────────────────────────────────
  if (req.method === 'GET' && url === '/ai-summary') {
    res.setHeader('Content-Type', 'application/json');
    try {
      // Serve from cache if fresh
      if (_summaryCache && Date.now() - _summaryCachedAt < SUMMARY_CACHE_TTL_MS) {
        console.log('[ai-summary] cache hit');
        res.writeHead(200);
        res.end(JSON.stringify({ ..._summaryCache, cached: true }));
        return;
      }
      if (!process.env.OPENAI_API_KEY) {
        res.writeHead(503);
        res.end(JSON.stringify({ error: 'OPENAI_API_KEY not configured' }));
        return;
      }
      console.log('[ai-summary] generating...');
      const result = await buildAISummary();
      _summaryCache = result;
      _summaryCachedAt = Date.now();
      res.writeHead(200);
      res.end(JSON.stringify(result));
      console.log(`[ai-summary] done — ${result.articleCount} articles`);
    } catch (e) {
      console.error('[ai-summary] error:', e.message);
      res.writeHead(500);
      res.end(JSON.stringify({ error: e.message }));
    }
    return;
  }

  // ── POST /auth/apple ──────────────────────────────────────────────────────
  if (req.method === 'POST' && url === '/auth/apple') {
    res.setHeader('Content-Type', 'application/json');
    const body = await readBody(req);
    const { identityToken, fullName, email } = body;
    if (!identityToken) { res.writeHead(400); res.end(JSON.stringify({ error: 'Missing identityToken' })); return; }
    let claims;
    try {
      claims = await verifyAppleToken(identityToken);
    } catch (e) {
      console.warn(`[auth] Apple token verification failed: ${e.message}`);
      res.writeHead(401);
      res.end(JSON.stringify({ error: `Apple token invalid: ${e.message}` }));
      return;
    }
    const userId = `apple:${claims.sub}`;
    const resolvedEmail = email || claims.email || '';
    const resolvedName  = (fullName?.givenName && fullName?.familyName)
      ? `${fullName.givenName} ${fullName.familyName}`.trim()
      : (fullName?.givenName || resolvedEmail.split('@')[0] || 'Utilizator');
    const user = upsertUser({ id: userId, email: resolvedEmail, displayName: resolvedName, avatarUrl: null, provider: 'apple' });
    const token = jwtSign({ sub: userId, email: user.email });
    console.log(`[auth] Apple sign-in verified: ${resolvedEmail || userId}`);
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

  // ── POST /auth/register ───────────────────────────────────────────────────
  if (req.method === 'POST' && url === '/auth/register') {
    res.setHeader('Content-Type', 'application/json');
    if (!_pool) {
      res.writeHead(503);
      res.end(JSON.stringify({ error: 'Înregistrarea prin email nu este disponibilă momentan' }));
      return;
    }
    const body = await readBody(req);
    const { email, password, displayName } = body;
    if (!email || !password) { res.writeHead(400); res.end(JSON.stringify({ error: 'Email și parola sunt obligatorii' })); return; }
    if (password.length < 8) { res.writeHead(400); res.end(JSON.stringify({ error: 'Parola trebuie să aibă cel puțin 8 caractere' })); return; }
    if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email)) { res.writeHead(400); res.end(JSON.stringify({ error: 'Adresă de email invalidă' })); return; }

    // Check if email already exists
    const existing = await dbQuery('SELECT id FROM users WHERE email = $1', [email.toLowerCase()]);
    if (existing && existing.rows.length > 0) { res.writeHead(409); res.end(JSON.stringify({ error: 'Există deja un cont cu acest email' })); return; }

    const userId   = `email:${crypto.randomBytes(16).toString('hex')}`;
    const pwHash   = hashPassword(password);
    const name     = displayName || email.split('@')[0];
    const defPrefs = { notificationTopics: ['breaking', 'live_alerts'], preferredCategories: ['politica', 'extern', 'economie'], autoplayVideos: true, highQualityStreaming: false, darkMode: true };

    await dbQuery(
      `INSERT INTO users (id, email, password_hash, display_name, provider, preferences)
       VALUES ($1, $2, $3, $4, 'email', $5)`,
      [userId, email.toLowerCase(), pwHash, name, JSON.stringify(defPrefs)],
    );

    const user = { id: userId, email: email.toLowerCase(), displayName: name, avatarUrl: null, provider: 'email', subscriptionTier: 'free', preferences: defPrefs, savedArticleIds: [], favoriteShowIds: [], watchlistTopics: [], createdAt: new Date().toISOString() };
    _users.set(userId, user);
    const token = jwtSign({ sub: userId, email: user.email });
    console.log(`[auth] Register: ${email}`);
    res.writeHead(201);
    res.end(JSON.stringify({ token, user }));
    return;
  }

  // ── POST /auth/login ──────────────────────────────────────────────────────
  if (req.method === 'POST' && url === '/auth/login') {
    res.setHeader('Content-Type', 'application/json');
    if (!_pool) {
      res.writeHead(503);
      res.end(JSON.stringify({ error: 'Autentificarea prin email nu este disponibilă momentan' }));
      return;
    }
    const body = await readBody(req);
    const { email, password } = body;
    if (!email || !password) { res.writeHead(400); res.end(JSON.stringify({ error: 'Email și parola sunt obligatorii' })); return; }

    const result = await dbQuery('SELECT * FROM users WHERE email = $1 AND provider = \'email\'', [email.toLowerCase()]);
    if (!result || !result.rows.length) { res.writeHead(401); res.end(JSON.stringify({ error: 'Email sau parolă incorectă' })); return; }

    const row = result.rows[0];
    if (!verifyPassword(password, row.password_hash)) { res.writeHead(401); res.end(JSON.stringify({ error: 'Email sau parolă incorectă' })); return; }

    const user = { id: row.id, email: row.email, displayName: row.display_name, avatarUrl: row.avatar_url, provider: 'email', subscriptionTier: row.subscription_tier, preferences: row.preferences ?? {}, savedArticleIds: row.saved_article_ids ?? [], favoriteShowIds: row.favorite_show_ids ?? [], watchlistTopics: row.watchlist_topics ?? [], createdAt: row.created_at };
    _users.set(row.id, user);
    const token = jwtSign({ sub: row.id, email: row.email });
    console.log(`[auth] Login: ${email}`);
    res.writeHead(200);
    res.end(JSON.stringify({ token, user }));
    return;
  }

  // ── POST /auth/forgot-password ────────────────────────────────────────────
  if (req.method === 'POST' && url === '/auth/forgot-password') {
    res.setHeader('Content-Type', 'application/json');
    const body = await readBody(req);
    const { email } = body;
    if (!email) { res.writeHead(400); res.end(JSON.stringify({ error: 'Email obligatoriu' })); return; }

    const result = await dbQuery('SELECT id FROM users WHERE email = $1 AND provider = \'email\'', [email.toLowerCase()]);
    // Always respond OK to prevent email enumeration
    res.writeHead(200);
    res.end(JSON.stringify({ ok: true, message: 'Dacă emailul există, vei primi instrucțiuni de resetare.' }));

    if (result && result.rows.length > 0) {
      const userId = result.rows[0].id;
      const token  = crypto.randomBytes(32).toString('hex');
      const expiry = new Date(Date.now() + 60 * 60 * 1000); // 1 hour
      await dbQuery(
        'INSERT INTO password_reset_tokens (user_id, token, expires_at) VALUES ($1, $2, $3)',
        [userId, token, expiry],
      );
      const resetUrl = `https://b1tv-proxy-production.up.railway.app/reset-password?token=${token}`;
      await sendEmail({
        to: email.toLowerCase(),
        subject: 'Resetare parolă B1 TV',
        html: `<div style="font-family:sans-serif;max-width:480px;margin:auto"><h2 style="color:#E8000D">B1 TV — Resetare parolă</h2><p>Ai solicitat resetarea parolei contului tău.</p><p><a href="${resetUrl}" style="background:#E8000D;color:white;padding:12px 24px;border-radius:6px;text-decoration:none;display:inline-block">Resetează parola</a></p><p style="color:#888;font-size:12px">Link-ul expiră în 1 oră. Dacă nu ai solicitat resetarea, ignoră acest email.</p></div>`,
      });
      console.log(`[auth] Reset token sent to ${email}`);
    }
    return;
  }

  // ── POST /auth/reset-password ─────────────────────────────────────────────
  if (req.method === 'POST' && url === '/auth/reset-password') {
    res.setHeader('Content-Type', 'application/json');
    const body = await readBody(req);
    const { token, password } = body;
    if (!token || !password) { res.writeHead(400); res.end(JSON.stringify({ error: 'Token și parola sunt obligatorii' })); return; }
    if (password.length < 8) { res.writeHead(400); res.end(JSON.stringify({ error: 'Parola trebuie să aibă cel puțin 8 caractere' })); return; }

    const result = await dbQuery(
      'SELECT * FROM password_reset_tokens WHERE token = $1 AND used = FALSE AND expires_at > NOW()',
      [token],
    );
    if (!result || !result.rows.length) { res.writeHead(400); res.end(JSON.stringify({ error: 'Token invalid sau expirat' })); return; }

    const resetRow = result.rows[0];
    const pwHash   = hashPassword(password);
    await dbQuery('UPDATE users SET password_hash = $1, updated_at = NOW() WHERE id = $2', [pwHash, resetRow.user_id]);
    await dbQuery('UPDATE password_reset_tokens SET used = TRUE WHERE id = $1', [resetRow.id]);
    console.log(`[auth] Password reset for user ${resetRow.user_id}`);
    res.writeHead(200);
    res.end(JSON.stringify({ ok: true }));
    return;
  }

  // ── GET /reset-password (web page for email link) ─────────────────────────
  if (req.method === 'GET' && url.startsWith('/reset-password')) {
    const token = new URL(`http://x${req.url}`).searchParams.get('token');
    res.setHeader('Content-Type', 'text/html; charset=utf-8');
    res.writeHead(200);
    res.end(`<!DOCTYPE html><html lang="ro"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Resetare parolă — B1 TV</title><style>*{box-sizing:border-box}body{font-family:sans-serif;background:#0A0A0F;color:#fff;display:flex;align-items:center;justify-content:center;min-height:100vh;margin:0}form{background:#1a1a2e;padding:32px;border-radius:12px;width:100%;max-width:400px}h2{color:#E8000D;margin:0 0 24px}input{width:100%;padding:12px;border-radius:8px;border:1px solid #333;background:#0A0A0F;color:#fff;font-size:16px;margin-bottom:16px}button{width:100%;padding:14px;background:#E8000D;color:#fff;border:none;border-radius:8px;font-size:16px;font-weight:700;cursor:pointer}#msg{margin-top:16px;color:#4CAF50;display:none}#err{margin-top:16px;color:#ff4444;display:none}</style></head><body><form id="f"><h2>Parolă nouă</h2><input type="password" id="p1" placeholder="Parolă nouă" minlength="8" required><input type="password" id="p2" placeholder="Confirmă parola" required><button type="submit">Salvează parola</button><div id="msg">✓ Parola a fost schimbată! Poți reveni în aplicație.</div><div id="err"></div></form><script>document.getElementById('f').onsubmit=async(e)=>{e.preventDefault();const p1=document.getElementById('p1').value,p2=document.getElementById('p2').value;if(p1!==p2){document.getElementById('err').textContent='Parolele nu coincid';document.getElementById('err').style.display='block';return;}const r=await fetch('/auth/reset-password',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({token:'${token}',password:p1})});const d=await r.json();if(d.ok){document.getElementById('msg').style.display='block';document.getElementById('f').querySelector('button').disabled=true;}else{document.getElementById('err').textContent=d.error||'Eroare';document.getElementById('err').style.display='block';}};</script></body></html>`);
    return;
  }

  // ── DELETE /auth/me ───────────────────────────────────────────────────────
  if (req.method === 'DELETE' && url === '/auth/me') {
    res.setHeader('Content-Type', 'application/json');
    const claims = getAuthUser(req);
    if (!claims) { res.writeHead(401); res.end(JSON.stringify({ error: 'Unauthorized' })); return; }
    _users.delete(claims.sub);
    await dbQuery('DELETE FROM users WHERE id = $1', [claims.sub]);
    console.log(`[auth] Account deleted: ${claims.sub}`);
    res.writeHead(200);
    res.end(JSON.stringify({ ok: true }));
    return;
  }

  // ── PATCH /auth/me ────────────────────────────────────────────────────────
  if (req.method === 'PATCH' && url === '/auth/me') {
    res.setHeader('Content-Type', 'application/json');
    const claims = getAuthUser(req);
    if (!claims) { res.writeHead(401); res.end(JSON.stringify({ error: 'Unauthorized' })); return; }
    let user = _users.get(claims.sub) || await loadUserFromDb(claims.sub);
    if (!user) { res.writeHead(404); res.end(JSON.stringify({ error: 'User not found' })); return; }
    const body = await readBody(req);
    const { displayName, currentPassword, newPassword } = body;

    if (newPassword) {
      if (user.provider !== 'email') { res.writeHead(400); res.end(JSON.stringify({ error: 'Schimbarea parolei e disponibilă doar pentru conturile email' })); return; }
      const row = await dbQuery('SELECT password_hash FROM users WHERE id = $1', [claims.sub]);
      if (!row || !row.rows.length || !verifyPassword(currentPassword || '', row.rows[0].password_hash)) {
        res.writeHead(401); res.end(JSON.stringify({ error: 'Parola curentă incorectă' })); return;
      }
      await dbQuery('UPDATE users SET password_hash = $1, updated_at = NOW() WHERE id = $2', [hashPassword(newPassword), claims.sub]);
    }

    if (displayName) {
      user.displayName = displayName;
      _users.set(claims.sub, user);
      await dbQuery('UPDATE users SET display_name = $1, updated_at = NOW() WHERE id = $2', [displayName, claims.sub]);
    }

    res.writeHead(200);
    res.end(JSON.stringify(user));
    return;
  }

  // ── GET /auth/me ───────────────────────────────────────────────────────────
  if (req.method === 'GET' && url === '/auth/me') {
    res.setHeader('Content-Type', 'application/json');
    const claims = getAuthUser(req);
    if (!claims) { res.writeHead(401); res.end(JSON.stringify({ error: 'Unauthorized' })); return; }
    let user = _users.get(claims.sub) || await loadUserFromDb(claims.sub);
    if (!user) {
      const provider = claims.sub.startsWith('apple:') ? 'apple' : claims.sub.startsWith('google:') ? 'google' : 'email';
      user = upsertUser({ id: claims.sub, email: claims.email ?? '', displayName: claims.email?.split('@')[0] ?? 'Utilizator', avatarUrl: null, provider });
      console.log(`[auth] /auth/me — user recreated from JWT: ${claims.sub}`);
    }
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

  // ── GET /seg/<base64url> — proxy individual HLS segments from CDN ──────────
  // URL is base64url-encoded to avoid Railway/Fastly WAF blocking token= params.
  if (req.method === 'GET' && url.startsWith('/seg/')) {
    let segUrl;
    try {
      const encoded = url.slice('/seg/'.length);
      segUrl = Buffer.from(encoded, 'base64url').toString('utf8');
    } catch {
      res.writeHead(400);
      res.end('Bad request: cannot decode segment URL');
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
      console.error('[proxy] /seg/ error:', e.message);
      if (!res.headersSent) {
        res.writeHead(502);
        res.end(JSON.stringify({ error: e.message }));
      }
    }
    return;
  }

  // ── GET /hls-segment?url=... — legacy endpoint (kept for backward compat) ──
  if (req.method === 'GET' && url.startsWith('/hls-segment')) {
    let segUrl;
    try {
      const qs  = new URL(`http://x${req.url}`).searchParams;
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

  // ── 404 catch-all (must be before the /live-url handler) ─────────────────
  if (req.method !== 'GET' || url !== '/live-url') {
    res.setHeader('Content-Type', 'application/json');
    res.writeHead(404);
    res.end(JSON.stringify({ error: 'Not found. Endpoints: GET /hls, GET /hls-segment, GET /live-url, GET /polls, POST /polls/:id/vote' }));
    return;
  }

  // ── GET /live-url — raw CDN URL (kept for diagnostics) ───────────────────

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
