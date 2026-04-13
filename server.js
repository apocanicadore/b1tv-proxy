/**
 * B1 TV HLS proxy server — v2 (HLS Relay mode)
 *
 * Problem: DeJaCast CDN IP-locks signed HLS URLs.
 * The URL captured by Chromium (Railway IP) returns 403 when fetched
 * from a mobile device (different IP).
 *
 * Solution: Full HLS relay.
 * - GET /hls           → fetches M3U8 from CDN (Railway IP + session cookies),
 *                         rewrites segment URLs to go through this proxy, returns
 *                         to app. AVPlayer loads playlist from Railway.
 * - GET /hls-segment   → proxies individual .ts segments from CDN to app.
 *                         All CDN traffic goes through Railway's trusted IP.
 *
 * Other endpoints:
 * - GET /live-url      → raw CDN URL + metadata (kept for diagnostics/debug)
 * - GET /polls         → poll data
 * - POST /polls/:id/vote
 */

'use strict';

const http      = require('http');
const https     = require('https');
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
          if (el) { (el as HTMLElement).click(); return sel; }
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

// ── HTTP server ───────────────────────────────────────────────────────────────

const server = http.createServer(async (req, res) => {
  // ── CORS ──────────────────────────────────────────────────────────────────
  res.setHeader('Access-Control-Allow-Origin',  '*');
  res.setHeader('Access-Control-Allow-Methods', 'GET, OPTIONS');
  res.setHeader('Access-Control-Allow-Headers', 'Content-Type');

  if (req.method === 'OPTIONS') {
    res.writeHead(204);
    res.end();
    return;
  }

  const url = req.url || '/';

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

  // ── GET /hls — HLS relay: fetch M3U8 from CDN and rewrite segment URLs ────
  if (req.method === 'GET' && url === '/hls') {
    console.log('\n[proxy] ← GET /hls');
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
      console.log(`[proxy] /hls → 200 (${m3u8.split('\n').length} lines, proxy: ${proxyBase})`);

      res.setHeader('Content-Type', 'application/vnd.apple.mpegurl');
      res.setHeader('Cache-Control', 'no-cache, no-store, must-revalidate');
      res.writeHead(200);
      res.end(rewritten);
    } catch (e) {
      console.error('[proxy] /hls error:', e.message);
      res.writeHead(500);
      res.end(JSON.stringify({ error: e.message }));
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
  console.log(`║  B1TV HLS Proxy v2  ·  http://localhost:${PORT}             ║`);
  console.log('║  GET /hls           →  HLS relay (M3U8 rewritten)        ║');
  console.log('║  GET /hls-segment   →  segment proxy from CDN            ║');
  console.log('║  GET /live-url      →  raw CDN URL (diagnostics)         ║');
  console.log('╚══════════════════════════════════════════════════════════╝');
  console.log('');
});

process.on('SIGINT',  async () => { if (_browser) await _browser.close(); process.exit(0); });
process.on('SIGTERM', async () => { if (_browser) await _browser.close(); process.exit(0); });
