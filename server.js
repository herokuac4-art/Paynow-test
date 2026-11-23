'use strict';

const express = require('express');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const QRCode = require('qrcode');

const PORT = process.env.PORT || 3000;
const DB_FILE = path.join(__dirname, 'data.json');
const KEY_FILE = path.join(__dirname, '.master.key');
const DEMO_MODE = process.env.DEMO_MODE !== 'false';

/* ------------------------------------------------------------------ */
/* Master key + AES-256-GCM secret vault                              */
/* ------------------------------------------------------------------ */

function loadMasterKey() {
  if (process.env.MASTER_KEY && process.env.MASTER_KEY.length === 64) {
    return Buffer.from(process.env.MASTER_KEY, 'hex');
  }
  if (fs.existsSync(KEY_FILE)) {
    return Buffer.from(fs.readFileSync(KEY_FILE, 'utf8').trim(), 'hex');
  }
  const k = crypto.randomBytes(32);
  fs.writeFileSync(KEY_FILE, k.toString('hex'), { mode: 0o600 });
  console.log('[paynow] generated new master key at .master.key — back this up.');
  return k;
}
const MKEY = loadMasterKey();
const SESSION_KEY = crypto.createHmac('sha256', MKEY).update('paynow-session').digest();

function encrypt(plain) {
  const iv = crypto.randomBytes(12);
  const c = crypto.createCipheriv('aes-256-gcm', MKEY, iv);
  const ct = Buffer.concat([c.update(plain, 'utf8'), c.final()]);
  return [iv, c.getAuthTag(), ct].map(b => b.toString('base64')).join('.');
}
function decrypt(payload) {
  const [ivb, tagb, ctb] = String(payload).split('.');
  const d = crypto.createDecipheriv('aes-256-gcm', MKEY, Buffer.from(ivb, 'base64'));
  d.setAuthTag(Buffer.from(tagb, 'base64'));
  return Buffer.concat([d.update(Buffer.from(ctb, 'base64')), d.final()]).toString('utf8');
}

/* ------------------------------------------------------------------ */
/* Tiny JSON store                                                    */
/* ------------------------------------------------------------------ */

const emptyDB = () => ({ users: [], gateways: [], links: [], transactions: [], apiKeys: [], webhooks: [], events: [] });
let db = emptyDB();
if (fs.existsSync(DB_FILE)) {
  try { db = Object.assign(emptyDB(), JSON.parse(fs.readFileSync(DB_FILE, 'utf8'))); }
  catch { console.warn('[paynow] data.json unreadable — starting fresh.'); }
}
let saveTimer = null;
function save() {
  clearTimeout(saveTimer);
  saveTimer = setTimeout(() => {
    try { fs.writeFileSync(DB_FILE, JSON.stringify(db, null, 2)); } catch (e) { console.error('save failed', e); }
  }, 50);
}
const id = () => crypto.randomBytes(12).toString('hex');
const now = () => Date.now();

/* ------------------------------------------------------------------ */
/* Passwords + sessions                                               */
/* ------------------------------------------------------------------ */

function hashPassword(pw, salt = crypto.randomBytes(16).toString('hex')) {
  return salt + ':' + crypto.scryptSync(pw, salt, 64).toString('hex');
}
function verifyPassword(pw, stored) {
  const [salt, hex] = String(stored).split(':');
  const a = Buffer.from(hex, 'hex');
  const b = crypto.scryptSync(pw, salt, 64);
  return a.length === b.length && crypto.timingSafeEqual(a, b);
}
function sign(v) { return crypto.createHmac('sha256', SESSION_KEY).update(v).digest('base64url'); }
function makeSession(uid) {
  const v = Buffer.from(JSON.stringify({ uid, iat: now() })).toString('base64url');
  return v + '.' + sign(v);
}
function readSession(token) {
  if (!token) return null;
  const [v, s] = token.split('.');
  if (!v || !s) return null;
  if (sign(v) !== s) return null;
  try {
    const o = JSON.parse(Buffer.from(v, 'base64url').toString());
    if (now() - o.iat > 1000 * 60 * 60 * 24 * 30) return null;
    return o.uid;
  } catch { return null; }
}
function cookies(req) {
  return Object.fromEntries(
    (req.headers.cookie || '').split(';').map(s => s.trim()).filter(Boolean)
      .map(p => { const i = p.indexOf('='); return [p.slice(0, i), decodeURIComponent(p.slice(i + 1))]; })
  );
}
function setSession(res, uid) {
  const secure = process.env.NODE_ENV === 'production' ? '; Secure' : '';
  res.setHeader('Set-Cookie', `sid=${makeSession(uid)}; HttpOnly; Path=/; SameSite=Lax; Max-Age=${30 * 86400}${secure}`);
}

/* ------------------------------------------------------------------ */
/* Rate limiting                                                      */
/* ------------------------------------------------------------------ */

const hits = new Map();
function rateLimit(key, max, windowMs) {
  const t = now();
  const arr = (hits.get(key) || []).filter(x => t - x < windowMs);
  arr.push(t);
  hits.set(key, arr);
  return arr.length <= max;
}

/* ------------------------------------------------------------------ */
/* App setup                                                          */
/* ------------------------------------------------------------------ */

const app = express();
app.disable('x-powered-by');
app.use(express.json({
  limit: '256kb',
  verify: (req, _res, buf) => { req.rawBody = buf.toString('utf8'); }
}));
app.use(express.static(path.join(__dirname, 'public'), { extensions: ['html'] }));

const PROVIDERS = [
  { id: 'razorpay', name: 'Razorpay', blurb: 'Cards, UPI, netbanking', beta: false },
  { id: 'paytm', name: 'Paytm', blurb: 'UPI + wallet', beta: false },
  { id: 'phonepe', name: 'PhonePe', blurb: 'UPI intent', beta: true },
  { id: 'bharatpe', name: 'BharatPe', blurb: 'UPI for online & offline', beta: true },
  { id: 'fampay', name: 'FamPay', blurb: 'Partner approval required', beta: true }
];
const PROVIDER_IDS = new Set(PROVIDERS.map(p => p.id));

const publicUser = u => ({ id: u.id, email: u.email, businessName: u.businessName, pan: u.pan ? u.pan.slice(0, 2) + '***' + u.pan.slice(-2) : null });

function auth(req, res, next) {
  const uid = readSession(cookies(req).sid);
  if (!uid || !db.users.some(u => u.id === uid)) return res.status(401).json({ error: 'Please log in.' });
  req.userId = uid;
  next();
}
function apiKeyAuth(req, res, next) {
  const h = req.headers.authorization || '';
  const token = h.startsWith('Bearer ') ? h.slice(7).trim() : '';
  if (!token) return res.status(401).json({ error: 'Missing API key.' });
  const hash = crypto.createHash('sha256').update(token).digest('hex');
  const key = db.apiKeys.find(k => k.hash === hash);
  if (!key) return res.status(401).json({ error: 'Invalid API key.' });
  req.userId = key.userId;
  req.apiKey = key;
  next();
}

/* ------------------------------------------------------------------ */
/* Auth routes                                                        */
/* ------------------------------------------------------------------ */

app.post('/api/auth/signup', (req, res) => {
  if (!rateLimit('signup:' + req.ip, 10, 60_000)) return res.status(429).json({ error: 'Too many attempts. Try again in a minute.' });
  const { email, password, businessName, pan } = req.body || {};
  if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email || '')) return res.status(400).json({ error: 'Enter a valid email address.' });
  if ((password || '').length < 8) return res.status(400).json({ error: 'Password must be at least 8 characters.' });
  if (!businessName || businessName.trim().length < 2) return res.status(400).json({ error: 'Business name is required.' });
  if (!/^[A-Z]{5}[0-9]{4}[A-Z]$/.test((pan || '').toUpperCase())) return res.status(400).json({ error: 'Enter a valid PAN (e.g. ABCDE1234F).' });
  if (db.users.some(u => u.email === email.toLowerCase())) return res.status(409).json({ error: 'An account with this email already exists.' });

  const user = {
    id: id(), email: email.toLowerCase(), passwordHash: hashPassword(password),
    businessName: businessName.trim(), pan: pan.toUpperCase(), createdAt: now()
  };
  db.users.push(user); save();
  setSession(res, user.id);
  res.json({ user: publicUser(user) });
});

app.post('/api/auth/login', (req, res) => {
  if (!rateLimit('login:' + req.ip, 20, 60_000)) return res.status(429).json({ error: 'Too many attempts. Try again in a minute.' });
  const { email, password } = req.body || {};
  const user = db.users.find(u => u.email === String(email || '').toLowerCase());
  if (!user || !verifyPassword(password || '', user.passwordHash)) return res.status(401).json({ error: 'Incorrect email or password.' });
  setSession(res, user.id);
  res.json({ user: publicUser(user) });
});

app.post('/api/auth/logout', (req, res) => {
  res.setHeader('Set-Cookie', 'sid=; HttpOnly; Path=/; SameSite=Lax; Max-Age=0');
  res.json({ ok: true });
});

app.get('/api/me', auth, (req, res) => {
  const user = db.users.find(u => u.id === req.userId);
  res.json({ user: publicUser(user) });
});

/* ------------------------------------------------------------------ */
/* Gateways                                                           */
/* ------------------------------------------------------------------ */

app.get('/api/gateways/providers', auth, (_req, res) => res.json({ providers: PROVIDERS }));

app.get('/api/gateways', auth, (req, res) => {
  const list = db.gateways.filter(g => g.userId === req.userId).map(g => ({
    id: g.id, provider: g.provider, label: g.label, keyId: g.keyId,
    upiVpa: g.upiVpa || null, status: g.status, createdAt: g.createdAt, testedAt: g.testedAt || null
  }));
  res.json({ gateways: list });
});

app.post('/api/gateways', auth, (req, res) => {
  const { provider, label, keyId, secret, upiVpa } = req.body || {};
  if (!PROVIDER_IDS.has(provider)) return res.status(400).json({ error: 'Unsupported gateway.' });
  if (!label || !keyId || !secret) return res.status(400).json({ error: 'Label, Key ID and Key Secret are required.' });
  if (String(secret).length < 8) return res.status(400).json({ error: 'Key secret looks too short.' });
  const gw = {
    id: id(), userId: req.userId, provider, label: label.trim(), keyId: keyId.trim(),
    secretEnc: encrypt(String(secret)), upiVpa: (upiVpa || '').trim() || null,
    status: 'connected', createdAt: now(), testedAt: null
  };
  db.gateways.push(gw); save();
  res.json({ gateway: { id: gw.id, provider, label: gw.label, keyId: gw.keyId, upiVpa: gw.upiVpa, status: gw.status } });
});

app.post('/api/gateways/:id/test', auth, (req, res) => {
  const gw = db.gateways.find(g => g.id === req.params.id && g.userId === req.userId);
  if (!gw) return res.status(404).json({ error: 'Gateway not found.' });
  // Real implementation: call provider's /orders or /balance endpoint with decrypted secret.
  decrypt(gw.secretEnc); // proves the vault round-trips
  gw.testedAt = now();
  gw.status = 'connected';
  save();
  res.json({ ok: true, gateway: { id: gw.id, status: gw.status, testedAt: gw.testedAt } });
});

app.delete('/api/gateways/:id', auth, (req, res) => {
  const i = db.gateways.findIndex(g => g.id === req.params.id && g.userId === req.userId);
  if (i === -1) return res.status(404).json({ error: 'Gateway not found.' });
  db.gateways.splice(i, 1); save();
  res.json({ ok: true });
});

/* ------------------------------------------------------------------ */
/* Payment links                                                      */
/* ------------------------------------------------------------------ */

function linkUrl(req, slug) {
  return `${req.protocol}://${req.get('host')}/pay/${slug}`;
}
function decorateLink(req, l) {
  return {
    id: l.id, slug: l.slug, url: linkUrl(req, l.slug), amount: l.amount, currency: l.currency,
    productName: l.productName, description: l.description, status: l.status,
    gatewayId: l.gatewayId, createdAt: l.createdAt, expiresAt: l.expiresAt, paidAt: l.paidAt || null
  };
}
function expireIfNeeded(link) {
  if (link.status === 'active' && link.expiresAt < now()) { link.status = 'expired'; save(); }
}

app.get('/api/links', auth, (req, res) => {
  const list = db.links.filter(l => l.userId === req.userId).map(l => { expireIfNeeded(l); return decorateLink(req, l); });
  list.sort((a, b) => b.createdAt - a.createdAt);
  res.json({ links: list });
});

app.post('/api/links', auth, (req, res) => {
  const { amount, productName, description, gatewayId, expiresIn } = req.body || {};
  const paise = Math.round(Number(amount) * 100);
  if (!Number.isFinite(paise) || paise < 100 || paise > 100_000_000) return res.status(400).json({ error: 'Amount must be between ₹1 and ₹1,000,000.' });
  if (!productName || String(productName).trim().length < 2) return res.status(400).json({ error: 'Product name is required.' });
  if (gatewayId && !db.gateways.some(g => g.id === gatewayId && g.userId === req.userId)) return res.status(400).json({ error: 'Unknown gateway.' });
  const minutes = Math.min(Math.max(Number(expiresIn) || 1440, 5), 60 * 24 * 30);

  let slug;
  do { slug = crypto.randomBytes(5).toString('hex'); } while (db.links.some(l => l.slug === slug));

  const link = {
    id: id(), slug, userId: req.userId, amount: paise, currency: 'INR',
    productName: String(productName).trim(), description: String(description || '').trim(),
    gatewayId: gatewayId || null, status: 'active',
    createdAt: now(), expiresAt: now() + minutes * 60_000, paidAt: null
  };
  db.links.push(link); save();
  res.json({ link: decorateLink(req, link) });
});

app.patch('/api/links/:id', auth, (req, res) => {
  const link = db.links.find(l => l.id === req.params.id && l.userId === req.userId);
  if (!link) return res.status(404).json({ error: 'Link not found.' });
  const { status } = req.body || {};
  if (!['active', 'disabled'].includes(status)) return res.status(400).json({ error: 'Status must be active or disabled.' });
  if (link.status === 'paid') return res.status(409).json({ error: 'Paid links cannot be changed.' });
  link.status = status; save();
  res.json({ link: decorateLink(req, link) });
});

/* ------------------------------------------------------------------ */
/* Public checkout                                                    */
/* ------------------------------------------------------------------ */

const streams = new Map();
function sseBroadcast(linkId, payload) {
  const set = streams.get(linkId);
  if (!set) return;
  const msg = `data: ${JSON.stringify(payload)}\n\n`;
  for (const res of set) { try { res.write(msg); } catch { /* ignore */ } }
}

app.get('/api/public/links/:slug', (req, res) => {
  const link = db.links.find(l => l.slug === req.params.slug);
  if (!link) return res.status(404).json({ error: 'Link not found.' });
  expireIfNeeded(link);
  const merchant = db.users.find(u => u.id === link.userId);
  res.json({
    slug: link.slug, amount: link.amount, currency: link.currency,
    productName: link.productName, description: link.description,
    status: link.status, expiresAt: link.expiresAt, paidAt: link.paidAt,
    businessName: merchant ? merchant.businessName : 'Merchant'
  });
});

app.post('/api/public/links/:slug/intent', async (req, res) => {
  const link = db.links.find(l => l.slug === req.params.slug);
  if (!link) return res.status(404).json({ error: 'Link not found.' });
  expireIfNeeded(link);
  if (link.status === 'paid') return res.status(409).json({ error: 'This link has already been paid.' });
  if (link.status !== 'active') return res.status(410).json({ error: 'This payment link is no longer active.' });

  const gw = link.gatewayId ? db.gateways.find(g => g.id === link.gatewayId) : null;
  const merchant = db.users.find(u => u.id === link.userId);
  const provider = gw ? gw.provider : 'demo';
  const vpa = (gw && gw.upiVpa) || 'paynow.demo@upi';
  const demo = !(gw && gw.upiVpa);

  const orderId = 'ord_' + crypto.randomBytes(8).toString('hex');
  const params = new URLSearchParams({
    pa: vpa, pn: merchant.businessName, am: (link.amount / 100).toFixed(2),
    cu: 'INR', tn: link.productName, tr: orderId
  });
  const qs = params.toString();
  const upi = 'upi://pay?' + qs;

  let qr = '';
  try { qr = await QRCode.toDataURL(upi, { margin: 1, width: 440, color: { dark: '#1d1d1f', light: '#ffffff' } }); }
  catch { /* QR is best-effort */ }

  const txn = {
    id: id(), userId: link.userId, linkId: link.id, gatewayId: gw ? gw.id : null,
    provider, orderId, amount: link.amount, product: link.productName,
    status: 'pending', method: null, createdAt: now(), paidAt: null
  };
  db.transactions.push(txn); save();

  res.json({ orderId, qr, vpa, upi, qs, demo, provider, expiresAt: link.expiresAt });
});

app.get('/api/public/links/:slug/events', (req, res) => {
  const link = db.links.find(l => l.slug === req.params.slug);
  if (!link) return res.status(404).end();

  res.writeHead(200, {
    'Content-Type': 'text/event-stream',
    'Cache-Control': 'no-cache, no-transform',
    Connection: 'keep-alive',
    'X-Accel-Buffering': 'no'
  });
  res.write('retry: 3000\n\n');

  let set = streams.get(link.id);
  if (!set) { set = new Set(); streams.set(link.id, set); }
  set.add(res);

  const { orderId } = req.query;
  if (orderId) {
    const txn = db.transactions.find(t => t.orderId === orderId);
    if (txn) res.write(`data: ${JSON.stringify({ type: 'status', orderId, status: txn.status })}\n\n`);
  }

  const ping = setInterval(() => { try { res.write(': ping\n\n'); } catch { /* ignore */ } }, 20_000);
  req.on('close', () => { clearInterval(ping); set.delete(res); if (!set.size) streams.delete(link.id); });
});

// DEMO ONLY: stands in for the gateway webhook. Disable in production.
app.post('/api/public/links/:slug/simulate', (req, res) => {
  if (!DEMO_MODE) return res.status(403).json({ error: 'Simulation disabled.' });
  const link = db.links.find(l => l.slug === req.params.slug);
  if (!link) return res.status(404).json({ error: 'Link not found.' });
  const { orderId } = req.body || {};
  const txn = db.transactions.find(t => t.orderId === orderId && t.linkId === link.id);
  if (!txn) return res.status(404).json({ error: 'Order not found.' });
  if (txn.status === 'success') return res.json({ ok: true, idempotent: true });

  txn.status = 'success'; txn.method = 'upi'; txn.paidAt = now();
  link.status = 'paid'; link.paidAt = txn.paidAt;
  db.events.push({ id: id(), type: 'payment.success', orderId, linkId: link.id, at: now() });
  if (db.events.length > 500) db.events.splice(0, db.events.length - 500);
  save();
  sseBroadcast(link.id, { type: 'status', orderId, status: 'success' });
  res.json({ ok: true });
});

/* ------------------------------------------------------------------ */
/* Gateway webhooks (real integration point)                          */
/* ------------------------------------------------------------------ */

app.post('/webhooks/:provider', (req, res) => {
  const provider = req.params.provider;
  const sig = String(req.headers['x-signature'] || req.headers['x-razorpay-signature'] || '');
  const raw = req.rawBody || '';
  const candidates = db.gateways.filter(g => g.provider === provider);

  let matched = null;
  for (const g of candidates) {
    try {
      const secret = decrypt(g.secretEnc);
      const expected = crypto.createHmac('sha256', secret).update(raw).digest('hex');
      if (expected.length === sig.length && crypto.timingSafeEqual(Buffer.from(expected), Buffer.from(sig))) { matched = g; break; }
    } catch { /* skip */ }
  }
  if (!matched) return res.status(401).json({ error: 'Invalid webhook signature.' });

  const { order_id, status, method } = req.body || {};
  const txn = db.transactions.find(t => t.orderId === order_id && t.gatewayId === matched.id);
  if (!txn) return res.status(404).json({ error: 'Unknown order.' });
  if (txn.status === 'success') return res.json({ ok: true, idempotent: true });

  txn.status = status === 'success' ? 'success' : (status || 'failed');
  txn.method = method || 'upi';
  txn.paidAt = txn.status === 'success' ? now() : null;
  if (txn.linkId) {
    const link = db.links.find(l => l.id === txn.linkId);
    if (link && txn.status === 'success') { link.status = 'paid'; link.paidAt = txn.paidAt; }
    s