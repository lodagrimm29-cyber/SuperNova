const express = require('express');
const path = require('node:path');
const dns = require('node:dns').promises;
const http = require('node:http');
const https = require('node:https');
const net = require('node:net');

const app = express();
const PORT = Number(process.env.PORT) || 3000;
const HOST = process.env.HOST || '127.0.0.1';
const PROXY_PORT = Number(process.env.PROXY_PORT) || PORT + 1;
const proxyApp = express();
const MAX_REDIRECTS = 5;
const MAX_BYTES = 10 * 1024 * 1024;
const REQUEST_TIMEOUT_MS = 12000;

function ipv4Number(ip) {
  return ip.split('.').reduce((n, part) => (n * 256 + Number(part)) >>> 0, 0) >>> 0;
}
function inV4(ip, base, bits) {
  const mask = bits === 0 ? 0 : (0xffffffff << (32 - bits)) >>> 0;
  return (ipv4Number(ip) & mask) === (ipv4Number(base) & mask);
}
function ipv6Number(ip) {
  let source = ip.toLowerCase().split('%')[0];
  if (source.includes('.')) {
    const lastColon = source.lastIndexOf(':');
    const v4 = source.slice(lastColon + 1);
    if (net.isIPv4(v4)) {
      const n = ipv4Number(v4);
      source = source.slice(0, lastColon + 1) + ((n >>> 16).toString(16)) + ':' + (n & 65535).toString(16);
    }
  }
  const halves = source.split('::');
  const left = halves[0] ? halves[0].split(':') : [];
  const right = halves[1] ? halves[1].split(':') : [];
  const fill = Array(Math.max(0, 8 - left.length - right.length)).fill('0');
  const groups = [...left, ...fill, ...right];
  if (groups.length !== 8) return null;
  return groups.reduce((n, part) => (n << 16n) | BigInt(parseInt(part || '0', 16)), 0n);
}
function inV6(ip, base, bits) {
  const n = ipv6Number(ip), b = ipv6Number(base);
  if (n === null || b === null) return false;
  const shift = 128n - BigInt(bits);
  return (n >> shift) === (b >> shift);
}
function isPublicIp(ip) {
  const family = net.isIP(ip);
  if (family === 4) {
    const denied = [
      ['0.0.0.0', 8], ['10.0.0.0', 8], ['100.64.0.0', 10], ['127.0.0.0', 8],
      ['169.254.0.0', 16], ['172.16.0.0', 12], ['192.0.0.0', 24], ['192.0.2.0', 24],
      ['192.88.99.0', 24], ['192.168.0.0', 16], ['198.18.0.0', 15], ['198.51.100.0', 24],
      ['203.0.113.0', 24], ['224.0.0.0', 4], ['240.0.0.0', 4]
    ];
    return !denied.some(([base, bits]) => inV4(ip, base, bits));
  }
  if (family === 6) {
    if (inV6(ip, '::ffff:0:0', 96)) {
      const n = ipv6Number(ip) & 0xffffffffn;
      const v4 = [Number((n >> 24n) & 255n), Number((n >> 16n) & 255n), Number((n >> 8n) & 255n), Number(n & 255n)].join('.');
      return isPublicIp(v4);
    }
    // Only globally assigned unicast space, excluding special-use and documentation blocks.
    if (!inV6(ip, '2000::', 3)) return false;
    const denied = [['2001:db8::', 32], ['2001::', 23], ['2002::', 16], ['3fff::', 20]];
    return !denied.some(([base, bits]) => inV6(ip, base, bits));
  }
  return false;
}
function parseTarget(raw, base) {
  if (typeof raw !== 'string' || !raw.trim() || raw.length > 4096) throw new Error('Enter a valid website address.');
  let url;
  try { url = new URL(raw, base); } catch { throw new Error('Enter a valid website address.'); }
  if (!['http:', 'https:'].includes(url.protocol)) throw new Error('Only HTTP and HTTPS websites are supported.');
  if (url.username || url.password) throw new Error('Website addresses cannot contain credentials.');
  if (url.port && !((url.protocol === 'http:' && url.port === '80') || (url.protocol === 'https:' && url.port === '443'))) {
    throw new Error('Only standard web ports (80 and 443) are supported.');
  }
  url.hash = '';
  return url;
}
async function resolvePublic(url) {
  const host = url.hostname.toLowerCase().replace(/^\[|\]$/g, '').replace(/\.$/, '');
  if (!host || host === 'localhost' || host.endsWith('.localhost') || host.endsWith('.local') || host.endsWith('.internal')) throw new Error('Private and local network addresses are blocked.');
  let answers;
  if (net.isIP(host)) answers = [{ address: host, family: net.isIP(host) }];
  else {
    try { answers = await dns.lookup(host, { all: true, verbatim: true }); }
    catch { throw new Error('That website could not be found.'); }
  }
  if (!answers.length || answers.some(({ address }) => !isPublicIp(address))) throw new Error('Private and local network addresses are blocked.');
  return answers[0];
}
function makeProxyUrl(url) { return '/proxy?url=' + encodeURIComponent(url.href); }
function rewriteUrl(value, base) {
  const trimmed = value.trim();
  if (!trimmed || trimmed.startsWith('#') || /^(?:data|blob|javascript|mailto|tel|about):/i.test(trimmed)) return value;
  try { return makeProxyUrl(parseTarget(trimmed, base)); }
  catch { return /^(?:https?:)?\/\//i.test(trimmed) || trimmed.startsWith('/') ? '#blocked-resource' : value; }
}
function rewriteHtml(html, base) {
  // Keep the document in the local viewer and route its usual navigations/resources back through /proxy.
  html = html.replace(/\s(href|src|action|poster|formaction)\s*=\s*(["'])(.*?)\2/gi, (all, attr, quote, value) => ` ${attr}=${quote}${rewriteUrl(value, base)}${quote}`);
  html = html.replace(/\s(srcset)\s*=\s*(["'])(.*?)\2/gi, (all, attr, quote, value) => {
    const rewritten = value.split(',').map(item => {
      const parts = item.trim().split(/\s+/, 2);
      return [rewriteUrl(parts[0], base), parts[1]].filter(Boolean).join(' ');
    }).join(', ');
    return ` ${attr}=${quote}${rewritten}${quote}`;
  });
  html = html.replace(/\burl\(\s*(["']?)(.*?)\1\s*\)/gi, (all, quote, value) => `url(${quote}${rewriteUrl(value, base)}${quote})`);
  const baseTag = `<base href="${makeProxyUrl(base)}">`;
  if (/<head\b[^>]*>/i.test(html)) html = html.replace(/<head\b[^>]*>/i, match => match + baseTag);
  else html = baseTag + html;
  return html;
}
function fetchOnce(url, ip) {
  return new Promise((resolve, reject) => {
    const transport = url.protocol === 'https:' ? https : http;
    const options = {
      protocol: url.protocol, hostname: url.hostname, port: url.port || undefined,
      path: url.pathname + url.search, method: 'GET',
      autoSelectFamily: false,
      headers: { 'User-Agent': 'SuperNovaBrowser/1.0 (local web proxy)', 'Accept': 'text/html,application/xhtml+xml,application/xml,image/avif,image/webp,*/*;q=0.8', 'Accept-Encoding': 'identity' },
      timeout: REQUEST_TIMEOUT_MS,
      lookup: (_hostname, options, callback) => {
        const done = typeof options === 'function' ? options : callback;
        done(null, ip.address, ip.family);
      },
      ...(net.isIP(url.hostname.replace(/^\[|\]$/g, '')) ? {} : { servername: url.hostname })
    };
    const req = transport.request(options, res => {
      let size = 0;
      const chunks = [];
      res.on('data', chunk => {
        size += chunk.length;
        if (size > MAX_BYTES) { req.destroy(new Error('The page is larger than the 10 MB limit.')); return; }
        chunks.push(chunk);
      });
      res.on('end', () => resolve({ status: res.statusCode || 502, headers: res.headers, body: Buffer.concat(chunks) }));
    });
    req.on('timeout', () => req.destroy(new Error('The website took too long to respond.')));
    req.on('error', reject);
    req.end();
  });
}
app.get('/config', (_req, res) => res.json({ proxyOrigin: `http://${HOST}:${PROXY_PORT}` }));
app.use(express.static(path.join(__dirname, 'public')));
proxyApp.get('/proxy', async (req, res) => {
  try {
    let target = parseTarget(req.query.url);
    let response;
    for (let redirects = 0; redirects <= MAX_REDIRECTS; redirects++) {
      const ip = await resolvePublic(target);
      response = await fetchOnce(target, ip);
      if ([301, 302, 303, 307, 308].includes(response.status) && response.headers.location) {
        if (redirects === MAX_REDIRECTS) throw new Error('This website redirected too many times.');
        target = parseTarget(response.headers.location, target);
        continue;
      }
      break;
    }
    const type = String(response.headers['content-type'] || 'application/octet-stream');
    res.status(response.status);
    res.set('X-Content-Type-Options', 'nosniff');
    res.set('Referrer-Policy', 'no-referrer');
    res.set('Cache-Control', 'no-store');
    if (/^(?:text\/html|application\/xhtml\+xml)/i.test(type)) {
      res.type('html').send(rewriteHtml(response.body.toString('utf8'), target));
    } else if (/^text\/css/i.test(type)) {
      res.type('text/css').send(response.body.toString('utf8').replace(/url\(\s*(["']?)(.*?)\1\s*\)/gi, (all, quote, value) => `url(${quote}${rewriteUrl(value, target)}${quote})`));
    } else {
      res.set('Content-Type', type);
      if (response.headers['content-length']) res.set('Content-Length', String(response.body.length));
      res.send(response.body);
    }
  } catch (error) {
    const status = /valid website|Only HTTP|credentials|ports|blocked|redirected too many/i.test(error.message) ? 400 : 502;
    res.status(status).type('text').send(`SuperNova Browser could not load this page: ${error.message}`);
  }
});
app.listen(PORT, HOST, () => console.log(`SuperNova Browser running at http://${HOST}:${PORT}`));
proxyApp.listen(PROXY_PORT, HOST, () => console.log(`SuperNova proxy running at http://${HOST}:${PROXY_PORT}`));
