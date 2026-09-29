#!/usr/bin/env node
// Zero-dependency static server for local preview:  node scripts/serve.mjs [port]
// Serves only the site entries, under /trureturing-visualize/ like GitHub Pages does.
import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { ROOT, SITE_ENTRIES } from './site.mjs';

export const BASE = '/trureturing-visualize/';
const TYPES = {
  '.html': 'text/html; charset=utf-8', '.css': 'text/css; charset=utf-8', '.js': 'text/javascript; charset=utf-8',
  '.mjs': 'text/javascript; charset=utf-8', '.json': 'application/json; charset=utf-8', '.svg': 'image/svg+xml',
  '.png': 'image/png', '.jpg': 'image/jpeg', '.jpeg': 'image/jpeg', '.webp': 'image/webp', '.woff2': 'font/woff2'
};

export function createServer() {
  return http.createServer((req, res) => {
    const url = new URL(req.url, 'http://localhost');
    if (url.pathname === '/') { res.writeHead(302, { location: BASE }); res.end(); return; }
    const send404 = () => { res.writeHead(404, { 'content-type': TYPES['.html'] }); fs.createReadStream(path.join(ROOT, '404.html')).pipe(res); };
    if (!url.pathname.startsWith(BASE)) return send404();
    let rel = decodeURIComponent(url.pathname.slice(BASE.length));
    if (rel === '' || rel.endsWith('/')) rel += 'index.html';
    const top = rel.split('/')[0];
    const file = path.resolve(ROOT, rel);
    if (!SITE_ENTRIES.includes(top) || !file.startsWith(ROOT + path.sep)) return send404();
    fs.stat(file, (err, st) => {
      if (err) return send404();
      if (st.isDirectory()) { res.writeHead(301, { location: url.pathname + '/' }); res.end(); return; }
      res.writeHead(200, { 'content-type': TYPES[path.extname(file).toLowerCase()] || 'application/octet-stream', 'cache-control': 'no-cache' });
      fs.createReadStream(file).pipe(res);
    });
  });
}

if (import.meta.url === `file://${process.argv[1]}`) {
  const port = Number(process.argv[2] || process.env.PORT || 8765);
  createServer().listen(port, '127.0.0.1', () => console.log(`serving http://127.0.0.1:${port}${BASE}`));
}
