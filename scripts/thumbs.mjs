#!/usr/bin/env node
// Capture index thumbnails with Playwright (Chromium, software WebGL):
//   node scripts/thumbs.mjs [id ...]      (default: every registered entry)
// Each page may mark the region to capture with data-thumb (otherwise its .stage is used) and may define
// window.TRV_THUMB() to switch into a representative state first. Toasts, HUD text and 3D labels are hidden,
// so one cover serves both languages.
// Playwright is a dev-only dependency: `npm i -D playwright` or a global install is enough.
import path from 'node:path';
import { createRequire } from 'node:module';
import { ROOT, readRegistry } from './site.mjs';
import { createServer, BASE } from './serve.mjs';

async function loadPlaywright() {
  try { return await import('playwright'); } catch { /* fall through to a global install */ }
  const { execSync } = await import('node:child_process');
  const globalRoot = execSync('npm root -g').toString().trim();
  return createRequire(path.join(globalRoot, 'noop.js'))('playwright');
}

const ids = process.argv.slice(2);
const entries = readRegistry().visualizations.filter((v) => !ids.length || ids.includes(v.id));
if (!entries.length) { console.error('no matching registry entries'); process.exit(2); }
const { chromium } = await loadPlaywright();
const server = createServer();
await new Promise((r) => server.listen(0, '127.0.0.1', r));
const origin = `http://127.0.0.1:${server.address().port}`;
const browser = await chromium.launch({ args: ['--use-angle=swiftshader', '--enable-unsafe-swiftshader', '--ignore-gpu-blocklist'] });
try {
  for (const v of entries) {
    const page = await browser.newPage({ viewport: { width: 1600, height: 1000 }, deviceScaleFactor: 1 });
    const errors = [];
    page.on('pageerror', (e) => errors.push(e.message));
    await page.goto(`${origin}${BASE}${v.path}`, { waitUntil: 'load' });
    await page.waitForTimeout(2500);
    // Optional page hook: window.TRV_THUMB() puts the page into its cover state before capture.
    const hooked = await page.evaluate(() => { if (typeof window.TRV_THUMB === 'function') { window.TRV_THUMB(); return true; } return false; });
    await page.waitForTimeout(hooked ? 3000 : 1000);
    // the cover is shared by both languages, so it carries no interface text
    await page.addStyleTag({ content: '.toast, .hud-tl, .hud-tr, #tags { opacity: 0 !important; }' });
    const target = (await page.$('[data-thumb]')) || (await page.$('.stage'));
    if (!target) throw new Error(`${v.id}: no [data-thumb] or .stage element to capture`);
    await target.screenshot({ path: path.join(ROOT, v.thumbnail), type: 'jpeg', quality: 82 });
    console.log(`${v.id} → ${v.thumbnail}${errors.length ? `  (page errors: ${errors.join('; ')})` : ''}`);
    await page.close();
  }
} finally {
  await browser.close();
  server.close();
}
