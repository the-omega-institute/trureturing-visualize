#!/usr/bin/env node
// Checks the registry against the files on disk and every page against the shared-shell contract.
// Exit code 1 lists every problem found.  Run:  node scripts/validate.mjs
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { ROOT, ID_RE, STATUSES, readRegistry } from './site.mjs';

const problems = [];
const fail = (msg) => problems.push(msg);
const exists = (rel) => fs.existsSync(path.join(ROOT, rel));
const read = (rel) => fs.readFileSync(path.join(ROOT, rel), 'utf8');

// 1. registry shape
let reg;
try { reg = readRegistry(); } catch (e) { fail(`visualizations.json: ${e.message}`); }
const entries = reg && Array.isArray(reg.visualizations) ? reg.visualizations : [];
if (reg && reg.version !== 1) fail('visualizations.json: version must be 1');
if (reg && !Array.isArray(reg.visualizations)) fail('visualizations.json: visualizations must be an array');
const seen = new Set();
const isHttps = (u) => typeof u === 'string' && /^https:\/\/\S+$/.test(u);
for (const [i, v] of entries.entries()) {
  const at = `visualizations[${i}]${v && v.id ? ` (${v.id})` : ''}`;
  for (const key of ['id', 'code', 'title', 'path', 'thumbnail', 'status', 'added']) {
    if (typeof v[key] !== 'string' || !v[key].trim()) fail(`${at}: missing string field "${key}"`);
  }
  // bilingual contract: a live entry carries both languages
  if (v.status === 'live') {
    for (const key of ['title_en', 'summary', 'summary_en']) {
      if (typeof v[key] !== 'string' || !v[key].trim()) fail(`${at}: a live entry needs "${key}"`);
    }
    if (Array.isArray(v.tags) && v.tags.length && (!Array.isArray(v.tags_en) || v.tags_en.length !== v.tags.length)) fail(`${at}: tags_en must translate every tag`);
    for (const ref of v.theory || []) if (ref && !ref.label_en) fail(`${at}: theory reference "${ref.label}" needs label_en`);
  }
  if (!ID_RE.test(v.id || '')) fail(`${at}: id must be kebab-case`);
  if (seen.has(v.id)) fail(`${at}: duplicate id`);
  seen.add(v.id);
  if (v.path !== `viz/${v.id}/`) fail(`${at}: path must be "viz/${v.id}/"`);
  if (!STATUSES.includes(v.status)) fail(`${at}: status must be one of ${STATUSES.join(', ')}`);
  if (!/^\d{4}-\d{2}-\d{2}$/.test(v.added || '')) fail(`${at}: added must be YYYY-MM-DD`);
  if (v.thumbnail && !v.thumbnail.startsWith(`viz/${v.id}/`)) fail(`${at}: thumbnail must live in viz/${v.id}/`);
  if (v.status === 'live' && v.thumbnail && !exists(v.thumbnail)) fail(`${at}: thumbnail ${v.thumbnail} does not exist (run node scripts/thumbs.mjs ${v.id})`);
  if (!Array.isArray(v.theory) || (v.status === 'live' && v.theory.length === 0)) fail(`${at}: a live entry names at least one theory reference`);
  for (const list of ['theory', 'lean']) {
    if (v[list] === undefined) continue;
    if (!Array.isArray(v[list])) { fail(`${at}: ${list} must be an array`); continue; }
    for (const ref of v[list]) if (!ref || !ref.label || !isHttps(ref.href)) fail(`${at}: every ${list} reference needs a label and an https href`);
  }
  if (v.tags !== undefined && (!Array.isArray(v.tags) || v.tags.some((t) => typeof t !== 'string'))) fail(`${at}: tags must be strings`);

  // 2. page contract
  const page = `viz/${v.id}/index.html`;
  if (!exists(page)) { fail(`${at}: ${page} does not exist`); continue; }
  const html = read(page);
  const need = [
    [`data-viz-id="${v.id}"`, 'body carries data-viz-id'],
    ['href="../../assets/theme.css"', 'loads the shared theme'],
    ['class="crumb" href="../../"', 'links back to the index'],
    ['<title>', 'has a <title>'],
    ['data-title-en="', 'gives an English title on <html>'],
    ['data-lang-set="zh"', 'offers the Chinese switch'],
    ['data-lang-set="en"', 'offers the English switch']
  ];
  for (const [needle, why] of need) if (!html.includes(needle)) fail(`${page}: ${why} (expected ${needle})`);
  const head = html.slice(0, html.indexOf('</head>'));
  if (!head.includes('src="../../assets/shell.js"')) fail(`${page}: loads the shared runtime in <head> (expected src="../../assets/shell.js" before </head>)`);
  const zhCount = (html.match(/class="[^"]*\bzh\b/g) || []).length, enCount = (html.match(/class="[^"]*\ben\b/g) || []).length;
  if (zhCount !== enCount) fail(`${page}: ${zhCount} .zh fragments but ${enCount} .en fragments; every text fragment needs both languages`);
}

// 2b. the index page follows the same language contract
{
  const html = read('index.html');
  for (const needle of ['data-lang-set="zh"', 'data-lang-set="en"', 'data-title-en="']) if (!html.includes(needle)) fail(`index.html: expected ${needle}`);
  const zhCount = (html.match(/class="[^"]*\bzh\b/g) || []).length, enCount = (html.match(/class="[^"]*\ben\b/g) || []).length;
  if (zhCount !== enCount) fail(`index.html: ${zhCount} .zh fragments but ${enCount} .en fragments`);
}

// 3. every viz directory is registered
if (exists('viz')) {
  for (const dir of fs.readdirSync(path.join(ROOT, 'viz'))) {
    if (fs.statSync(path.join(ROOT, 'viz', dir)).isDirectory() && !seen.has(dir)) fail(`viz/${dir}/ is not registered in visualizations.json`);
  }
}

// 4. local links in site HTML resolve, and nothing is rooted at "/" (Pages serves under /<repo>/)
const htmlFiles = ['index.html'];
for (const v of entries) if (exists(`viz/${v.id}/index.html`)) htmlFiles.push(`viz/${v.id}/index.html`);
for (const rel of htmlFiles) {
  const html = read(rel);
  for (const m of html.matchAll(/\s(?:src|href)="([^"]+)"/g)) {
    const url = m[1];
    if (/^(https?:|mailto:|data:|#)/.test(url)) continue;
    if (url.startsWith('/')) { fail(`${rel}: root-absolute link "${url}" breaks under /<repo>/`); continue; }
    let target = path.join(path.dirname(rel), url.split(/[?#]/)[0]);
    if (url.endsWith('/') || url === '.' || url === './') target = path.join(target, 'index.html');
    if (!exists(target)) fail(`${rel}: link "${url}" does not resolve (${target})`);
  }
}

// 5. every first-party script parses
const scripts = [];
const walk = (dir) => {
  for (const name of fs.readdirSync(path.join(ROOT, dir))) {
    const rel = path.join(dir, name);
    const st = fs.statSync(path.join(ROOT, rel));
    if (st.isDirectory()) { if (name !== 'vendor' && name !== 'node_modules') walk(rel); }
    else if (/\.(m?js)$/.test(name)) scripts.push(rel);
  }
};
for (const d of ['assets', 'viz', 'scripts', 'templates', 'tests']) if (exists(d)) walk(d);
for (const rel of scripts) {
  try { execFileSync(process.execPath, ['--check', path.join(ROOT, rel)], { stdio: 'pipe' }); }
  catch (e) { fail(`${rel}: ${String(e.stderr || e.message).trim().split('\n').slice(0, 4).join(' | ')}`); }
}

if (problems.length) {
  console.error(`validate: ${problems.length} problem(s)`);
  for (const p of problems) console.error('  - ' + p);
  process.exit(1);
}
console.log(`validate: ok · ${entries.length} registered (${entries.filter((v) => v.status === 'live').length} live) · ${htmlFiles.length} pages · ${scripts.length} scripts`);
