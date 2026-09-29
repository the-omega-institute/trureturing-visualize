#!/usr/bin/env node
// Scaffold a new visualization from templates/viz-starter and register it as a draft.
//   node scripts/new-viz.mjs <id> "<CODE//NAME>" "<中文标题>" ["<English title>"]
// Drafts are published at their URL but stay off the index until status is set to "live".
import fs from 'node:fs';
import path from 'node:path';
import { ROOT, ID_RE, readRegistry, writeRegistry } from './site.mjs';

const [id, code, title, titleEn = ''] = process.argv.slice(2);
if (!id || !code || !title) {
  console.error('usage: node scripts/new-viz.mjs <id> "<CODE//NAME>" "<中文标题>" ["<English title>"]');
  process.exit(2);
}
if (!ID_RE.test(id)) { console.error(`id "${id}" must be kebab-case`); process.exit(2); }
const dest = path.join(ROOT, 'viz', id);
if (fs.existsSync(dest)) { console.error(`viz/${id}/ already exists`); process.exit(2); }
const reg = readRegistry();
if (reg.visualizations.some((v) => v.id === id)) { console.error(`${id} is already registered`); process.exit(2); }

const src = path.join(ROOT, 'templates', 'viz-starter');
const [codeHead, ...codeRest] = code.split('//');
const codeHtml = codeRest.length ? `${codeHead}<b>//</b>${codeRest.join('//')}` : code;
fs.mkdirSync(dest, { recursive: true });
for (const name of fs.readdirSync(src)) {
  const text = fs.readFileSync(path.join(src, name), 'utf8')
    .replaceAll('__ID__', id).replaceAll('__CODE_HTML__', codeHtml).replaceAll('__CODE__', code).replaceAll('__TITLE_EN__', titleEn || title).replaceAll('__TITLE__', title);
  fs.writeFileSync(path.join(dest, name), text);
}
reg.visualizations.push({
  id, code, title, title_en: titleEn, summary: '', summary_en: '', path: `viz/${id}/`, thumbnail: `viz/${id}/thumb.jpg`,
  status: 'draft', added: new Date().toISOString().slice(0, 10), tags: [], tags_en: [], theory: [], lean: []
});
writeRegistry(reg);
console.log(`created viz/${id}/ and registered it as a draft.
next: edit viz/${id}/ (every text in both .zh and .en), fill summary/summary_en/theory in visualizations.json, run node scripts/thumbs.mjs ${id}, set status to "live", then node scripts/validate.mjs`);
