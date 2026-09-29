#!/usr/bin/env node
// Copy the published entries into an output directory (default _site):  node scripts/build.mjs [outDir]
// There is no compile step; the site is served exactly as it is in the repository.
import fs from 'node:fs';
import path from 'node:path';
import { ROOT, SITE_ENTRIES } from './site.mjs';

const out = path.resolve(ROOT, process.argv[2] || '_site');
if (out === ROOT || !out.startsWith(ROOT + path.sep)) { console.error('output directory must be inside the repository'); process.exit(2); }
fs.rmSync(out, { recursive: true, force: true });
fs.mkdirSync(out, { recursive: true });
for (const entry of SITE_ENTRIES) fs.cpSync(path.join(ROOT, entry), path.join(out, entry), { recursive: true });
fs.writeFileSync(path.join(out, '.nojekyll'), '');
let files = 0, bytes = 0;
const walk = (d) => { for (const n of fs.readdirSync(d)) { const p = path.join(d, n), st = fs.statSync(p); if (st.isDirectory()) walk(p); else { files++; bytes += st.size; } } };
walk(out);
console.log(`built ${path.relative(ROOT, out)}/ · ${files} files · ${(bytes / 1024).toFixed(0)} KiB`);
