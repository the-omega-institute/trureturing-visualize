#!/usr/bin/env node
// Run every browser regression suite in tests/*.test.mjs, one after another:  node scripts/test-browser.mjs
// Each suite is a standalone script that exits non-zero when a check fails. Needs Playwright with Chromium.
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { ROOT } from './site.mjs';

const dir = path.join(ROOT, 'tests');
const suites = fs.existsSync(dir) ? fs.readdirSync(dir).filter((f) => f.endsWith('.test.mjs')).sort() : [];
if (!suites.length) { console.log('no browser suites in tests/'); process.exit(0); }
let failed = 0;
for (const f of suites) {
  console.log(`\n=== ${f}`);
  const r = spawnSync(process.execPath, [path.join(dir, f)], { stdio: 'inherit' });
  if (r.status !== 0) failed++;
}
console.log(`\n${suites.length - failed}/${suites.length} suites passed`);
process.exit(failed ? 1 : 0);
