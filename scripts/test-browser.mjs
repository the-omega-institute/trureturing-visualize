#!/usr/bin/env node
// Run the browser regression suites in tests/*.test.mjs, one after another:
//   node scripts/test-browser.mjs                 every suite
//   node scripts/test-browser.mjs --shard 2/4     suites 2, 6, 10, … of the sorted list (CI runs the shards in parallel)
//   node scripts/test-browser.mjs --shard 2/4 --list   print the selection without running it
// Each suite is a standalone script that exits non-zero when a check fails. Needs Playwright with Chromium.
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { ROOT } from './site.mjs';

const args = process.argv.slice(2);
const at = args.indexOf('--shard');
let shard = [1, 1];
if (at >= 0) {
  const m = /^(\d+)\/(\d+)$/.exec(args[at + 1] || '');
  if (!m || +m[1] < 1 || +m[1] > +m[2]) { console.error('usage: --shard i/n with 1 ≤ i ≤ n'); process.exit(2); }
  shard = [+m[1], +m[2]];
}
const dir = path.join(ROOT, 'tests');
const all = fs.existsSync(dir) ? fs.readdirSync(dir).filter((f) => f.endsWith('.test.mjs')).sort() : [];
const suites = all.filter((_, k) => k % shard[1] === shard[0] - 1);
if (args.includes('--list')) { console.log(suites.join('\n')); process.exit(0); }
if (!suites.length) { console.log(all.length ? `shard ${shard[0]}/${shard[1]} has no suites` : 'no browser suites in tests/'); process.exit(0); }
let failed = 0;
for (const f of suites) {
  console.log(`\n=== ${f}`);
  const r = spawnSync(process.execPath, [path.join(dir, f)], { stdio: 'inherit' });
  if (r.status !== 0) failed++;
}
console.log(`\n${suites.length - failed}/${suites.length} suites passed${shard[1] > 1 ? ` (shard ${shard[0]}/${shard[1]})` : ''}`);
process.exit(failed ? 1 : 0);
