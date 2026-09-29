// Shared facts about the published site, used by the other scripts.
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import fs from 'node:fs';

export const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
/** Paths copied into the Pages artifact; everything else in the repo stays out of the site. */
export const SITE_ENTRIES = ['index.html', '404.html', 'visualizations.json', 'assets', 'viz'];
export const ID_RE = /^[a-z0-9]+(?:-[a-z0-9]+)*$/;
export const STATUSES = ['live', 'draft'];

export function readRegistry() {
  return JSON.parse(fs.readFileSync(path.join(ROOT, 'visualizations.json'), 'utf8'));
}
export function writeRegistry(reg) {
  fs.writeFileSync(path.join(ROOT, 'visualizations.json'), JSON.stringify(reg, null, 2) + '\n');
}
