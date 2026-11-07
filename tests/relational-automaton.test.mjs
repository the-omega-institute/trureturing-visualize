#!/usr/bin/env node
import path from 'node:path';
import { createRequire } from 'node:module';
import { createServer, BASE } from '../scripts/serve.mjs';
async function loadPlaywright() {
  try { return await import('playwright'); } catch {}
  const { execSync } = await import('node:child_process');
  return createRequire(path.join(execSync('npm root -g').toString().trim(), 'noop.js'))('playwright');
}
const { chromium } = await loadPlaywright();
const server = createServer(); await new Promise((r) => server.listen(0, '127.0.0.1', r));
const browser = await chromium.launch({ args: ['--use-angle=swiftshader', '--enable-unsafe-swiftshader', '--ignore-gpu-blocklist'] });
const page = await browser.newPage({ viewport: { width: 1440, height: 900 }, locale: 'zh-CN' });
const errors = [];
page.on('pageerror', (e) => errors.push(e.message));
const checks = [];
const check = (name, ok) => { checks.push(ok); console.log((ok ? 'PASS ' : 'FAIL ') + name); };
const info = () => page.evaluate(() => RQA_DEBUG.info());
const state = () => page.evaluate(() => RQA_DEBUG.state());
await page.goto('http://127.0.0.1:' + server.address().port + BASE + 'viz/relational-automaton/');
await page.waitForFunction(() => window.RQA_DEBUG);
let i = await info();
check('opens at identity step', (await state()).step === 0 && i.norm === 1 && i.edges === 0);
await page.click('[data-step="1"]'); i = await info();
check('split step has two equal Born branches', i.step === 1 && Math.abs(i.norm - 1) < 1e-12 && Math.abs(i.born[0] - 0.5) < 1e-12 && i.edges === 1);
await page.evaluate(() => RQA_DEBUG.setStep(2)); await page.evaluate(() => RQA_DEBUG.setPhase(90)); i = await info();
check('phase step keeps normalization and records the phase', i.step === 2 && i.phase === 90 && Math.abs(i.norm - 1) < 1e-12 && Math.abs(i.born[0] - 0.5) < 1e-12);
await page.evaluate(() => RQA_DEBUG.setStep(3)); i = await info();
check('network step closes the triangle and keeps the norm', i.step === 3 && i.edges === 6 && Math.abs(i.norm - 1) < 1e-12 && i.bloch.length === 3);
check('rule inspector exposes six finite closure rules', i.rules.length === 6 && i.rules[0].status === 'PASS' && i.rules.every((r) => r.status === 'PASS'));
await page.click('[data-rule="2"]'); await page.click('#faultBtn'); i = await info();
check('selected rule can expose a concrete counterexample state', i.rules[2].status === 'FAIL' && i.rules[2].reason.length > 0);
await page.click('#faultBtn'); i = await info();
check('counterexample mode restores the rule', i.rules[2].status === 'PASS');
await page.click('[data-lang-set="en"]'); await page.waitForTimeout(250);
check('English mode changes the document title', (await page.title()).startsWith('REL//AUTOMATON · Relational quantum automaton'));
await page.click('#infoBtn'); await page.waitForTimeout(100);
check('the theory drawer opens', !(await page.locator('#drawer').getAttribute('hidden')));
await page.keyboard.press('Escape'); await page.waitForTimeout(100);
check('Escape closes the theory drawer', await page.locator('#drawer').getAttribute('hidden') !== null);
check('no page errors', errors.length === 0);
const passed = checks.filter(Boolean).length;
console.log(passed + '/' + checks.length + ' passed');
await browser.close(); server.close();
if (passed !== checks.length) process.exit(1);
