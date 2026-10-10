# trureturing-visualize

Interactive visualizations of the theory in [trureturing](https://github.com/the-omega-institute/trureturing), published with GitHub Pages at
**https://the-omega-institute.github.io/trureturing-visualize/**.

Every page is bilingual (中文 / English, switchable in the header) and states three things: which theory sections it draws on, which results are kernel-verified Lean theorems frozen in trureturing, and which parts are a schematic model chosen to make the structure visible. A visualization proves nothing. Mathematical truth stays with the Lean declarations in trureturing.

## Visualizations

| id | Page | Theory |
| --- | --- | --- |
| `hard-squares` | [HARD//SQUARES 硬方块格气 · 互不相邻的粒子](https://the-omega-institute.github.io/trureturing-visualize/viz/hard-squares/) | 问题卷宗：Adamaszek 2012 · Davies 等 2026 |
| `prime-gaps` | [PRIME//GAPS 素数间隙 · 素数能挤多近、能隔多远](https://the-omega-institute.github.io/trureturing-visualize/viz/prime-gaps/) | 问题卷宗：OEIS A079063 · A089610 · A049591 |
| `explicit-formula` | [EXPLICIT//FORMULA 显式公式 · 用 ζ 的零点重建素数](https://the-omega-institute.github.io/trureturing-visualize/viz/explicit-formula/) | Lean：D5/S3/Weil 的 ZetaBridge · Separator · ZeroInfinitude · PrimeNumberTheorem |
| `state-transfer` | [STATE//TRANSFER 完美态传输 · 量子行走把态送到哪里](https://the-omega-institute.github.io/trureturing-visualize/viz/state-transfer/) | 问题卷宗：Song–Lin 2026 · Connelly 等 2017 · Kay 2010 |
| `fourth-basis` | [FOURTH//BASIS 六维第四组互无偏基 · 一个开放问题](https://the-omega-institute.github.io/trureturing-visualize/viz/fourth-basis/) | 六维第四组互无偏基理论卷 §0 §23 |
| `whole-parts` | [WHOLE//PARTS 整体大于局部 · 纠缠、局部盲区与隐形传态](https://the-omega-institute.github.io/trureturing-visualize/viz/whole-parts/) | 观察者完备反射 §118–§120 · 递归关系观察 §165 |
| `hermite-ladder` | [HERMITE//LADDER 量子谐振子 · 能级阶梯与厄米函数](https://the-omega-institute.github.io/trureturing-visualize/viz/hermite-ladder/) | 谐振子微分图 定理 6.1 7.1 8.1 |
| `tomo-glance` | [TOMO//GLANCE 互补与层析 · 一次看不全](https://the-omega-institute.github.io/trureturing-visualize/viz/tomo-glance/) | 观察者完备反射 §83 §86 §100 · GICT 6.38 E.168 |
| `syndrome-mend` | [SYNDROME//MEND 量子纠错 · 离开编码空间不等于丢了信息](https://the-omega-institute.github.io/trureturing-visualize/viz/syndrome-mend/) | 量子现实 ST27–ST31 |
| `dark-walk` | [DARK//WALK 首次探测与暗态 · 永远找不到的行走者](https://the-omega-institute.github.io/trureturing-visualize/viz/dark-walk/) | 波粒整体的关系全息表示 §11–§13 §49 |
| `zeno-watch` | [ZENO//WATCH 量子芝诺效应 · 被盯住的跃迁](https://the-omega-institute.github.io/trureturing-visualize/viz/zeno-watch/) | 量子现实 §221–§230 · 锥程序 §5.4 |
| `delay-eraser` | [DELAY//ERASER 延迟选择量子擦除 · 先落点，后贴标签](https://the-omega-institute.github.io/trureturing-visualize/viz/delay-eraser/) | 波粒整体的关系全息表示 §5 §8 |
| `darwin-echo` | [DARWIN//ECHO 量子达尔文主义 · 事实的回声](https://the-omega-institute.github.io/trureturing-visualize/viz/darwin-echo/) | OBSERVER-QUANTUM §5 · GICT 定理 6.26 |
| `friend-bell` | [FRIEND//BELL Wigner 之友 · 贝尔竞技场](https://the-omega-institute.github.io/trureturing-visualize/viz/friend-bell/) | OBSERVER-QUANTUM §8 · GICT 观察 6.30 |
| `cat-ledger` | [CAT//LEDGER 薛定谔的猫 · 账本时空块](https://the-omega-institute.github.io/trureturing-visualize/viz/cat-ledger/) | 波粒整体的关系全息表示 §5 §8 §11–§13 · OBSERVER-QUANTUM §8 §18.2 |
| `chrono-slit` | [CHRONO//SLIT 双缝时空体](https://the-omega-institute.github.io/trureturing-visualize/viz/chrono-slit/) | 波粒整体的关系全息表示 §3 §4 §5 §8 §24 |

`visualizations.json` is the registry; the index page is rendered from it.

## Layout

```
index.html              index page, rendered from visualizations.json
404.html                self-contained "signal lost" page
visualizations.json     registry: one entry per visualization
assets/
  theme.css             shared tokens and components (panels, sliders, stage HUD, clock rail, drawer)
  shell.js              shared runtime, window.TRV (language switch, palette, canvas sizing, toast, glitch, drawer, seeded RNG)
  hub.css, hub.js       index page
  favicon.svg
  vendor/               pinned third-party scripts (three.js r128, MIT)
viz/<id>/               one visualization: index.html, style.css, main.js, thumb.jpg
templates/viz-starter/  starting point copied by scripts/new-viz.mjs (not published)
tests/<id>.test.mjs     browser regression suite for a visualization (Playwright)
scripts/                validate, serve, build, thumbs, new-viz, test-browser (Node >= 20, no runtime dependencies)
```

There is no build step. The published site is the repository's `index.html`, `404.html`, `visualizations.json`, `assets/` and `viz/`, copied as they are.

## Local preview

```sh
node scripts/serve.mjs          # http://127.0.0.1:8765/trureturing-visualize/
node scripts/validate.mjs       # registry, page contract, links, script syntax
node scripts/test-browser.mjs   # browser suites in tests/ (needs Playwright with Chromium)
```

The server mounts the site under `/trureturing-visualize/`, the same prefix GitHub Pages uses, so root-relative mistakes show up locally.

## Adding a visualization

1. Scaffold it:
   ```sh
   node scripts/new-viz.mjs <id> "<CODE//NAME>" "<中文标题>" "<English title>"
   ```
   This copies `templates/viz-starter/` to `viz/<id>/` and registers a `draft` entry. Drafts are published at their URL but stay off the index.
2. Build the page in `viz/<id>/`, in both languages. Keep the shared theme and runtime, the language switch, the link back to the index, and the theory drawer.
3. Fill the registry entry in both languages: `title_en`, `summary` / `summary_en`, `tags` / `tags_en`, `theory` (theory volume links with `label` / `label_en`) and `lean` (frozen theorem names and file links only).
4. Capture the index thumbnail:
   ```sh
   node scripts/thumbs.mjs <id>
   ```
   It screenshots the element marked `data-thumb`, or the page's `.stage`. A page can define `window.TRV_THUMB()` to switch into a cover state first. Playwright is needed only for this step (`npm i -D playwright`, or a global install).
5. Add `tests/<id>.test.mjs` for the page's controls and invariants; `tests/chrono-slit.test.mjs` shows the pattern, reading state through a read-only `window.<NAME>_DEBUG` probe.
6. Set `status` to `live`, run `node scripts/validate.mjs` and `node scripts/test-browser.mjs`, and open a pull request. CI validates every pull request; merging to `main` deploys.

## Two languages

`assets/shell.js` sets `<html data-lang>` before the page renders. The language comes from `?lang=zh|en`, then the visitor's last choice (stored in the browser), then the browser language. Every page carries a `中 / EN` switch (`data-lang-set`).

- Static text is written twice, `<span class="zh">…</span><span class="en">…</span>`; `theme.css` shows one of them. Without script, Chinese shows.
- Text built by script goes through `TRV.L('中文', 'English')`; pages re-render it in `TRV.onLang(fn)`.
- Attributes: put the Chinese in `aria-label` and the English in `data-aria-en`; the page `<title>` is the Chinese title and `<html data-title-en>` the English one.

## Page contract

`scripts/validate.mjs` fails when any of these break:

- every `viz/<dir>/` is registered, and every entry has `path` `viz/<id>/`, a kebab-case `id`, a date, and a thumbnail inside its own folder;
- each page sets `data-viz-id` on `<body>`, loads `../../assets/theme.css`, loads `../../assets/shell.js` inside `<head>`, and links back with `class="crumb" href="../../"`;
- each page (and the index) has the `中 / EN` switch, a `data-title-en`, and as many `.en` fragments as `.zh` fragments; live registry entries carry `title_en`, `summary_en`, a `tags_en` for every tag and a `label_en` for every theory reference;
- live entries name at least one theory reference, and every reference link is `https`;
- local `src`/`href` links resolve, and none is rooted at `/` (Pages serves the site under `/trureturing-visualize/`);
- every first-party script passes `node --check`.

## Style

One night-console look across pages: tokens in `assets/theme.css`, Chakra Petch for display, Noto Sans SC for text, JetBrains Mono for numbers. Colour carries meaning. Cyan, magenta and the rest of the branch palette tell conditional branches apart. Amber marks "now" and the current selection. Green marks a Lean-verified statement. Pages respect `prefers-reduced-motion` and work at phone width without horizontal scrolling.

## Deployment

`.github/workflows/pages.yml` validates and runs the browser suites on every pull request. On a push to `main` it does the same, assembles `_site/` with `scripts/build.mjs`, and deploys with `actions/deploy-pages` once both jobs pass. Two repository settings are required once:

- Settings → Pages → Build and deployment → Source: **GitHub Actions**.
- The repository must be allowed to publish Pages: either it is public, or the organization's plan allows Pages from private repositories.

## License

Apache-2.0, see [LICENSE](LICENSE). `assets/vendor/three.r128.min.js` is three.js r128 under the MIT license (header retained in the file).
