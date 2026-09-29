# trureturing-visualize · agent 工作守则

本仓库收纳 trureturing 理论的交互可视化，经 GitHub Pages 发布在 `https://the-omega-institute.github.io/trureturing-visualize/`。它只负责展示：数学真值以 trureturing 中经 Lean 内核验证的声明为准，页面不承担证明。

## 结构

- `visualizations.json` 是唯一注册表；索引页 `index.html` 由它渲染，`scripts/validate.mjs` 用它核对磁盘上的页面。
- `assets/theme.css`、`assets/shell.js`（`window.TRV`）是所有页面共享的外观与运行时。可复用的样式和辅助函数放这里；只属于某个可视化的布局和逻辑放在 `viz/<id>/`。
- 每个可视化一个目录：`viz/<id>/index.html`、`style.css`、`main.js`、`thumb.jpg`。
- 新可视化从 `templates/viz-starter/` 开始，用 `node scripts/new-viz.mjs <id> "<CODE//NAME>" "<中文标题>" "<English title>"` 生成并登记为 `draft`。

## 规则

1. **无构建步骤，无运行时依赖。** 页面是纯 HTML/CSS/JS；第三方脚本钉版后放 `assets/vendor/` 并保留许可证头。字体只从 Google Fonts 加载。
2. **只用相对链接。** 站点挂在 `/trureturing-visualize/` 下，任何以 `/` 开头的本地链接都会断。
3. **页面契约由 `validate.mjs` 机器检查**：`data-viz-id`、引用共享主题与（`<head>` 内的）运行时、中英切换与成对的 `.zh`/`.en` 片段、`class="crumb" href="../../"` 返回索引、注册表字段完整、本地链接可解析、脚本能通过 `node --check`。
4. **诚实标注。** 每个页面的理论接口抽屉必须写明：依据的理论卷与节号；哪些结论是 trureturing 中已冻结的 Lean 定理（给定理名和文件链接）；哪些是示意模型及其简化。只有在 trureturing 的 `Golden/Frozen/state/` 中确有冻结状态片的定理才能标 `LEAN ✓`；不得把示意模型的数值说成物理模拟，也不得把理论卷散文说成已证。
5. **双语。** 所有可见文字都要中英两份：静态文字写成成对的 `<span class="zh">…</span><span class="en">…</span>`；脚本生成的文字用 `TRV.L('中文', 'English')`，并在 `TRV.onLang(...)` 里重绘；`aria-label` 写中文、`data-aria-en` 写英文；`<html data-title-en>` 给英文标题。注册表的已发布条目要有 `title_en`、`summary_en`、`tags_en`、`label_en`。英文要自然、准确，不逐字硬译；理论卷只有中文时，在英文说明里注明。
6. **颜色有语义。** 分支/类别用 `TRV.rgb` 或页面自己的分支色板；琥珀色只留给“现在”与当前选择；绿色只留给 Lean 已验证。保持 `prefers-reduced-motion` 与手机宽度（约 400px）无横向滚动。
7. **提交前验证。** 至少运行 `node scripts/validate.mjs` 和 `node scripts/test-browser.mjs`（每个可视化在 `tests/<id>.test.mjs` 有浏览器回归测试，覆盖全部控件与页面声称的不变量；页面承诺的性质要有对应检查）；改动页面时用 `node scripts/serve.mjs` 在桌面和手机宽度、中英两种语言（`?lang=zh`、`?lang=en`）实际打开，确认无脚本错误、英文模式下没有漏译。缩略图用 `node scripts/thumbs.mjs <id>` 生成（页面可定义 `window.TRV_THUMB()` 切到封面状态）。
8. **经 PR 合入 `main`。** CI 对每个 PR 运行校验；合入 `main` 后自动部署 Pages。完成以 PR 合并且部署成功为准。
