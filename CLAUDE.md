# MoonRocq 工作约定

用 Rocq 实现的 MoonBit 类型检查器 / 静态分析基座，要证明 type soundness 和 decidability，用 rocq2mbt 抽取到 MoonBit。
整体设计见 `DESIGN.md`，开工前先读。与用户用中文交流。

## 构建
- 用 rocq2mbt 的项目本地 opam switch（Rocq 9.4+alpha，已装 rocq-stdlib）：`scripts/env.sh`
  会 source `../rocq2mbt/scripts/env.sh`。旧的 switch `5.5.0`（Rocq 9.1.1）不再使用。
  rocq-stdlib 是这样装进去的：`opam pin add rocq-stdlib git+https://github.com/rocq-prover/stdlib.git#22fcaa27d17bc28ab4be728ed10a1fb73afb23ee`（与插件 pin 的 Rocq commit 同期的 master）。
  不要往这个 switch 以外装东西；改 rocq2mbt 插件要遵守 `../rocq2mbt/CLAUDE.md`。
- 同一 switch 里装了 `vsrocq-language-server` 2.5.1（2026-11-06，供 VS Code 检阅；它会让
  `rocq-runtime` 带上可选依赖 `memprof-limits` 重编一次）。`.vscode/settings.json`（不入库）的
  `vsrocq.path` 指向 `~/.local/share/rocq2mbt/_opam/bin/vsrocqtop`；先 `build.sh` 生成 `.vo`。
- 从 Windows Git Bash 运行（`<script>` 换成下面的脚本）：
  `MSYS_NO_PATHCONV=1 wsl.exe -d Ubuntu -- bash -l /mnt/c/Users/86158/Documents/projects/Claude/moonrocq/scripts/<script> 2>&1 | tr -d '\0' | grep -av -e translate -e localhost`
  - `build.sh`：dune build，最后一行 `BUILD_OK`；
  - `check_assumptions.sh`：公理审计 + `tests/Examples.v`，主定理都应 `Closed under the global context`，最后一行 `TESTS_OK`。新增主定理时，要把它加入 `tests/Assumptions.v`；
  - `extract.sh`：重新生成 `extraction/Parser.v`（mbti2rocq），编译 `extraction/Driver.v`，写出 `mbt/checker/moonrocq.mbt`，最后一行 `EXTRACT_OK`；
  - `test_frontend.sh`：构建命令行工具，对 `examples/{ok,bad,unsupported}` 与 `moon check` 做差分，最后一行 `FRONTEND_OK`。
- 改了 `theories/` 中计算相关的代码后，要依次跑 `extract.sh` 和 `test_frontend.sh`。
- 官方工具链 `moon` 在 WSL 的 `~/.moon/bin`（env.sh 会加进 PATH）：moon 0.1.20261104 / moonc v0.10.20
  （2026-11-06 升级；旧版备份在 `~/.moon.bak-20260814`）。依赖：`moonbitlang/parser@0.4.7`、
  `moonbitlang/lexer@0.4.4`、`moonbitlang/x@0.5.7`。命令行参数用 `@env.args()`。

## 规则
- 这是长期项目：不要 ad-hoc 地堵问题。遇到语言特性先想清楚它在 Core 中的位置，再动手。
- 不允许 `Admitted` / `admit` / 新增 `Axiom` 进入主线；尚未支持的构造让 checker 报 unsupported。
- 方法论（用户明确要求）：类型规则和小步求值语义都用 `Inductive` 定义；小步语义只用于证明 type soundness（progress + preservation），不写解释器。
- type checker 采用 correct by construction：返回 `result {τ | has_type Γ e τ} err`，可靠性由构造保证；完备性单独证明；两者合起来得到 decidability。
- 判断放在 `Prop` 中，这样抽取时会被擦除；计算部分只做 `Type` 上的结构递归或 Equations 良基递归，不对 `Prop` 证明做消去来驱动计算。
- 抽取：`MoonRocq` 库只依赖 Stdlib；抽取命令、胶水公理只放在 `extraction/Driver.v`。
  `extraction/Parser.v` 和 `mbt/checker/moonrocq.mbt` 是生成文件，不要手改。
  MoonBit 胶水（`mbt/checker/lower.mbt`、`show.mbt`）不受信任，只做语法投影和打印，不做名字解析和类型判断。
- `Surface/Elab.v` 是 M1.5 的临时 elaborator（无规范、无证明），M6 会按 DESIGN.md 第 2 节重写。
  在它上面加特性时保持“类型只问 Core `infer`”。
- 计算路径上用到的判定过程必须透明（`Defined`）；Stdlib 中用 Qed 封装的（如 `ListDec.NoDup_dec`）不能用，用 `Prelude/ListDec.v` 的版本。`tests/Examples.v` 用 `vm_compute` 检查 checker 确实能规约。
- 自行决定的语言细节记到 `docs/decisions.md`。
- 相等判定统一用 `Prelude/EqDec.v` 的 `EqDec` 类。
- 判断一律用记号书写（定义处用 `Reserved Notation` + `where`，因此判断的 `ge`、`Σ` 是 inductive 的参数，而不是 section 变量）：
  `Γ ⊢[ge;Σ;Λ] e : τ`、`Γ ⊢*[ge;Σ;Λ] es : τs`、`Γ ⊢ᵇ[ge;Σ;Λ] bs : τs ⇒ τ`（`Σ` store typing，`Λ` 标签上下文）、
  `⟨σ ∣ K ▷ e⟩` / `⟨σ ∣ K ◁ v⟩` / `⟨σ ∣ K ⇑ c k v⟩`、`s ⟶[ge] s'`、`s ⟶*[ge] s'`、
  `⊢ᵖ[ge] p : τ ⇝ Δ`、`⊢ᵖ*[ge] ps : τs ⇝ Δ`、
  `⊢ᶠ[ge;Σ;Λ] F : τ ⇒ τ'`、`⊢ᵏ[ge;Σ] K : τ ⇒ τ'`、`⊢ˢ[ge] s : τ`。不要用 `|-`：它会和 Ltac 的 `H : _ |- _` 冲突。
  在 section 外显式应用构造子时，要写出 `ge`、`Σ`，例如 `FT_Tuple ge Σ ...`、`T_Lit ge Σ Λ Γ l`。
- 命名：Core 的 store typing 项是 `lty`（`LCell`/`LArr`），标签上下文是 `lblctx`；Surface 的类型是 `sty`、
  Elab 的局部上下文是 `lctx`。抽取后同名会冲突，不要在 Core 里再用 `sty`/`lctx` 这类名字。
- 在 Windows 上用 Python 改文件时要写 `newline='\n'`，否则会产生 CRLF。
- 文档有歧义的语言细节，用 `moon` 做实验确认，并记到 `docs/decisions.md`。
- 语言参考：`ref/moonbit-docs/next/language/*.md`，示例代码在 `ref/moonbit-docs/next/sources/`。
- 用 Python 改 `.v` 文件时，脚本先用 Write 工具写成文件再运行：Bash 工具会把行尾的 `\` 当作续行吃掉
  （即使在带引号的 heredoc 里），破坏 `/\` 合取。
- `Surface/Elab.v` 打开了 `string_scope`，那里的 `++`、`length`、`concat` 会解析成字符串版本，
  列表要写 `List.app`、`List.length`、`List.concat`。
