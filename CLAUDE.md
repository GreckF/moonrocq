# MoonRocq 工作约定

用 Rocq 实现的 MoonBit 类型检查器 / 静态分析基座，要证明 type soundness 和 decidability，并为抽取到 OCaml 留空间。
整体设计见 `DESIGN.md`，开工前先读。与用户用中文交流。

## 构建
- Rocq 9.1.1 装在 WSL Ubuntu 的 opam switch `5.5.0` 中（同一 switch 里还有 Equations、mathcomp、elpi）。
- 从 Windows Git Bash 构建：
  `MSYS_NO_PATHCONV=1 wsl.exe -d Ubuntu -- bash -l /mnt/c/Users/86158/Documents/projects/Claude/moonrocq/scripts/build.sh 2>&1 | tr -d '\0' | grep -av -e translate -e localhost`
  成功时最后一行是 `BUILD_OK`。
- 公理审计和冒烟测试：用同样的方式运行 `scripts/check_assumptions.sh`。主定理都应输出 `Closed under the global context`，最后一行是 `TESTS_OK`。新增主定理时，要把它加入 `tests/Assumptions.v`。
- 官方工具链 `moon` 在 WSL 的 `~/.moon/bin`（不在 PATH 中），Windows 侧也有，用于差分实验。

## 规则
- 这是长期项目：不要 ad-hoc 地堵问题。遇到语言特性先想清楚它在 Core 中的位置，再动手。
- 不允许 `Admitted` / `admit` / 新增 `Axiom` 进入主线；尚未支持的构造让 checker 报 unsupported。
- 方法论（用户明确要求）：类型规则和小步求值语义都用 `Inductive` 定义；小步语义只用于证明 type soundness（progress + preservation），不写解释器。
- type checker 采用 correct by construction：返回 `result {τ | has_type Γ e τ} err`，可靠性由构造保证；完备性单独证明；两者合起来得到 decidability。
- 判断放在 `Prop` 中，这样抽取时会被擦除；计算部分只做 `Type` 上的结构递归或 Equations 良基递归，不对 `Prop` 证明做消去来驱动计算。
- 暂时不做抽取和解析器，但代码要给抽取留出空间。
- 计算路径上用到的判定过程必须透明（`Defined`）；Stdlib 中用 Qed 封装的（如 `ListDec.NoDup_dec`）不能用，用 `Prelude/ListDec.v` 的版本。`tests/Examples.v` 用 `vm_compute` 检查 checker 确实能规约。
- 自行决定的语言细节记到 `docs/decisions.md`。
- 相等判定统一用 `Prelude/EqDec.v` 的 `EqDec` 类。
- 文档有歧义的语言细节，用 `moon` 做实验确认，并记到 `docs/decisions.md`。
- 语言参考：`ref/moonbit-docs/next/language/*.md`，示例代码在 `ref/moonbit-docs/next/sources/`。
