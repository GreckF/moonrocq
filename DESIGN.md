# MoonRocq 设计说明

目标：用 Rocq 写一个第三方的 MoonBit 类型检查与静态分析基座，在 Rocq 中证明
**type soundness** 和 **type checking decidable**。日后会抽取成可运行的 type checker，
抽取不在当前范围内，但写代码时要给它留出空间。解析器同样暂不考虑。

语言参照：`ref/moonbit-docs`（moonbitlang/moonbit-docs @ `4d3b9d3`，2026-10-30），
主要依据 `next/language/*.md` 和 `next/sources/language/src/**/*.mbt`。
文档只给出了词法的形式文法，语法和语义都没有形式定义，所以**本项目的形式定义本身就是规范的一部分**。
文档有歧义时，用官方 `moon`（在 WSL 的 `~/.moon/bin` 下）做实验来判定，
结论记在 `docs/decisions.md`。

---

## 1. 方法论

每一层（Core，以及之后的 Surface）都由三部分组成：

1. **类型规则**：用 `Inductive` 定义的声明式判断，例如 `has_type : ctx -> expr -> ty -> Prop`。
2. **小步求值语义**：用 `Inductive` 定义的归约关系 `step : state -> state -> Prop`。
   它的唯一用途是陈述并证明 type soundness，不写解释器，也不需要能执行。
3. **类型检查器**：采用 correct by construction 的写法，返回值本身就带着推导：
   ```
   typecheck : forall Γ e, result {τ | has_type Γ e τ} type_error
   ```
   - **可靠性（soundness of the checker）**：由构造保证。返回 `Ok` 时，结果里就带着 `has_type` 的证明。
   - **完备性（completeness）**：单独证明，`has_type Γ e τ -> exists τ', typecheck Γ e = Ok τ'`
     （在类型唯一的层次上可以加强为 `τ' = τ`）。
   - 两者合起来得到 **decidability**：
     `forall Γ e τ, {has_type Γ e τ} + {~ has_type Γ e τ}`。

**Type soundness** = progress + preservation，加上多步归约不变式。
良类型的程序要么归约到值，要么以允许的方式终止（未捕获的 `raise` 属于声明的 effect、panic/`Abort`），
要么可以继续归约；绝不会卡住。

### 与抽取的兼容
`has_type` 等判断放在 `Prop` 里，所以 `{τ | has_type Γ e τ}` 抽取后就是 `τ`，
correct by construction 不会给抽取出来的代码带来负担。需要注意：
- 计算部分（检查器本身的分支、合一、查表）都是 `Type` 中的结构递归（需要时再引入良基递归），
  不能在 `Prop` 证明上做消去来驱动计算。
- 可判定相等统一用 `EqDec` 类（`Prelude/EqDec.v`），抽取后只剩布尔函数。
- 标识符用 Stdlib `string`，整数用 `Z` 加按位宽回绕，不引入公理。抽取到 MoonBit 后它们是
  归纳类型（`String0`、`Z`），胶水负责与 MoonBit 的 `String`/`BigInt` 互相转换；需要性能时再换表示。

## 2. 分层

```
 Surface AST    忠实反映 MoonBit 语法（名字、标签/可选参数、方法、管道、级联、is/guard、
   │            for-in、推导式、插值……）
   │  elaboration（类型检查器）：双向检查 + 一阶合一 + trait 解析
   ▼
 Core           显式类型、de Bruijn、字典传递之后的小内核演算
                inductive 类型规则 + inductive 小步语义 + soundness
                correct-by-construction checker + completeness
 Analysis       在带类型的 Core 上做：穷尽性/冗余、effect、未使用……
```

- **Core 尽量小，Surface 尽量全**：语法糖在 elaboration 阶段消去，证明成本集中在 Core 上，
  增加 Surface 特性不会动摇已有证明。
- **Surface 层**也遵循第 1 节的三件套：用 inductive 定义声明式的双向 elaboration 关系
  `Γ ⊢ s ⇒/⇐ τ ⇝ e`，规则做成语法制导。MoonBit 中依赖顺序的启发式
  （字面量重载的默认化、方法解析、trait object 的隐式转换）作为显式规则写进规范，不藏在算法里。
  elaborator 也按 correct by construction 来写（输出带有 elaboration 推导），并证明完备性。
  再结合“elaboration 结果在 Core 中良类型”，就得到 Surface 程序的 soundness。
  MoonBit 的顶层签名必须显式写出，局部函数是单态的，所以推断只发生在单个顶层定义内部
  （一阶合一 + 期望类型传播），可判定性是可以做到的。

## 3. 小步语义：栈机器

MoonBit 有大量非局部控制流：`return`、带标签和值的 `break`/`continue`、`raise`、
`defer`/`errdefer`。语义采用带显式栈的抽象机器（CK 风格），统一处理这些控制流：

```
state ::= ⟨σ, K, e⟩            (* 正在求值 e *)
        | ⟨σ, K, v⟩↑           (* 把值返回给栈顶 *)
        | ⟨σ, K, sig⟩⇑         (* 正在展开栈：Raise v | Break l v | Continue l vs | Return v *)
        | Abort                (* panic：越界、除零、match 失败、abort() …… *)
frame ::= 求值帧 | Loop | Try | Call | Defer | ErrDefer | ……
```

- `raise` 一路展开到 `Try` 帧，`break l` 展开到标签为 `l` 的 `Loop` 帧，`return` 展开到 `Call` 帧。
- 展开经过 `Defer` 帧时先执行清理。清理代码自己抛出的错误会替换原来的错误，与文档描述一致。
- 栈本身有类型：`Δ ⊢ K : τ ⇒ τ_final`，Δ 记录标签、handler 和返回类型。
  progress 中“`break` 一定能找到对应的 `Loop` 帧”这类事实，由栈的类型来保证。
- store σ 配合 store typing，处理 `let mut`、`mut` 字段和数组。
- 以后支持 async 时，可以把单个栈扩展成多个栈加调度器。

## 4. Core IR 草图（实现时定稿）

- **类型**：原始类型（Unit/Bool/各宽度整数/Double/Float/Char/Byte/String/Bytes/BigInt），
  元组，函数类型 `(τ…) -> τ ! ε`，名义类型构造子 `T[τ…]`
  （struct / enum / tuple struct / suberror / extenum），开放的 `Error`，类型变量，
  `&Trait`。`Ref`、`Array`、`Map`、`Iter` 等作为库类型。
- **Effect** `ε = (raise: none | E | 多态变量, async, cancel)`，
  覆盖 `raise`、`noraise`、`raise?`、`async`、`nocancel`。
- **多态**：rank-1，只有顶层带 trait bound 的类型参数；Core 中显式写类型应用和字典参数。
- **Trait**：elaborate 成字典；supertrait 是嵌套字典；默认方法在 impl 处补全。
  一致性（impl 唯一、孤儿规则、sealed trait）是全局环境上的可判定良构性检查。
  trait object 利用 object-safety，编码成“已部分应用的方法记录”。
- **状态**：`let mut` 被闭包捕获时按引用共享，统一作为 store 中的 cell。
- **模式**：嵌套的构造子/元组/字面量/范围/数组（含 `..rest`）/或模式（含 `with` 默认值）/`as`。
  match 失败归约到 `Abort`，所以 soundness 不依赖穷尽性；穷尽性作为单独的分析，另行证明。
- **原语**：内置运算通过带类型签名的原语接口给出，只要求“良类型输入归约到良类型结果或 `Abort`”，
  不在 Rocq 中建模 IEEE754 等细节。

## 5. 推进方式

**先设计全语言的 Core 语法，再按特性加入类型规则、归约规则和证明。**
checker 对尚未支持的构造直接拒绝，这样每个里程碑结束时，
对已支持的子集，soundness、checker 可靠性/完备性都**完整成立**。
主线上不允许 `Admitted`，也不允许新增公理。

| 里程碑 | 内容 |
|---|---|
| M0 | 基础设施：dune、Prelude（Result/EqDec/Ident），构建脚本 ✅ |
| M1 | Core λ：原始类型、函数、let、if、元组、全局（互）递归函数、rank-1 泛型、原语运算 ✅（见 `theories/Core/Theorems.v`） |
| M1.5 | 前端原型 ✅：经 rocq2mbt 抽取到 MoonBit，接上官方 parser，得到可运行的 `moonrocq` 命令（见第 7 节）。`Surface/Elab.v` 是**未经验证**的临时 elaborator，输出由 Core checker 重新检查；M6 用有规范的 certified elaborator 取代它 |
| M2 | 名义 ADT（struct/enum/tuple struct）+ 模式匹配 ✅（Core：`TData`、`EConstr`、`EMatch`，模式为通配/变量/字面量/元组/构造子；Surface：类型声明、构造子、记录、字段访问、`match`、解构 `let`、内建 `Option`；见第 8 节） |
| M3 | 状态与循环：`let mut`、`mut` 字段、数组、`while`/`for`、带标签 `break`/`continue`/`nobreak`、`return` |
| M4 | 错误与 effect：suberror、`Error`、`raise`/`raise?`/`noraise`、`try`/`catch`/`noraise`、`defer`/`errdefer` |
| M5 | trait：声明/impl/supertrait/默认方法、字典 elaboration、一致性、trait object |
| M6 | Surface + elaboration：双向检查、合一、字面量重载、标签/可选参数、方法/管道/级联、`is`/`guard`、`for-in`、推导式、插值…… |
| M7 | 包与可见性：`priv`/抽象/`pub`/`pub(all)`、`pub(open)` trait |
| M8 | 静态分析：穷尽性/冗余（Maranget）、未使用绑定、effect 相关检查…… |
| 以后 | async 细节、regex/`lexmatch`/`lexscan`、bitstring/map/json 模式、FFI、attributes、`derive` |

每个里程碑对当前子集都交付：inductive 类型规则、inductive 小步语义、progress/preservation、
correct-by-construction checker 和完备性证明。

## 6. 目录

```
theories/
  Prelude/    Result, EqDec, Ident，以后加 Map、Integers……
  Core/       Syntax, Typing, Semantics, Soundness, Check, CheckComplete……
  Surface/    Syntax, Elab（M1.5 原型），以后 ElabSpec, ElabComplete……
  Analysis/   Exhaustiveness……
extraction/   Parser.v（mbti2rocq 生成）、Driver.v（胶水公理 + check_source + Extraction）
mbt/          MoonBit 工程：checker/（抽取结果 + 胶水）、cmd/main/（命令行）
examples/     ok / bad / unsupported 三类示例，scripts/test_frontend.sh 与 moon check 做差分
scripts/      env.sh、build.sh、check_assumptions.sh、extract.sh、test_frontend.sh
ref/moonbit-docs   语言文档（不入库）
```

## 7. 前端与抽取（M1.5）

```
 源码 ──@parser.parse_string──▶ @syntax AST ──lower（MoonBit 胶水）──▶ sprog
      ──elab_prog（Rocq）──▶ Core genv + main ──check_program（Rocq，certified）──▶ 结论
```

- **环境**：与 rocq2mbt 共用其项目本地 opam switch（Rocq 9.4+alpha，含可扩展 extraction API，
  另装了 rocq-stdlib）。`MoonRocq` 库本身只依赖 Stdlib，抽取相关的东西都在 `extraction/`，
  不进库。
- **在 Rocq 中调用 parser**：`mbti2rocq` 把 `moonbitlang/parser` 的接口翻译成
  `extraction/Parser.v`（公理 + `Extract MoonBit Function`）。`@syntax` 的 AST 里用了
  `@list.List`（Rocq 中是公理类型），不满足严格正性，翻译出来只能是不透明的公理类型，
  没法在 Rocq 里做模式匹配。所以由一层 MoonBit 胶水 `lower`（Rocq 中是公理
  `Driver.lower`）把 AST 投影成 Rocq 定义的 `sprog`：只做语法上的一一对应，不做名字解析和类型推断，
  不支持的构造在这里报 unsupported。
- **不信任前端**：`Driver.check_source_sound` 表明，只要 `check_source` 给出 `O_Ok ge main τ`，
  就有 `program_ok ge main τ`，从而 progress/preservation 成立。这个定理不依赖 parser、
  胶水和 elaborator 的任何性质。它目前**还不能**说明 Core 程序忠实于源程序，那是 M6
  （elaboration 规范 + 证明）的任务。
- **临时 elaborator**（`Surface/Elab.v`）：名字解析、运算符按左操作数类型选原语、期望类型传播、
  泛型调用的类型实参用一阶**匹配**求出；参数类型未知的 lambda 实参推迟到其他实参之后再处理。
  需要子项类型时调用 Core 的 `infer`（在只含签名的“头部环境”里），所以类型的定义只有一份。
- **版本**：MoonBit 工具链 moonc v0.10.20（2026-11），parser 用 `moonbitlang/parser@0.4.7`。
  parser 升级后要重跑 `extract.sh`（重新生成 `Parser.v`）和 `test_frontend.sh`；
  胶水按构造子匹配 `@syntax` AST，AST 变了要相应修改 `lower.mbt`。

## 8. M2：数据类型与模式匹配

**Core**
- 类型加 `TData T ts`；全局环境改为记录 `{ ge_types; ge_funs }`。`tdef` 列出构造子及其字段类型
  （字段类型里的 `TVar i` 指类型参数）。struct 和 tuple struct 是同名的单构造子类型，
  字段名只在 Surface 层出现。
- `EConstr T c ts e`：构造子的载荷 `e` 是字段元组，所以只多一种帧 `FConstr` 和一种值
  `V_Constr`。
- `EMatch e τ bs`：带结果类型，空 `match` 的类型也唯一。模式 `pat` 是通配、变量、字面量、元组、
  构造子；变量无名，从左到右绑定，最左边的是分支体里的 de Bruijn 0（与 `ELam` 的参数顺序一致）。
  模式类型 `⊢ᵖ[ge] p : τ ⇝ Δ`，分支类型 `Γ ⊢ᵇ[ge] bs : τs ⇒ τ`（与表达式类型互递归）。
- 语义：`pmatch`/`first_match` 是函数；没有分支匹配时归约到 `SAbort`（MoonBit 的 panic），
  所以 progress 不需要穷尽性。关键引理 `pmatch_typed`：良类型值匹配成功时，绑定的值具有 `Δ` 中的类型。
- `genv_ok` 增加：类型名、构造子名不重复；构造子字段类型和函数签名良构（`ty_wf`：
  数据类型存在且参数个数正确、类型变量在范围内）。soundness 不需要良构性，它让声明有意义，
  也让 `inst` 的默认值不可达（决定 8）。
- checker：`check_pat`/`check_pats` 与 `check_branches` 用和 `check_list` 一样的嵌套递归写法，
  完备性逐一证明。

**Surface**（临时 elaborator）
- 构造子解析：`T::C` → 期望类型的构造子 → 唯一声明了 `C` 的类型；有名字段的 struct
  只能用 `{ .. }` 构造。构造子的类型实参与泛型函数一样靠匹配推出。
- 记录字面量按书写顺序求值：各字段先用 `let` 依次绑定，再构造（决定 25）。
- 字段访问 `e.f`、tuple struct 的 `e.0` 消成单分支 `match`；`let p = e; body` 消成
  `match e { p => body }`。
- 模式中 `C(..)`/`{ x, .. }` 用通配补齐，字段双关 `{ x }` 是 `{ x: x }`。
- `Option[T]`（含 `T?`）是预先声明的 `enum Option[T] { None; Some(T) }`。
