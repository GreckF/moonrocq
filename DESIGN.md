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
- 计算部分（检查器本身的分支、合一、查表）都是 `Type` 中的结构递归或 Equations 良基递归，
  不能在 `Prop` 证明上做消去来驱动计算。
- 可判定相等统一用 `EqDec` 类（`Prelude/EqDec.v`），抽取后只剩布尔函数。
- 标识符用 Stdlib `string`，整数用 `Z` 加按位宽回绕，不引入公理。

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
| M2 | 名义 ADT（struct/enum/tuple struct）+ 模式匹配 |
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
  Surface/    Syntax, Elab, ElabComplete……
  Analysis/   Exhaustiveness……
scripts/build.sh   在 WSL 中用 opam switch 5.5.0 执行 dune build
ref/moonbit-docs   语言文档（不入库）
```
