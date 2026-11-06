# MoonRocq

经形式化验证的第三方 [MoonBit](https://www.moonbitlang.com) 类型检查器，用 [Rocq](https://rocq-prover.org)
编写。检查器经 [rocq2mbt](https://github.com/GreckF/rocq2mbt) 抽取成可执行的 MoonBit 代码。

抽取出的 MoonBit 模块已发布到 mooncakes.io：[`GreckF/moonrocq`](https://mooncakes.io/docs/GreckF/moonrocq)。
在 MoonBit 项目中可以直接依赖它（`moon add GreckF/moonrocq`），调用 `@checker.check_source` 检查一段源码。

```
$ moonrocq examples/ok/traits.mbt
examples/ok/traits.mbt: OK
  type Named[T0] = Named(Area[T0], (T0) -> String)
  type &Area = &Area(() -> Int, () -> String)
  fn[T0] describe(Named[T0], T0) -> String
  ...
  main : Unit
```

## 主要证明性质

MoonRocq 对它所支持的 MoonBit 子集给出两方面的保证，都在 Rocq 中有完整的机器证明：

- **类型安全（soundness）**：被接受的程序在运行时不会出现类型错误。程序要么正常结束并得到正确类型的结果，
  要么以 MoonBit 允许的方式停止（例如 `panic`、数组越界），绝不会进入"不知道该怎么继续"的状态。
- **检查结果可信且完整（decidability）**：检查器接受一个程序，当且仅当这个程序按类型规则是良类型的。
  它既不会放过错误的程序，也不会拒绝正确的程序。

这些证明不依赖任何额外的公理，代码中也没有未完成的证明（`Admitted`）。

## 工作流程

```
 源码 ──官方 parser──▶ 语法树 ──转换──▶ Surface ──elaborate──▶ Core ──类型检查器──▶ 结论
```

1. **解析**：直接使用 MoonBit 官方的 parser（`moonbitlang/parser`），再由一小段 MoonBit 代码把语法树转换成
   Rocq 能处理的 Surface 语法。
2. **Elaboration**：把 Surface 程序翻译成一个更小、类型完全显式的核心语言 Core。名字解析、局部类型推断、
   trait 的展开（翻译成显式传递的"字典"）都在这一步完成。
3. **Core 类型检查**：Core 的类型检查器会重新检查 elaboration 的结果，前面所有的保证都落在这一步上。

关键在于第 3 步。前两步就算有错误，也只会让检查器拒绝本该接受的程序，或者给出不够友好的报错，
不会让一个有类型错误的程序蒙混过关。所以整个系统可以信任的部分只有 Core 和它的检查器，它们都经过了证明：

- Core 的类型规则和运行时行为（一台带内存的抽象机器，按小步执行）都在 Rocq 中精确定义。
  这台抽象机器的作用是给出"程序如何运行"的数学定义，类型安全就是针对它来证明的，并不需要真的拿它运行程序。
- 检查器每次给出"通过"的结论时，都会同时构造出一份类型推导。这份推导就是程序良类型的证明，
  所以检查器"说通过就一定对"是由构造本身保证的；"该通过的一定通过"则另外证明。
- trait 的实例解析（为每个约束选出用哪个实现）也单独做了证明：只要存在合适的实现就一定能找到；
  在实现不重叠的前提下，找到的实现是唯一的；生成的代码类型正确。

主要定理：

| 定理 | 含义 |
|---|---|
| `Soundness.progress`、`preservation`、`soundness` | 良类型的程序不会卡住；正常结束时，结果具有程序的类型 |
| `CheckComplete.infer_complete`、`has_type_dec` | 检查器完备；类型判断可判定 |
| `Theorems.checked_program_safe` | 检查器接受的程序是安全的 |
| `Resolve.resolve_complete`、`entails_unique`、`entails_typed` | trait 实例解析完备、唯一、类型正确 |
| `Driver.check_source_sound` | 从源码到结论的整条流程：结论不依赖 parser 和 elaboration 的正确性 |

更详细的设计见 [`DESIGN.md`](DESIGN.md)。MoonBit 文档没有写清楚的语言细节，我们大多用官方工具链做实验确认，
记录在 [`docs/decisions.md`](docs/decisions.md)。

## 构建

需要 Linux，或 Windows 上的 WSL（Ubuntu）。

MoonRocq 依赖 [rocq2mbt](https://github.com/GreckF/rocq2mbt)：它提供把 Rocq 代码抽取成 MoonBit 的插件，
以及一个装好了合适 Rocq 版本（9.4+alpha）的本地 opam 环境，MoonRocq 直接复用这个环境。
两个仓库需要放在同一个目录下：

```
<dir>/
  rocq2mbt/
  moonrocq/
```

如果 rocq2mbt 放在别处，可以用环境变量 `ROCQ2MBT` 指向它。

**1. 安装 MoonBit 工具链**（在 moonc v0.10.20 上测试过）：

```bash
curl -fsSL https://cli.moonbitlang.com/install/unix.sh | bash
```

**2. 获取并构建 rocq2mbt。** 这一步会建立 opam 环境并编译插件，详见 rocq2mbt 的
[README](https://github.com/GreckF/rocq2mbt) 和 `docs/USAGE.md`：

```bash
git clone git@github.com:GreckF/rocq2mbt.git
git clone git@github.com:GreckF/moonrocq.git
cd rocq2mbt
bash scripts/setup-opam.sh
source scripts/env.sh
dune build
```

**3. 在同一个 opam 环境里安装 Rocq 标准库**，版本与 Rocq 对应：

```bash
opam pin add rocq-stdlib \
  git+https://github.com/rocq-prover/stdlib.git#22fcaa27d17bc28ab4be728ed10a1fb73afb23ee
```

**4. 构建 MoonRocq。** 下面的脚本会自动进入上面的 opam 环境：

```bash
cd ../moonrocq
bash scripts/build.sh              # 编译所有证明
bash scripts/check_assumptions.sh  # 确认主定理不依赖公理，并运行 Rocq 内的测试
bash scripts/extract.sh            # 把检查器抽取成 MoonBit 代码
bash scripts/test_frontend.sh      # 构建 moonrocq 命令，并在示例程序上与 moon check 的结果对比
```

每个脚本成功时，最后一行分别是 `BUILD_OK`、`TESTS_OK`、`EXTRACT_OK`、`FRONTEND_OK`。

`test_frontend.sh` 用到的示例分成三类：`examples/ok/` 中的程序 MoonRocq 和官方工具链都应接受，
`examples/bad/` 中的都应拒绝，`examples/unsupported/` 是官方工具链接受、但 MoonRocq 目前还不支持的程序。

## 使用

```bash
mbt/_build/native/release/build/cmd/main/main.exe FILE.mbt...
```

程序通过检查时，退出码为 0，并列出翻译到 Core 之后各个声明的签名和 `main` 的类型；没有通过时，
给出出错的位置和原因。

如果想在 VS Code 里阅读证明，可以安装 vsrocq 插件和 `vsrocq-language-server`（`opam install
vsrocq-language-server`），把插件设置里的 `vsrocq.path` 指向 opam 环境中的 `vsrocqtop`，
再运行一次 `scripts/build.sh`。

## 作为 MoonBit 包使用

抽取出的检查器已发布为 mooncakes.io 上的模块 [`GreckF/moonrocq`](https://mooncakes.io/docs/GreckF/moonrocq)，
不需要安装 Rocq 就能在 MoonBit 项目里使用。

### 引入

```bash
moon add GreckF/moonrocq
```

在要使用检查器的包的 `moon.pkg` 中导入 `checker` 包：

```
import {
  "GreckF/moonrocq/checker" @checker,
}
```

### 基本用法

最简单的用法是把一段 MoonBit 源码交给 `check_source`，再用 `render_outcome` 转成可读的文字：

```moonbit
fn main {
  let src = "fn add(a : Int, b : Int) -> Int { a + b }\nfn main { ignore(add(1, 2)) }"
  let (accepted, lines) = @checker.render_outcome(@checker.check_source(src))
  println(if accepted { "accepted" } else { "rejected" })
  for l in lines {
    println("  " + l)
  }
}
```

输出：

```
accepted
  fn add(Int, Int) -> Int
  main : Unit
```

如果需要区分失败的原因，或者读取检查结果，可以直接对 `check_source` 的返回值做模式匹配：

```moonbit
fn describe(src : String) -> String {
  match @checker.check_source(src) {
    O_Ok(Mk_genv(_, fds), _, t) => "ok, main : " + @checker.show_ty(t)
    O_Type(e) => "type error: " + @checker.show_type_error(e)
    O_Elab(e) => @checker.show_elab_error(e)
    O_Unsupported(LowerUnsupported(what, p)) => @checker.show_pos(p) + ": unsupported: " + what
    O_Parse(reports) => "\{reports.length()} parse error(s)"
  }
}
```

### 主要函数

| 函数 | 说明 |
|---|---|
| `check_source(src : String) -> Outcome` | 完整流程：解析、转换、elaboration、Core 类型检查 |
| `render_outcome(o : Outcome) -> (Bool, Array[String])` | 是否通过，以及可读的结果（通过时是各声明的签名，失败时是错误信息） |
| `check_program(ge : Genv, e : Expr) -> Result0[Ty, Type_error]` | 直接检查一个 Core 程序：全局环境 `ge` 加入口表达式 `e` |
| `infer(ge, Σ, Λ, Γ, e) -> Result0[Ty, Type_error]` | Core 表达式的类型推导（`check_program` 用 `Σ = Nil`、`Λ = cc0`、`Γ = Nil` 调用它） |
| `elab_prog(sp : Sprog) -> Result0[(Genv, Expr), Elab_error]` | Surface 程序到 Core 的 elaboration |
| `check_sprog(sp : Sprog) -> Outcome` | elaboration 之后再做 Core 类型检查 |
| `lower_impls(impls) -> Result0[Sprog, Lower_error]` | 把官方 parser 的语法树转换成 Surface 程序 |
| `show_ty`、`show_type_error`、`show_elab_error`、`show_pos` | 把类型、错误、位置转成字符串 |
| `string_of_ident`、`ident_of_string` | 标识符与 MoonBit `String` 之间的转换 |

`check_program` 和 `infer` 是经过证明的部分：它们给出 `Ok` 时，程序一定良类型（证明在抽取时被擦除，
保证来自 Rocq 中的定理）。其余函数负责把源码变成 Core，即使有错误，也只会让结果偏向拒绝。

### 主要类型

检查结果：

```moonbit
pub(all) enum Outcome {
  O_Parse(Array[@basic.Report])   // 语法错误（来自官方 parser）
  O_Unsupported(Lower_error)      // 用到了暂不支持的语法
  O_Elab(Elab_error)              // 名字解析、类型推断等阶段的错误
  O_Type(Type_error)              // Core 类型检查发现的错误
  O_Ok(Genv, Expr, Ty)            // 通过：Core 全局环境、main 的 Core 表达式、main 的类型
}
```

Core 的全局环境和类型：

```moonbit
pub(all) enum Genv { Mk_genv(List[Tdef], List[Fdef]) }      // 数据类型、函数
pub(all) enum Fdef { Mk_fdef(Ident, Nat, List[Ty], Ty, Ty, Expr) }
                     // 名字、类型参数个数、参数类型、返回类型、可能 raise 的错误类型、函数体
pub(all) enum Tdef { Mk_tdef(Ident, Nat, List[Cdef], Bool) }  // 名字、类型参数个数、构造子、是否 suberror
pub(all) enum Cdef { Mk_cdef(Ident, List[Ty]) }               // 构造子名、字段类型

pub(all) enum Ty {
  TBase(Base_ty)               // Unit、Bool、各种整数、Char、Double、Float、String，以及内部的 Never
  TVar(Nat)                    // 类型参数（按位置编号）
  TTuple(List[Ty])
  TArrow(List[Ty], Ty, Ty)     // 参数、返回类型、可能 raise 的错误类型（Never 表示 noraise）
  TData(Ident, List[Ty])       // 用户定义的数据类型；trait 被翻译成同名的字典类型，&Tr 是对象类型
  TRef(Ty)                     // 可变单元（let mut、mut 字段）
  TArray(Array_kind, Ty)       // AGrow 是 Array，AFixed 是 FixedArray
  TError                       // Error
}
```

Core 表达式 `Expr` 的构造子有 `EVar`、`EGlobal`、`ELit`、`ELam`、`EApp`、`ELet`、`EIf`、`ETuple`、`EProj`、
`EPrim`（内建运算）、`EConstr`、`EMatch`、`EMem`（读写可变单元和数组）、`ELoop`、`EJump`
（`break`/`continue`/`return`）、`EAbort`、`EUp`、`ERaise`、`ETry`、`EDefer`。它们的含义见
`theories/Core/Syntax.v`。

需要注意，这些类型是从 Rocq 直接抽取出来的，保留了 Rocq 的表示方式：

- `List[A]` 是 `Nil`/`Cons` 构成的链表，`Nat` 是 `O`/`S` 构成的自然数，`Result0` 是 `Ok`/`Err`；
- 标识符 `Ident` 是逐字节表示的字符串，用 `string_of_ident` 转成 MoonBit 的 `String`；
- 变量用 de Bruijn 编号（`EVar(n)` 指向第 `n` 个外层绑定），没有名字。

例如，取出第一个函数的名字和返回类型：

```moonbit
match @checker.check_source("fn f() -> Int { 1 }") {
  O_Ok(Mk_genv(_, Cons(Mk_fdef(name, _, _, ret, _, _), _)), _, _) =>
    println(@checker.string_of_ident(name) + " returns " + @checker.show_ty(ret))
  _ => ()
}
```

## 目录

```
theories/
  Prelude/    通用工具：Result、可判定相等、标识符
  Core/       核心语言：语法、类型规则、运行语义、类型安全证明、类型检查器及其完备性
  Surface/    Surface 语法、elaboration、trait 实例解析及其证明
extraction/   连接 parser 与检查器的入口，以及抽取命令
mbt/          MoonBit 工程：抽取出的检查器、语法树转换和输出代码、命令行程序
examples/     示例程序（ok / bad / unsupported）
tests/        Rocq 内的测试，以及检查主定理所依赖公理的文件
scripts/      构建和测试脚本
docs/         语言细节上的决定
```

## 进度

| 阶段 | 内容 | 状态 |
|---|---|---|
| M1 | 核心语言：原始类型、函数、`let`、`if`、元组、递归泛型函数、内建运算 | ✅ |
| M1.5 | 抽取成 MoonBit，接上官方 parser | ✅ |
| M2 | 代数数据类型（struct、enum）与模式匹配 | ✅ |
| M3 | 可变状态、数组与循环 | ✅ |
| M4 | 错误处理与 effect | ✅ |
| M5 | trait、方法与 trait object | ✅ |
| M6 | 经过证明的 elaboration，以及更完整的类型推断 | 计划中 |
| M7 | 包与可见性 | 计划中 |
| M8 | 静态分析：模式匹配的穷尽性、未使用的绑定等 | 计划中 |

## 支持的语法

**类型**
- `Unit`、`Bool`、`Int`、`Int16`、`Int64`、`UInt`、`UInt16`、`UInt64`、`Byte`、`BigInt`、`Char`、`Double`、`Float`、`String`
- 元组、函数类型 `(A, B) -> R`，以及 `raise E`、`raise`、`noraise`、`raise?`
- `Option[T]`（`T?`）、`Result[T, E]`、`Ref[T]`、`Array[T]`、`FixedArray[T]`、`Error`
- 用户定义的 `enum`、`struct`（可以有 `mut` 字段）、tuple struct、`suberror`，可以带类型参数
- trait object `&Trait`

**顶层声明**
- `fn`：参数类型和返回类型显式写出；可以有类型参数和 trait 约束 `fn[T : A + B]`；可以带 `raise` 注解
- 方法 `fn T::m(self : T, ..)`（也可以定义在 `Array` 等内建类型上）、`fn main`
- `trait`：supertrait、默认方法（`m(Self) -> R = _`）、会 raise 的方法、没有 `self` 的静态方法
- `impl Tr for T with m(..)`、带约束的 `impl[X : B] Tr for H[X]`、默认实现 `impl Tr with m(..)`、
  不写方法的 `impl Tr for T`

**表达式**
- 字面量：整数（带或不带后缀）、字符、字符串、浮点数
- 内建类型上的算术与比较运算符、`&&`、`||`、`!`、取负
- `let`、`let mut`、解构 `let`、`if`/`else`、代码块与语句序列
- `match`：通配、变量、字面量、元组、构造子（`T::C`、`C(..)`）、记录（`{ x, y: p, .. }`）、类型注解
- 元组和 `.0`、构造子、记录字面量、字段读取和赋值（`p.x = v`、`p.x += v`）
- lambda（`fn(x) { .. }`、`(x) => ..`）、函数调用、泛型调用（类型实参自动推出）
- 赋值和复合赋值（`x = e`、`x += e`）
- 数组：字面量、`a[i]`、`a[i] = v`、`a[i] += v`、`length()`、`push()`、`Array::make`、`FixedArray::make`、`Array::new()`
- `Ref::new(v)`、`{ val: v }`、`r.val`
- `while`、C 风格 `for`、`for .. in`（整数范围 `..<`、`..<=`、`>..`、`>=..`，数组，带状态变量）、`nobreak`
- 带标签的 `break`/`continue`、带标签的块、`return`
- `raise`、`try .. catch .. noraise`、`e catch { .. }`、`try!`、`defer`、`errdefer`、`fail`、
  到 `Error` 的自动提升
- `panic()`、`abort(msg)`、`ignore(e)`、`not(e)`
- 方法调用：`x.m(..)`、`T::m(..)`、`Trait::m(..)`、`X::m()`（`X` 是带约束的类型参数）
- trait object：`e as &Trait`、按期望类型隐式转换、调用对象的方法

## 暂不支持的语法

- **迭代**：一般的 `Iter`/`Iter2`（比如遍历 `String`）、列表推导式
- **模式**：`match` guard、或模式、`as` 模式、范围模式、数组模式、`E::_`
- **调用和语法糖**：带标签参数和可选参数、管道 `|>`、级联 `..`、`is`/`guard`、字符串插值、多行字符串
- **内建 trait**：`Eq`、`Compare`、`Show`、`Hash`、`Default` 的实例；用户类型上的运算符重载；`derive`；
  `println`、`to_string` 等标准库函数
- **trait 的其他用法**：泛型 trait 方法、带约束的泛型函数作为值、impl 方法签名里的 `Self`
- **声明**：类型别名、带标签或 `mut` 的构造子字段、构造子 tag、`extenum`
- **包与模块**：`import`、可见性（`pub`/`priv`）、顶层 `let`、`test` 块、`fn init`
- **其他**：`async`/`nocancel`、`Bytes`、`Map`、`Json`、正则、`lexmatch`/`lexscan`、FFI、attributes
- **类型推断上的限制**（M6 会改进）：
  - lambda 的参数类型需要写注解，或能从上下文得知；
  - 带返回值的标签块、没有条件的 `for` 循环，需要从上下文得知结果类型；
  - lambda 不会根据函数体自动推断出 `raise`；
  - `try` 中错误类型的推断只是近似。
- **比官方工具链宽松的地方**：还不检查 `match` 和 `catch` 是否覆盖了所有情况（M8）。
  这类程序会被接受，运行到没有分支匹配的值时停止（与 `panic` 相同）。
