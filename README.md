# MoonRocq

用 [Rocq](https://rocq-prover.org) 写的 [MoonBit](https://www.moonbitlang.com) 类型检查器。类型系统的
**soundness** 和类型检查的 **decidability** 都有机器证明。检查器经
[rocq2mbt](https://github.com/GreckF/rocq2mbt) 抽取成 MoonBit 代码，接上官方 parser，得到可以直接运行的
`moonrocq` 命令。

```
$ moonrocq examples/ok/traits.mbt
examples/ok/traits.mbt: OK
  type Named[T0] = Named(Area[T0], (T0) -> String)
  type &Area = &Area(() -> Int, () -> String)
  fn[T0] describe(Named[T0], T0) -> String
  ...
  main : Unit
```

## 方法

```
 源码 ──官方 parser──▶ AST ──lower（MoonBit 胶水）──▶ Surface ──elaborate──▶ Core ──certified checker──▶ 结论
```

- **Core** 是一个显式类型的小内核演算。它的类型规则（`Γ ⊢[ge;Σ;Λ] e : τ`）和小步语义（带 store 的栈机器）
  都用 `Inductive` 定义。小步语义只用来证明 soundness（progress + preservation），不写解释器。
- **检查器 correct by construction**：`infer` 的返回值带着类型推导，所以它的可靠性由构造保证；完备性单独证明。
  两者合在一起，得到类型检查的可判定性。
- **Surface → Core** 的 elaboration 负责名字解析、局部类型推断、trait 的字典传递等。它的输出会交给
  certified checker 重新检查，所以 `check_source_sound` 不依赖 parser、胶水和 elaborator 的任何性质。
  trait 的实例解析（`Surface/Resolve.v`）有规范，也有证明：解析器的完备性、一致性下解析的唯一性、
  解析出的字典良类型。
- 主线上没有 `Admitted`，也没有新增公理。`scripts/check_assumptions.sh` 会检查每条主定理都是
  `Closed under the global context`。

主要定理（详见 `DESIGN.md`）：

| 定理 | 内容 |
|---|---|
| `Soundness.progress` / `preservation` / `soundness` | 良类型程序不会卡住；正常结束时，结果的类型就是程序的类型 |
| `CheckComplete.infer_complete`、`has_type_dec`、`genv_ok_dec` | 检查器完备；类型判断和全局环境的良构性可判定 |
| `Theorems.checked_program_safe` | 检查器接受的程序是安全的 |
| `Resolve.resolve_complete` / `entails_unique` / `entails_typed` | trait 实例解析：完备、唯一、良类型 |
| `Driver.check_source_sound` | 从源码到结论的整条管线 |

设计说明见 [`DESIGN.md`](DESIGN.md)。语言细节上自行做出的决定（大多用 `moon` 做实验确认过）见
[`docs/decisions.md`](docs/decisions.md)。

## 构建

需要 Linux，或 Windows 上的 WSL（Ubuntu）。MoonRocq 与 [rocq2mbt](https://github.com/GreckF/rocq2mbt)
共用后者的项目本地 opam switch（Rocq 9.4+alpha，带可扩展的 extraction API），两个仓库要**并排放置**：

```
<dir>/
  rocq2mbt/
  moonrocq/
```

（也可以设置环境变量 `ROCQ2MBT` 指向 rocq2mbt 的位置。）

1. 安装 MoonBit 工具链（`moon`，在 moonc v0.10.20 上测试过）：

   ```bash
   curl -fsSL https://cli.moonbitlang.com/install/unix.sh | bash
   ```

2. 克隆并构建 rocq2mbt（建立 opam switch，编译 MoonBit 抽取插件），细节见它的
   [README](https://github.com/GreckF/rocq2mbt) 与 `docs/USAGE.md`：

   ```bash
   git clone git@github.com:GreckF/rocq2mbt.git
   git clone git@github.com:GreckF/moonrocq.git
   cd rocq2mbt
   bash scripts/setup-opam.sh
   source scripts/env.sh
   dune build
   ```

3. 在同一个 switch 里安装 rocq-stdlib，取与 Rocq 版本同期的 commit：

   ```bash
   opam pin add rocq-stdlib \
     git+https://github.com/rocq-prover/stdlib.git#22fcaa27d17bc28ab4be728ed10a1fb73afb23ee
   ```

4. 构建并检查 MoonRocq（脚本会自己 source 环境，不需要手动进入 switch）：

   ```bash
   cd ../moonrocq
   bash scripts/build.sh              # 编译 Rocq 库，最后一行 BUILD_OK
   bash scripts/check_assumptions.sh  # 公理审计和 vm_compute 测试，最后一行 TESTS_OK
   bash scripts/extract.sh            # 抽取到 mbt/checker/moonrocq.mbt，最后一行 EXTRACT_OK
   bash scripts/test_frontend.sh      # 构建命令行工具，与 moon check 做差分测试，最后一行 FRONTEND_OK
   ```

   `test_frontend.sh` 会把 `examples/` 下的每个文件分别交给 moonrocq 和官方 `moon check`：
   `ok/` 两边都接受，`bad/` 两边都拒绝，`unsupported/` 是 MoonBit 接受、moonrocq 暂不支持的程序。

5. 使用：

   ```bash
   mbt/_build/native/release/build/moonrocq/moonrocq/cmd/main/main.exe FILE.mbt...
   ```

   程序被接受时，退出码为 0，并打印 elaborate 后各声明的 Core 签名与 `main` 的类型；
   被拒绝时，打印出错位置和原因。

用 VS Code 浏览证明：把 vsrocq 的 `vsrocq.path` 设成 switch 里的 `vsrocqtop`
（`opam install vsrocq-language-server`），先跑一次 `scripts/build.sh`。

## 目录

```
theories/
  Prelude/    Result、EqDec、Ident、可判定的 NoDup
  Core/       Syntax、Typing、Semantics、Soundness、Check、CheckComplete、Theorems
  Surface/    Syntax、Elab（临时 elaborator）、Resolve（trait 实例解析，有证明）
extraction/   Driver.v（胶水公理、check_source、抽取命令）、Parser.v（mbti2rocq 生成）
mbt/          MoonBit 工程：checker/（抽取结果 + 胶水 lower/show）、cmd/main/（命令行）
examples/     ok / bad / unsupported 三类示例
tests/        公理审计（Assumptions.v）与 vm_compute 测试（Examples.v）
scripts/      env.sh、build.sh、check_assumptions.sh、extract.sh、test_frontend.sh
docs/         decisions.md：语言细节上的决定
```

## 进度

| 里程碑 | 状态 |
|---|---|
| M1 Core λ：原始类型、函数、`let`、`if`、元组、递归泛型函数、原语 | ✅ |
| M1.5 前端：抽取到 MoonBit，接上官方 parser | ✅ |
| M2 名义 ADT 与模式匹配 | ✅ |
| M3 状态与循环 | ✅ |
| M4 错误与 effect | ✅ |
| M5 trait（字典传递、实例解析、trait object） | ✅ |
| M6 有规范、有证明的 elaborator（取代临时 elaborator），完整的类型推断 | 计划中 |
| M7 包与可见性 | 计划中 |
| M8 静态分析：穷尽性、未使用绑定等 | 计划中 |

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
- **推断能力的限制**（临时 elaborator，M6 解决）：
  - lambda 的参数类型需要注解或期望类型；
  - 带值的标签块、无条件的 `for` 循环需要期望类型；
  - lambda 不会从函数体推出 `raise`；
  - `try` 体的错误类型推断是近似的。
- **检查比 MoonBit 宽松的地方**：`match` 和 `catch` 的穷尽性还不检查（M8），没有分支匹配时运行时 `Abort`
