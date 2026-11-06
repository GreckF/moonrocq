# 语义与设计决定记录

记录文档没有说清、由我们自行决定（或有待用 `moon` 实验确认）的地方。
状态：**待确认** = 还没用 `moon` 验证；**已确认** = 实验结果与此一致。

## M1

| # | 问题 | 当前决定 | 状态 |
|---|---|---|---|
| 1 | 整数溢出 | 所有定宽整数运算按位宽回绕（`Prim.wrap`）；`BigInt` 不回绕 | 待确认 |
| 2 | 整数除法/取余 | 向零截断（`Z.quot`/`Z.rem`）；除数为 0 → `Abort`（panic） | 待确认 |
| 3 | `INT_MIN / -1` | 按回绕处理（结果为 `INT_MIN`），不 panic。wasm 后端可能会 trap，需要实验 | 待确认 |
| 4 | 无符号整数取负 | 允许，按回绕处理 | 待确认（MoonBit 是否给 `UInt` 实现 `Neg`？） |
| 5 | `()` | 在 Core 中是 `LUnit : Unit`；Core 的 `ETuple []` 是另一种类型 `TTuple []`，elaborator 不会生成它 | 设计决定 |
| 6 | 字符串表示 | UTF-16 code unit 序列（`list Z`），与文档一致 | 设计决定 |
| 7 | 浮点字面量 | 以 IEEE-754 位模式（`Z`）保存；M1 不含浮点运算 | 设计决定 |
| 8 | 全局函数类型参数越界 | `inst` 把越界的类型变量映射为 `Unit`。良构签名不会遇到这种情况；以后加类型良构性检查（M2，随类型构造子的 kind 检查一起）时，会把它变成不可达的情况 | 设计决定 |
| 9 | 计算代码中的判定过程 | 必须是透明的（`Defined`）。Stdlib 的 `ListDec.NoDup_dec` 是不透明的，已换成 `Prelude/ListDec.v` 中的版本 | 设计决定 |

## Surface 层的类型推断（用 moon 0.1.20260814 实验确认；尚未在 0.1.20261104 上复查）

| # | 现象 | 结论 | 状态 |
|---|---|---|---|
| 10 | `let id = fn(x) { x }` 后接 `id(1); id(true)` → 报错 Bool/Int 不匹配；局部 `fn id2(x) { x }` 同样报错 | **没有 let-多态**，局部绑定和局部函数都是单态的 | 已确认 |
| 11 | `let f = fn(x) { x + 1 }; f(41)` 能通过 | 局部 lambda 的参数类型可以由后续使用推出（一阶合一） | 已确认 |
| 12 | `let g = fn(x) { x }` 而 `x` 始终没有被约束 | 警告 0013 unresolved_type_variable，**默认为 Unit** | 已确认 |
| 13 | `fn(x) { x.length() }`，此时 `x` 的类型还未知 | 报错 4015 "Type _/0 has no method length"：**方法解析要求接收者的类型在调用点已知**，推断与检查的顺序会影响结果 | 已确认 |
| 14 | `let r = []; r.length(); r.push("a")` 能通过 | 只要类型构造子已知（`Array[_]`）就能解析方法，元素类型可以稍后确定 | 已确认 |
| 15 | `let x = 1; let y : Int64 = x` → 报错 Int/Int64 | 无期望类型时，整数字面量**当场默认为 Int**，不会推迟到后面再决定 | 已确认 |

## M1.5 前端原型（临时 elaborator 的行为）

| # | 问题 | 当前决定 | 状态 |
|---|---|---|---|
| 16 | 不带后缀的整数字面量 | 期望类型是整数类型时取该类型，否则为 `Int`；超出范围报错（`int_in_range`）。期望类型为 `Double` 等情况暂不支持 | 部分确认（与 #15 一致） |
| 17 | 负字面量 | parser 已把 `-3L` 折叠成字面量；elaborator 也把 `-字面量` 折叠，因此 `-2147483648 : Int` 合法 | 设计决定 |
| 18 | 泛型调用的类型实参 | 对已知的实参类型做一阶匹配（期望的返回类型也参与），求不出就报 `cannot infer`，不像 MoonBit 那样默认为 `Unit`（#12） | 设计决定（比 MoonBit 严格） |
| 19 | lambda 参数类型 | 来自注解或期望类型；泛型调用中参数类型未知的 lambda 实参推迟到其他实参之后处理。MoonBit 可以由后续使用推出（#11），这要等 M6 的合一 | 已知限制 |
| 20 | 运算符 | 按左操作数的类型选原语；左边是不带后缀的整数字面量而右边不是时，先看右边。`&&`/`||` 消成 `if` | 设计决定 |
| 21 | 标识符的表示 | Rocq `string` 存 UTF-8 字节 | 设计决定 |
| 22 | 实参个数错误 | Core checker 先比较参数与实参的总个数，再逐个检查，报错给出总数 | 设计决定 |
| 23 | 内建函数 | 只认 `not`、`ignore`、`panic`、`abort`（#45；且未被同名定义遮蔽时）；`println` 等要等 M4/M5 的 effect 与 trait | 已知限制 |

## M2 数据类型与模式匹配

| # | 问题 | 当前决定 | 状态 |
|---|---|---|---|
| 24 | `match` 没有分支匹配 | 归约到 `Abort`（panic）；不完全匹配不是类型错误，穷尽性检查放到 M8 | 与文档一致（moon 对不完全匹配给 warning） |
| 25 | 记录字面量的求值顺序 | 按**书写顺序**求值（elaborator 先按书写顺序 `let` 绑定，再按声明顺序构造） | 已确认（moon，2026-11：`{ b: .., a: .. }` 先求 `b`） |
| 26 | 构造子名解析 | `T::C` 优先，其次期望类型，再其次全局唯一；有歧义时报错要求写 `T::C` | 待确认（MoonBit 的完整规则还涉及类型推断） |
| 27 | 有名字段的 struct 能否当构造子调用 | 不能，只能用 `{ .. }` | 设计决定 |
| 28 | `Option` | 预先声明为 `enum Option[T] { None; Some(T) }`，`T?` 是它的简写；用户再定义 `Option` 会报重复类型 | 设计决定 |
| 29 | 记录模式缺字段 | 有 `..` 时缺的字段是通配；没有 `..` 时报 missing field | 待确认（MoonBit 可能只给 warning） |
| 30 | 类型良构性 | 函数签名和构造子字段的类型必须良构（`ty_wf`），表达式内部的注解暂不检查（不影响 soundness） | 设计决定 |
| 31 | 暂不支持 | 带标签的构造子字段、`match` guard、或模式、`as` 模式、范围/数组模式、ADT 上的 `==`（需要 M5 的 `Eq`）、类型别名、`suberror`（M4）、`derive` 只被忽略 | 已知限制 |

## M3 状态与循环

| # | 问题 | 当前决定 | 状态 |
|---|---|---|---|
| 32 | store 的表示 | store 是对象列表（单元 `OCell v` 或数组 `OArr vs`），位置 `ELoc l` 是只在运行时出现的值；store typing `Σ` 每个位置记 `LCell τ`/`LArr k τ`。类型判断带 `Σ` 参数，程序本身在 `Σ = []` 下检查 | 设计决定 |
| 33 | `let mut` | Core 中是一个单元（`TRef τ`）：`let mut x = e` 是 `let x = ref(e)`，读写是 `MGet`/`MSet`。被闭包捕获时共享同一个单元，与 MoonBit 语义一致 | 设计决定 |
| 34 | `mut` 字段 | 字段在 Core 中的类型是 `TRef τ`，构造时分配单元（按书写顺序），读取用模式 `PRef`，写入用 `MSet`；结构体值复制时共享单元，所以别名可见修改 | 设计决定（`physical_equal` 等身份操作以后再说） |
| 35 | 数组 | `Array[T]`（可增长）与 `FixedArray[T]` 是 `TArray AGrow/AFixed`；字面量无期望类型时是 `Array`；支持下标读写、`length`、`push`（仅 `Array`）、`make`、`new`。下标越界、`make` 长度为负都归约到 `Abort` | 已确认（moon：`make(-1, ..)` panic） |
| 36 | 循环的 Core 表示 | 只有一种 `ELoop init ps τ body`（参数元组 + 结果类型）和 `EJump CBreak/CCont k e τ`（de Bruijn 编号的目标循环，`τ` 是跳转表达式自身的类型）。函数体包一层循环作为 `return` 的目标；λ 体的标签上下文为空，跳转不跨函数 | 设计决定 |
| 37 | `while c { b } nobreak { n }` | `loop () { if c { b; continue () } else { n } }`；没有 `nobreak` 时结果是 `Unit` | 设计决定 |
| 38 | `for x = i; c; x = u { b } nobreak { n }` | 外层循环带循环变量，体是 `if c { (内层块 b); continue (u) } else { n }`。不带参数的 `continue` 跳出内层块（随后执行更新），`continue a, ..` 直接重入外层循环（跳过更新）；更新子句**同时**赋值，没写的变量保持原值 | 已确认（moon：`i = i + 1, j = i` 中 `j` 取旧的 `i`） |
| 39 | 标签与 `break`/`continue` 的目标 | 不带标签的 `break`/`continue` 找最近的循环，不能穿过带标签的块；`continue` 不能指向块；条件、更新子句和 `nobreak` 里的跳转指向外层循环 | 已确认（moon：`nobreak` 中的 `break` 退出外层循环） |
| 40 | 跳转与无期望类型 | 带值的标签块、无条件的 `for` 循环需要期望类型才能确定结果类型（否则是 `Unit`）；分支/`match` 中跳走的分支取其他分支的类型 | 已知限制（临时 elaborator，M6） |
| 41 | 复合赋值的求值顺序 | `a[i] += v`：先 `a`、`i`（各求一次），再读 `a[i]`，再求 `v`；`e.f += v` 同理 | 已确认 `i` 先于 `v`（moon）；读与 `v` 的先后不可观察 |
| 42 | 暂不支持 | 数组切片与展开、数组模式、透明标签 `l~~:`、其他内建方法 | 已知限制（M6） |
| 43 | `for .. in` | 支持整数范围 `a..<b`、`a..<=b`、`a>..b`（从 `a - 1` 降到 `b`）、`a>=..b` 和数组（一个绑定是元素，两个绑定是下标与元素；绑定可以是模式），以及状态变量 `; s = e` 与更新子句 `; s = u`。范围的两端与数组各求值一次（先 `a` 后 `b`），整数类型由起点决定（`0..<n` 而 `n : Int64` 是类型错误）；数组长度在开始时读一次，元素每轮实时读取。不带参数的 `continue` 应用更新子句，带参数的 `continue` 直接给出下一状态。包含端点的范围到达 `Int` 边界时不溢出 | 已确认（moon，2026-11：各项均做了实验） |
| 44 | `Ref[T]` | 预先声明为 `struct Ref[T] { mut val : T }`，`Ref::new(v)` 等于 `{ val: v }`；用户不能再定义 `Ref` | 设计决定（MoonBit 中 `Ref` 是 core 库的类型，可以被遮蔽） |
| 45 | `panic()`、`abort(msg)` | Core 表达式 `EAbort τ`：任意类型（标注 `τ` 保证类型唯一），一步归约到 `SAbort`。它不产生值，所以任意类型不破坏 soundness（`SAbort` 是终止状态）。elaborator 取期望类型（否则 `Unit`），`abort` 先求值并检查 `String` 参数；分支里的 `panic`/`abort` 像跳转一样取其他分支的类型 | 设计决定 |

## M4 错误与 effect

| # | 问题 | 当前决定 | 状态 |
|---|---|---|---|
| 46 | effect 的表示 | 函数类型 `TArrow ps r ε` 带一个"可能 raise 的错误类型" ε：`Never`（内部类型，没有值）表示 `noraise`，`Error` 或某个 suberror 表示 `raise E`，类型变量表示 `raise?`（`raise?` 签名多一个隐藏的类型参数，错误多态因此就是普通的 rank-1 多态） | 设计决定 |
| 47 | effect 之间没有子类型 | `noraise` 函数不能用在要求 `raise` 的位置，`raise E1` 的函数里不能调用 `raise E2` 或 `raise Error` 的函数；调用与 `raise` 只要求 `ε = Never` 或 `ε =` 当前允许的错误类型（`eff_le`） | 已确认（moon，2026-11：三种情况都报错） |
| 48 | 提升到 `Error` | Core 中显式：`EUp T e : Error`（值 `EUp T v`），匹配 `Error` 用模式 `PUp T p`。elaborator 在以下位置自动插入：期望类型是 `Error` 的 `let`/注解/实参/`return`、`raise` 一个 suberror 值而当前允许 `Error`、在允许 `Error` 处调用 `raise E` 的函数（用 `try .. catch { e => raise EUp(e) }` 包起来） | 设计决定（MoonBit 是隐式的） |
| 49 | `fn main` | 不能 raise：程序在 `cc0`（允许的错误类型为 `Never`）下检查；所以未捕获的错误不会到达空栈 | 已确认（moon：main 中调用 raise 函数报错） |
| 50 | lambda 的 effect | 来自注解，否则来自期望的函数类型，否则 `noraise` | 已确认（moon：没有注解、没有期望类型的 lambda 不会推出 `raise`） |
| 51 | `try` 体的错误类型 | `catch` 的构造子模式都属于同一个错误类型 E 时取 E，属于不同类型时取 `Error`；模式不提供信息时，取唯一能让 `try` 体通过检查的错误类型，否则 `Error` | 设计决定（近似 MoonBit 的"多种错误时为 Error"，已确认 moon 对 `e => Err(e)` 给出精确类型） |
| 52 | `catch` 不穷尽 | 没有分支匹配时 `Abort`；moon 把不穷尽的 `catch` 当作错误，穷尽性检查放到 M8 | 已知差异（moonrocq 更宽松） |
| 53 | `defer`/`errdefer` | 帧 `FDefer` 在体正常结束、跳转（仅 `defer`）或 raise 时先运行清理代码，再继续原来的出口（帧 `FAfter` 记住它）；清理代码看不到外围循环（不能 `break`/`continue`/`return`），它 raise 的错误取代原来的结果；清理表达式必须是 `Unit`。多个 `defer` 逆序执行 | 已确认（moon：清理错误取代原错误、逆序、`errdefer` 只在 raise 时运行、`defer 1` 报错） |
| 54 | 预先声明的类型 | `Result[T, E]`（`Ok`/`Err`）、`suberror Failure { Failure(String) }`；`fail(msg)` 即 `raise Failure(msg)`（不带位置信息） | 设计决定 |
| 55 | `try!` | `try e catch { _ => panic() }`：任何错误都 `Abort` | 已确认（moon：`try!` 在错误时 panic） |
| 56 | 暂不支持 | `catch` 中的 guard、`E::_` 通配构造子模式、`as` 模式、async/`nocancel`、带标签的错误构造子字段、lambda 中的 `raise?` | 已知限制（M6） |

## M5 trait

| # | 问题 | 当前决定 | 状态 |
|---|---|---|---|
| 57 | trait 的编码 | 字典传递，Core 不变：trait `Tr` 是数据类型 `Tr[Self]`（一个构造子，先放 supertrait 字典，再放方法）；`impl` 是全局函数 `inst$Tr$H`，由它的约束的字典构造字典；约束 `X : Tr` 是字典参数（排在普通参数之前）；supertrait 字典在函数体外用 `let` 投影出来 | 设计决定（用户确认） |
| 58 | 实例解析 | `Surface/Resolve.v`：声明式规则 `entails`（假设，或头部匹配的 impl）、certified 的 `resolve_dict`（先假设，再按顺序试 impl，可回溯）及其完备性、`entails_dec`；生成的字典在 Core 中良类型（`entails_typed`） | 设计决定 |
| 59 | 一致性 | 同一 trait、同一类型头部最多一个 impl（`coherent`，可判定）；impl 头部是类型构造子作用于按顺序排列的类型参数，所以 `impl[T] S for Array[T]` 与 `impl S for Array[Int]` 重叠；在一致性下解析唯一（`entails_unique`） | 已确认（moon：重复和特化的 impl 都报错） |
| 60 | 方法调用 `x.m(..)` | 先找类型自己的方法 `fn T::m`；再找 trait object 的方法；再在类型参数（约束及其 supertrait）或程序自己的类型上找 trait 方法；对内建类型不能用 `.` 调用 trait 方法 | 已确认（moon：`1.f()` 报 "Type Int has no method f"；类型自己的方法优先于 trait 方法） |
| 61 | `T::m(..)` / `Tr::m(..)` | 类型的方法、trait 方法（`Self` 来自第一个参数，或来自期望的返回类型）、带约束的类型参数 `X::m(..)` | 已确认（moon：`Z::zero()` 由期望类型决定 `Self`） |
| 62 | 默认方法 | 声明为 `m(Self) -> R = _`，实现为 `impl Tr with m(self) { .. }`（全局函数 `default$Tr$m`，以 `Tr[Self]` 字典为参数）；缺少方法且无默认实现时报错；`impl Tr for T`（无方法）全部使用默认实现 | 已确认（moon：缺方法报错，默认实现可用） |
| 63 | trait object `&Tr` | 只对 object-safe 的 trait（它和所有 supertrait 的方法都以 `Self` 为第一个参数、别处不出现 `Self`）生成对象类型 `&Tr`：闭包记录（含 supertrait 的方法），`self` 已经部分应用；`e as &Tr` 或期望类型为 `&Tr` 时隐式转换；`&Tr` 自动实现 `Tr` 及其 supertrait | 已确认（moon：隐式转换、`&Tr` 满足 `Tr` 约束、非 object-safe 报错） |
| 64 | 暂不支持 | 内建 trait（`Eq`/`Compare`/`Show`/`Hash`/`Default`）的实例与运算符重载、`derive`、泛型 trait 方法、impl 方法签名中的 `Self`、带约束的泛型函数作为值、impl 头部的类型参数不按顺序、`impl` 的可见性与孤儿规则（M7） | 已知限制 |
