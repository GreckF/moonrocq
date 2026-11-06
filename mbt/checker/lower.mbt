// Glue between the official MoonBit parser and the extracted checker.
//
// `lower_impls` implements the Rocq axiom `Driver.lower`: a purely
// syntactic projection of the parser AST (@syntax) onto the Surface AST
// (`Sprog`, extracted from theories/Surface/Syntax.v).  It does no name
// resolution and no typing -- that is the job of the (Rocq) elaborator and
// checker.  Constructs outside the supported fragment are reported as
// `Lower_error::LowerUnsupported`.
//
// Nothing here is trusted: the checker's guarantee (Driver.check_source_sound)
// does not depend on this file.

///|
priv suberror Unsupported {
  Unsupported(String, @basic.Location)
}

///|
fn unsupported(what : String, loc : @basic.Location) -> Unit raise Unsupported {
  raise Unsupported(what, loc)
}

// ---------------------------------------------------------------------------
// Conversions to the extracted Rocq types

///|
fn positive_of_bigint(n : BigInt) -> Positive {
  // n >= 1
  if n == 1N {
    Positive::XH
  } else if n % 2N == 0N {
    Positive::XO(positive_of_bigint(n / 2N))
  } else {
    Positive::XI(positive_of_bigint(n / 2N))
  }
}

///|
fn z_of_bigint(n : BigInt) -> Z {
  if n == 0N {
    Z::Z0
  } else if n > 0N {
    Z::Zpos(positive_of_bigint(n))
  } else {
    Z::Zneg(positive_of_bigint(-n))
  }
}

///|
fn z_of_int(n : Int) -> Z {
  z_of_bigint(BigInt::from_int(n))
}

///|
fn n_of_int(n : Int) -> N {
  if n <= 0 {
    N::N0
  } else {
    N::Npos(positive_of_bigint(BigInt::from_int(n)))
  }
}

///|
fn nat_of_int(n : Int) -> Nat {
  let mut r = Nat::O
  for _ in 0..<n {
    r = Nat::S(r)
  }
  r
}

///|
fn[A] list_of_array(xs : Array[A]) -> List[A] {
  let mut r = List::Nil
  for i = xs.length() - 1; i >= 0; i = i - 1 {
    r = List::Cons(xs[i], r)
  }
  r
}

///|
fn ascii_of_byte(b : Int) -> Ascii {
  Ascii::Ascii0(
    (b & 1) != 0,
    (b & 2) != 0,
    (b & 4) != 0,
    (b & 8) != 0,
    (b & 16) != 0,
    (b & 32) != 0,
    (b & 64) != 0,
    (b & 128) != 0,
  )
}

///|
/// UTF-8 encoding of a code point.
fn utf8_bytes(c : Int, out : Array[Int]) -> Unit {
  if c < 0x80 {
    out.push(c)
  } else if c < 0x800 {
    out.push(0xC0 | (c >> 6))
    out.push(0x80 | (c & 0x3F))
  } else if c < 0x10000 {
    out.push(0xE0 | (c >> 12))
    out.push(0x80 | ((c >> 6) & 0x3F))
    out.push(0x80 | (c & 0x3F))
  } else {
    out.push(0xF0 | (c >> 18))
    out.push(0x80 | ((c >> 12) & 0x3F))
    out.push(0x80 | ((c >> 6) & 0x3F))
    out.push(0x80 | (c & 0x3F))
  }
}

///|
/// Identifiers are Rocq `string`s, i.e. byte strings: we use UTF-8.
pub fn ident_of_string(s : String) -> String0 {
  let bytes = []
  for c in s {
    utf8_bytes(c.to_int(), bytes)
  }
  let mut r = String0::EmptyString
  for i = bytes.length() - 1; i >= 0; i = i - 1 {
    r = String0::String1(ascii_of_byte(bytes[i]), r)
  }
  r
}

///|
fn pos_of_loc(loc : @basic.Location) -> Pos {
  Pos::Mk_pos(n_of_int(loc.start.lnum), n_of_int(loc.start.cnum - loc.start.bol + 1))
}

// ---------------------------------------------------------------------------
// Literals

///|
fn digit_value(c : Char) -> Int {
  match c {
    '0'..='9' => c.to_int() - '0'.to_int()
    'a'..='f' => c.to_int() - 'a'.to_int() + 10
    'A'..='F' => c.to_int() - 'A'.to_int() + 10
    _ => 99
  }
}

///|
/// Integer literal text as produced by the parser: optional sign, optional
/// `0x`/`0o`/`0b` prefix, digits with `_` separators, optional suffix.
fn parse_int_literal(
  text : String,
  loc : @basic.Location,
) -> BigInt raise Unsupported {
  let chars = text.to_array()
  let mut i = 0
  let mut neg = false
  if i < chars.length() && (chars[i] == '-' || chars[i] == '+') {
    neg = chars[i] == '-'
    i = i + 1
  }
  let mut base = 10
  if i + 1 < chars.length() && chars[i] == '0' {
    match chars[i + 1] {
      'x' | 'X' => {
        base = 16
        i = i + 2
      }
      'o' | 'O' => {
        base = 8
        i = i + 2
      }
      'b' | 'B' => {
        base = 2
        i = i + 2
      }
      _ => ()
    }
  }
  let mut n = 0N
  let mut digits = 0
  while i < chars.length() {
    let c = chars[i]
    if c == '_' {
      i = i + 1
      continue
    }
    let d = digit_value(c)
    if d >= base {
      // a type suffix (L, U, UL, N): the constant's kind already says it
      break
    }
    n = n * BigInt::from_int(base) + BigInt::from_int(d)
    digits = digits + 1
    i = i + 1
  }
  if digits == 0 {
    unsupported("integer literal `\{text}`", loc)
  }
  if neg {
    -n
  } else {
    n
  }
}

///|
/// Decode the escapes of a string/char literal body into code points.
fn unescape(text : String, loc : @basic.Location) -> Array[Int] raise Unsupported {
  let cs = text.to_array()
  let out = []
  let mut i = 0
  while i < cs.length() {
    let c = cs[i]
    if c != '\\' {
      out.push(c.to_int())
      i = i + 1
      continue
    }
    if i + 1 >= cs.length() {
      unsupported("escape sequence", loc)
    }
    let e = cs[i + 1]
    i = i + 2
    match e {
      'n' => out.push(10)
      't' => out.push(9)
      'r' => out.push(13)
      'b' => out.push(8)
      '\\' => out.push(92)
      '"' => out.push(34)
      '\'' => out.push(39)
      ' ' => out.push(32)
      'x' => {
        if i + 1 >= cs.length() {
          unsupported("escape sequence", loc)
        }
        out.push(digit_value(cs[i]) * 16 + digit_value(cs[i + 1]))
        i = i + 2
      }
      'o' => {
        if i + 2 >= cs.length() {
          unsupported("escape sequence", loc)
        }
        out.push(
          digit_value(cs[i]) * 64 + digit_value(cs[i + 1]) * 8 + digit_value(cs[i + 2]),
        )
        i = i + 3
      }
      'u' => {
        let mut v = 0
        if i < cs.length() && cs[i] == '{' {
          i = i + 1
          while i < cs.length() && cs[i] != '}' {
            v = v * 16 + digit_value(cs[i])
            i = i + 1
          }
          i = i + 1
        } else {
          for _ in 0..<4 {
            if i < cs.length() {
              v = v * 16 + digit_value(cs[i])
              i = i + 1
            }
          }
        }
        out.push(v)
      }
      _ => unsupported("escape sequence `\\\{e}`", loc)
    }
  }
  out
}

///|
/// MoonBit strings are UTF-16: split code points above the BMP.
fn utf16_units(cps : Array[Int]) -> List[Z] {
  let units = []
  for c in cps {
    if c >= 0x10000 {
      let v = c - 0x10000
      units.push(z_of_int(0xD800 + (v >> 10)))
      units.push(z_of_int(0xDC00 + (v & 0x3FF)))
    } else {
      units.push(z_of_int(c))
    }
  }
  list_of_array(units)
}

///|
fn parse_double_literal(
  text : String,
  loc : @basic.Location,
) -> Double raise Unsupported {
  let clean = text.replace_all(old="_", new="")
  @string.parse_double(clean) catch {
    _ => {
      unsupported("floating point literal `\{text}`", loc)
      0.0
    }
  }
}

///|
fn lower_constant(
  c : @syntax.Constant,
  loc : @basic.Location,
) -> Slit raise Unsupported {
  match c {
    Bool(b) => Slit::SLBool(b)
    Int(s) => Slit::SLInt(None, z_of_bigint(parse_int_literal(s, loc)))
    Int64(s) =>
      Slit::SLInt(Some(Int_kind::I64), z_of_bigint(parse_int_literal(s, loc)))
    UInt(s) =>
      Slit::SLInt(Some(Int_kind::U32), z_of_bigint(parse_int_literal(s, loc)))
    UInt64(s) =>
      Slit::SLInt(Some(Int_kind::U64), z_of_bigint(parse_int_literal(s, loc)))
    BigInt(s) =>
      Slit::SLInt(Some(Int_kind::IBigInt), z_of_bigint(parse_int_literal(s, loc)))
    Byte(s) => {
      let cps = unescape(s, loc)
      if cps.length() != 1 {
        unsupported("byte literal", loc)
      }
      Slit::SLInt(Some(Int_kind::IByte), z_of_int(cps[0]))
    }
    Char(s) => {
      let cps = unescape(s, loc)
      if cps.length() != 1 {
        unsupported("character literal", loc)
      }
      Slit::SLChar(z_of_int(cps[0]))
    }
    String(s) => Slit::SLString(utf16_units(unescape(s, loc)))
    Double(s) => {
      let d = parse_double_literal(s, loc)
      Slit::SLDouble(z_of_bigint(BigInt::from_uint64(d.reinterpret_as_uint64())))
    }
    Float(s) => {
      let d = parse_double_literal(s, loc)
      let f = Float::from_double(d)
      Slit::SLFloat(z_of_bigint(BigInt::from_uint(f.reinterpret_as_uint())))
    }
    Bytes(_) => {
      unsupported("Bytes literal", loc)
      Slit::SLUnit
    }
    Regex(_) => {
      unsupported("regex literal", loc)
      Slit::SLUnit
    }
  }
}

// ---------------------------------------------------------------------------
// Types

///|
fn lower_type(t : @syntax.Type) -> Sty raise Unsupported {
  match t {
    Name(constr_id~, tys~, loc~) =>
      match constr_id.id {
        Ident(name~) => Sty::SName(pos_of_loc(loc), ident_of_string(name), lower_types(tys))
        Dot(pkg~, id~) => {
          unsupported("qualified type @\{pkg}.\{id}", loc)
          Sty::STuple(pos_of_loc(loc), List::Nil)
        }
      }
    Tuple(tys~, loc~) => Sty::STuple(pos_of_loc(loc), lower_types(tys))
    Arrow(args~, res~, err~, is_async~, loc~) => {
      match err {
        NoErrorType => ()
        _ => unsupported("function type with an error type", loc)
      }
      if is_async is Some(_) {
        unsupported("async function type", loc)
      }
      Sty::SArrow(pos_of_loc(loc), lower_types(args), lower_type(res))
    }
    Option(loc~, ..) => {
      unsupported("option type", loc)
      Sty::STuple(pos_of_loc(loc), List::Nil)
    }
    Any(loc~) => {
      unsupported("type placeholder `_`", loc)
      Sty::STuple(pos_of_loc(loc), List::Nil)
    }
    Object(c) => {
      unsupported("trait object type", c.loc)
      Sty::STuple(pos_of_loc(c.loc), List::Nil)
    }
  }
}

///|
fn lower_types(ts : @list.List[@syntax.Type]) -> List[Sty] raise Unsupported {
  let out = []
  for t in ts {
    out.push(lower_type(t))
  }
  list_of_array(out)
}

// ---------------------------------------------------------------------------
// Expressions

///|
fn var_name(v : @syntax.Var) -> String raise Unsupported {
  match v.name {
    Ident(name~) => name
    Dot(pkg~, id~) => {
      unsupported("qualified name @\{pkg}.\{id}", v.loc)
      id
    }
  }
}

///|
fn lower_exprs(es : @list.List[@syntax.Expr]) -> List[Sexpr] raise Unsupported {
  let out = []
  for e in es {
    out.push(lower_expr(e))
  }
  list_of_array(out)
}

///|
fn lower_lambda(f : @syntax.Func, loc : @basic.Location) -> Sexpr raise Unsupported {
  match f.error_type {
    NoErrorType => ()
    _ => unsupported("function with an error type", loc)
  }
  if f.is_async is Some(_) {
    unsupported("async function", loc)
  }
  let ps = []
  for p in f.parameters {
    match p {
      Positional(binder~, ty~) => {
        let ann = match ty {
          Some(t) => Some(lower_type(t))
          None => None
        }
        ps.push((ident_of_string(binder.name), ann))
      }
      _ => unsupported("non-positional lambda parameter", loc)
    }
  }
  let ret = match f.return_type {
    Some(t) => Some(lower_type(t))
    None => None
  }
  Sexpr::SLam(pos_of_loc(loc), list_of_array(ps), ret, lower_expr(f.body))
}

///|
fn lower_expr(e : @syntax.Expr) -> Sexpr raise Unsupported {
  match e {
    Ident(id~, loc~) => Sexpr::SVar(pos_of_loc(loc), ident_of_string(var_name(id)))
    Constant(c~, loc~) => Sexpr::SLit(pos_of_loc(loc), lower_constant(c, loc))
    Unit(loc~, ..) => Sexpr::SLit(pos_of_loc(loc), Slit::SLUnit)
    Apply(func~, args~, loc~) => {
      let out = []
      for a in args {
        match a.kind {
          Positional => out.push(lower_expr(a.value))
          _ => unsupported("labelled argument", loc)
        }
      }
      Sexpr::SApp(pos_of_loc(loc), lower_expr(func), list_of_array(out))
    }
    Infix(op~, lhs~, rhs~, loc~) =>
      Sexpr::SInfix(
        pos_of_loc(loc),
        ident_of_string(var_name(op)),
        lower_expr(lhs),
        lower_expr(rhs),
      )
    Unary(op~, expr~, loc~) =>
      Sexpr::SUnary(pos_of_loc(loc), ident_of_string(var_name(op)), lower_expr(expr))
    Let(pattern~, expr~, body~, loc~) => {
      let (x, ann) = lower_let_pattern(pattern, loc)
      Sexpr::SLet(pos_of_loc(loc), x, ann, lower_expr(expr), lower_expr(body))
    }
    Sequence(exprs~, last_expr~, loc~) => {
      let es = exprs.to_array()
      let mut r = lower_expr(last_expr)
      for i = es.length() - 1; i >= 0; i = i - 1 {
        r = Sexpr::SLet(pos_of_loc(loc), None, None, lower_expr(es[i]), r)
      }
      r
    }
    If(cond~, ifso~, ifnot~, loc~) => {
      let e = match ifnot {
        Some(e) => Some(lower_expr(e))
        None => None
      }
      Sexpr::SIf(pos_of_loc(loc), lower_expr(cond), lower_expr(ifso), e)
    }
    Tuple(exprs~, loc~) => Sexpr::STup(pos_of_loc(loc), lower_exprs(exprs))
    Field(record~, accessor~, loc~) =>
      match accessor {
        Index(tuple_index~, ..) =>
          Sexpr::SProj(pos_of_loc(loc), lower_expr(record), nat_of_int(tuple_index))
        _ => {
          unsupported("field access", loc)
          Sexpr::SLit(pos_of_loc(loc), Slit::SLUnit)
        }
      }
    Function(func~, loc~) => lower_lambda(func, loc)
    Constraint(expr~, ty~, loc~) =>
      Sexpr::SAnnot(pos_of_loc(loc), lower_expr(expr), lower_type(ty))
    Group(expr~, ..) => lower_expr(expr)
    _ => {
      unsupported(expr_kind(e), expr_loc(e))
      Sexpr::SLit(pos_of_loc(expr_loc(e)), Slit::SLUnit)
    }
  }
}

///|
fn lower_let_pattern(
  p : @syntax.Pattern,
  loc : @basic.Location,
) -> (Option[String0], Option[Sty]) raise Unsupported {
  match p {
    Var(b) => (Some(ident_of_string(b.name)), None)
    Any(..) => (None, None)
    Constraint(pat~, ty~, ..) => {
      let x = match pat {
        Var(b) => Some(ident_of_string(b.name))
        Any(..) => None
        _ => {
          unsupported("let pattern", loc)
          None
        }
      }
      (x, Some(lower_type(ty)))
    }
    _ => {
      unsupported("let with a destructuring pattern", loc)
      (None, None)
    }
  }
}

///|
fn expr_kind(e : @syntax.Expr) -> String {
  let s = @debug.to_string(e)
  let mut n = 0
  for c in s {
    if c == '(' || c == ' ' || c == '\n' {
      break
    }
    n = n + 1
  }
  "expression `" + s.view(end_offset=n).to_owned() + "`"
}

///|
fn expr_loc(e : @syntax.Expr) -> @basic.Location {
  match e {
    Apply(loc~, ..)
    | Infix(loc~, ..)
    | Unary(loc~, ..)
    | Array(loc~, ..)
    | ArraySpread(loc~, ..)
    | ListComprehension(loc~, ..)
    | ArrayGet(loc~, ..)
    | ArrayGetSlice(loc~, ..)
    | ArraySet(loc~, ..)
    | ArrayAugmentedSet(loc~, ..)
    | Constant(loc~, ..)
    | MultilineString(loc~, ..)
    | Interp(loc~, ..)
    | BytesInterp(loc~, ..)
    | Constraint(loc~, ..)
    | Constr(loc~, ..)
    | LabelledBlock(loc~, ..)
    | While(loc~, ..)
    | Function(loc~, ..)
    | Ident(loc~, ..)
    | If(loc~, ..)
    | Guard(loc~, ..)
    | Is(loc~, ..)
    | RegexMatch(loc~, ..)
    | Defer(loc~, ..)
    | LetFn(loc~, ..)
    | LetAnd(loc~, ..)
    | Let(loc~, ..)
    | Sequence(loc~, ..)
    | Tuple(loc~, ..)
    | Record(loc~, ..)
    | RecordUpdate(loc~, ..)
    | Field(loc~, ..)
    | Method(loc~, ..)
    | DotApply(loc~, ..)
    | As(loc~, ..)
    | Mutate(loc~, ..)
    | Match(loc~, ..)
    | LexMatch(loc~, ..)
    | LexScan(loc~, ..)
    | LetMut(loc~, ..)
    | Pipe(loc~, ..)
    | RevPipe(loc~, ..)
    | Assign(loc~, ..)
    | Hole(loc~, ..)
    | Return(loc~, ..)
    | Raise(loc~, ..)
    | Quantifier(loc~, ..)
    | Implies(loc~, ..)
    | ProofAssert(loc~, ..)
    | ProofLet(loc~, ..)
    | Unit(loc~, ..)
    | Break(loc~, ..)
    | Continue(loc~, ..)
    | For(loc~, ..)
    | ForEach(loc~, ..)
    | Try(loc~, ..)
    | TryOperator(loc~, ..)
    | Map(loc~, ..)
    | Group(loc~, ..)
    | TemplateWriting(loc~, ..) => loc
    StaticAssert(body~, ..) => expr_loc(body)
  }
}

// ---------------------------------------------------------------------------
// Top level

///|
fn lower_fun(
  d : @syntax.FunDecl,
  body : @syntax.Expr,
  loc : @basic.Location,
) -> Sfun raise Unsupported {
  if d.type_name is Some(_) {
    unsupported("method definition", loc)
  }
  if d.is_async is Some(_) {
    unsupported("async function", loc)
  }
  match d.error_type {
    NoErrorType => ()
    _ => unsupported("function with an error type", loc)
  }
  let tps = []
  for q in d.quantifiers {
    if !q.constraints.is_empty() {
      unsupported("trait bound on type parameter \{q.name}", q.name_loc)
    }
    tps.push(ident_of_string(q.name))
  }
  let ps = []
  match d.decl_params {
    Some(params) =>
      for p in params {
        match p {
          Positional(binder~, ty~) =>
            match ty {
              Some(t) => ps.push((ident_of_string(binder.name), lower_type(t)))
              None =>
                unsupported(
                  "parameter `\{binder.name}` without type annotation",
                  binder.loc,
                )
            }
          _ => unsupported("non-positional parameter", loc)
        }
      }
    None => ()
  }
  let ret = match d.return_type {
    Some(t) => Some(lower_type(t))
    None => None
  }
  Sfun::Mk_sfun(
    pos_of_loc(loc),
    ident_of_string(d.name.name),
    list_of_array(tps),
    list_of_array(ps),
    ret,
    lower_expr(body),
  )
}

///|
fn lower_impls_exn(impls : @list.List[@syntax.Impl]) -> Sprog raise Unsupported {
  let funs = []
  let mut main = None
  for i in impls {
    match i {
      TopFuncDef(fun_decl~, decl_body~, where_clause~, loc~) => {
        if where_clause is Some(_) {
          unsupported("where clause", loc)
        }
        let body = match decl_body {
          DeclBody(expr~) => expr
          _ => {
            unsupported("function without a body", loc)
            panic()
          }
        }
        if fun_decl.name.name == "main" && fun_decl.decl_params is None {
          main = Some(lower_expr(body))
        } else {
          funs.push(lower_fun(fun_decl, body, loc))
        }
      }
      TopExpr(expr~, is_main~, loc~, ..) =>
        if is_main {
          main = Some(lower_expr(expr))
        } else {
          unsupported("fn init", loc)
        }
      TopTest(loc~, ..) => unsupported("test block", loc)
      TopTypeDef(d) => unsupported("type definition", d.loc)
      TopLetDef(loc~, ..) => unsupported("top-level let", loc)
      TopTrait(d) => unsupported("trait definition", d.loc)
      TopImpl(loc~, ..) => unsupported("impl", loc)
      TopView(loc~, ..) => unsupported("view", loc)
      TopImplRelation(loc~, ..) => unsupported("impl", loc)
      TopUsing(loc~, ..) => unsupported("using", loc)
      TopExtend(loc~, ..) => unsupported("extend", loc)
      TopImport(loc~, ..) => unsupported("import", loc)
    }
  }
  Sprog::Mk_sprog(list_of_array(funs), main)
}

///|
/// Implementation of the Rocq axiom `Driver.lower`.
pub fn lower_impls(impls : @list.List[@syntax.Impl]) -> Result0[Sprog, Lower_error] {
  lower_impls_exn(impls) catch {
    Unsupported(what, loc) =>
      Result0::Err(Lower_error::LowerUnsupported(what, pos_of_loc(loc)))
  } noraise {
    sp => Result0::Ok(sp)
  }
}
