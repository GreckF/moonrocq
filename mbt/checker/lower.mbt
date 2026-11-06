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
    Arrow(args~, res~, err~, is_async~, loc~, ..) => {
      if is_async is Some(_) {
        unsupported("async function type", loc)
      }
      Sty::SArrow(pos_of_loc(loc), lower_types(args), lower_type(res), lower_eff(err, loc))
    }
    Option(ty~, loc~, ..) =>
      Sty::SName(
        pos_of_loc(loc),
        ident_of_string("Option"),
        List::Cons(lower_type(ty), List::Nil),
      )
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
/// The effect of a signature: `None` for `noraise`, `raise` is `raise Error`,
/// `raise?` is `raise ?` (a hidden type parameter, see `Elab.sig_tparams`).
fn lower_eff(e : @syntax.ErrorType, loc : @basic.Location) -> Sty? raise Unsupported {
  match e {
    NoErrorType | Noraise(..) => None
    DefaultErrorType(..) => Some(Sty::SName(pos_of_loc(loc), ident_of_string("Error"), List::Nil))
    ErrorType(ty~) => Some(lower_type(ty))
    MaybeError(..) => Some(Sty::SName(pos_of_loc(loc), ident_of_string("?"), List::Nil))
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
/// The `T` of `T::C`, if written.
fn ctor_type(c : @syntax.Constructor) -> String0? raise Unsupported {
  match c.extra_info {
    NoExtraInfo => None
    TypeName(tn) => Some(ident_of_string(type_name_str(tn)))
    _ => {
      unsupported("constructor of another package", c.loc)
      None
    }
  }
}

///|
fn type_name_str(tn : @syntax.TypeName) -> String raise Unsupported {
  match tn.name {
    Ident(name~) => name
    Dot(pkg~, id~) => {
      unsupported("qualified type @\{pkg}.\{id}", tn.loc)
      id
    }
  }
}

///|
fn lower_patterns(ps : @list.List[@syntax.Pattern]) -> List[Spat] raise Unsupported {
  let out = []
  for p in ps {
    out.push(lower_pattern(p))
  }
  list_of_array(out)
}

///|
fn lower_pattern(p : @syntax.Pattern) -> Spat raise Unsupported {
  match p {
    Any(loc~) => Spat::SPWild(pos_of_loc(loc))
    Var(b) => Spat::SPVar(pos_of_loc(b.loc), ident_of_string(b.name))
    Constant(c~, loc~) => Spat::SPLit(pos_of_loc(loc), lower_constant(c, loc))
    Tuple(pats~, loc~) => Spat::SPTuple(pos_of_loc(loc), lower_patterns(pats))
    Constr(constr~, args~, is_open~, loc~) => {
      let ps = []
      match args {
        Some(xs) =>
          for a in xs {
            match a.kind {
              Positional => ps.push(lower_pattern(a.pat))
              _ => unsupported("labelled constructor pattern", loc)
            }
          }
        None => ()
      }
      Spat::SPConstr(
        pos_of_loc(loc),
        ctor_type(constr),
        ident_of_string(constr.name.name),
        list_of_array(ps),
        is_open,
      )
    }
    Record(fields~, is_closed~, loc~) => {
      let fs = []
      for f in fields {
        let sp = if f.is_pun {
          Spat::SPVar(pos_of_loc(f.loc), ident_of_string(f.label.name))
        } else {
          lower_pattern(f.pattern)
        }
        fs.push((ident_of_string(f.label.name), sp))
      }
      Spat::SPRecord(pos_of_loc(loc), list_of_array(fs), !is_closed)
    }
    Constraint(pat~, ty~, loc~) =>
      Spat::SPAnnot(pos_of_loc(loc), lower_pattern(pat), lower_type(ty))
    _ => {
      unsupported("this kind of pattern", p.loc())
      Spat::SPWild(pos_of_loc(p.loc()))
    }
  }
}

///|
/// `let x = e` / `let _ = e` / `let x : T = e`, without destructuring.
fn simple_let_pattern(p : @syntax.Pattern) -> Bool {
  match p {
    Var(_) | Any(..) => true
    Constraint(pat~, ..) => pat is (Var(_) | Any(..))
    _ => false
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
  // `None`: not annotated (the effect comes from the expected type)
  let eff : Sty?? = match f.error_type {
    NoErrorType => None
    e => Some(lower_eff(e, loc))
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
  Sexpr::SLam(pos_of_loc(loc), list_of_array(ps), ret, eff, lower_expr(f.body))
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
    Let(pattern~, expr~, body~, loc~) =>
      if simple_let_pattern(pattern) {
        let (x, ann) = lower_let_pattern(pattern, loc)
        Sexpr::SLet(pos_of_loc(loc), x, ann, lower_expr(expr), lower_expr(body))
      } else {
        // `let p = e; body` is `match e { p => body }`
        Sexpr::SMatch(
          pos_of_loc(loc),
          lower_expr(expr),
          List::Cons((lower_pattern(pattern), lower_expr(body)), List::Nil),
        )
      }
    Constr(constr~, loc~) =>
      Sexpr::SConstr(pos_of_loc(loc), ctor_type(constr), ident_of_string(constr.name.name))
    Record(type_name~, fields~, loc~, ..) => {
      let tq = match type_name {
        Some(tn) => Some(ident_of_string(type_name_str(tn)))
        None => None
      }
      let fs = []
      for f in fields {
        let fe = if f.is_pun {
          Sexpr::SVar(pos_of_loc(f.loc), ident_of_string(f.label.name))
        } else {
          lower_expr(f.expr)
        }
        fs.push((ident_of_string(f.label.name), fe))
      }
      Sexpr::SRecord(pos_of_loc(loc), tq, list_of_array(fs))
    }
    Match(expr~, cases~, loc~, ..) =>
      Sexpr::SMatch(pos_of_loc(loc), lower_expr(expr), lower_cases(cases, loc))
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
        Label(l) =>
          Sexpr::SField(pos_of_loc(loc), lower_expr(record), ident_of_string(l.name))
        _ => {
          unsupported("field access", loc)
          Sexpr::SLit(pos_of_loc(loc), Slit::SLUnit)
        }
      }
    Function(func~, loc~) => lower_lambda(func, loc)
    Constraint(expr~, ty~, loc~) =>
      Sexpr::SAnnot(pos_of_loc(loc), lower_expr(expr), lower_type(ty))
    Group(expr~, ..) => lower_expr(expr)
    // ---- milestone M3: state and loops ----
    LetMut(binder~, ty~, expr~, body~, loc~) => {
      let ann = match ty {
        Some(t) => Some(lower_type(t))
        None => None
      }
      Sexpr::SLetMut(
        pos_of_loc(loc),
        ident_of_string(binder.name),
        ann,
        lower_expr(expr),
        lower_expr(body),
      )
    }
    Assign(var_~, expr~, augmented_by~, loc~) =>
      Sexpr::SAssign(
        pos_of_loc(loc),
        ident_of_string(var_name(var_)),
        lower_op(augmented_by),
        lower_expr(expr),
      )
    Array(exprs~, is_iter~, loc~) => {
      if is_iter {
        unsupported("iterator literal", loc)
      }
      Sexpr::SArray(pos_of_loc(loc), lower_exprs(exprs))
    }
    ArrayGet(array~, index~, loc~) =>
      Sexpr::SIndex(pos_of_loc(loc), lower_expr(array), lower_expr(index))
    ArraySet(array~, index~, value~, loc~) =>
      Sexpr::SIndexSet(
        pos_of_loc(loc),
        lower_expr(array),
        lower_expr(index),
        None,
        lower_expr(value),
      )
    ArrayAugmentedSet(op~, array~, index~, value~, loc~) =>
      Sexpr::SIndexSet(
        pos_of_loc(loc),
        lower_expr(array),
        lower_expr(index),
        lower_op(Some(op)),
        lower_expr(value),
      )
    Mutate(record~, accessor~, field~, augmented_by~, loc~) =>
      match accessor {
        Label(l) =>
          Sexpr::SFieldSet(
            pos_of_loc(loc),
            lower_expr(record),
            ident_of_string(l.name),
            lower_op(augmented_by),
            lower_expr(field),
          )
        _ => {
          unsupported("assignment to this kind of field", loc)
          Sexpr::SLit(pos_of_loc(loc), Slit::SLUnit)
        }
      }
    DotApply(self~, method_name~, args~, return_self~, loc~) => {
      if return_self {
        unsupported("method cascade `..`", loc)
      }
      Sexpr::SMethod(
        pos_of_loc(loc),
        lower_expr(self),
        ident_of_string(method_name.name),
        lower_args(args, loc),
      )
    }
    Method(type_name~, method_name~, loc~) =>
      Sexpr::SQual(
        pos_of_loc(loc),
        ident_of_string(type_name_str(type_name)),
        ident_of_string(method_name.name),
      )
    While(loop_cond~, loop_body~, while_else~, label~, loc~) =>
      Sexpr::SWhile(
        pos_of_loc(loc),
        lower_label(label),
        lower_expr(loop_cond),
        lower_expr(loop_body),
        lower_opt_expr(while_else),
      )
    For(binders~, condition~, continue_block~, body~, for_else~, where_clause~, label~, loc~) => {
      if where_clause is Some(_) {
        unsupported("where clause", loc)
      }
      Sexpr::SFor(
        pos_of_loc(loc),
        lower_label(label),
        lower_bindings(binders),
        lower_opt_expr(condition),
        lower_bindings(continue_block),
        lower_expr(body),
        lower_opt_expr(for_else),
      )
    }
    ForEach(patterns~, expr~, init~, continue_block~, body~, else_block~, where_clause~, label~, loc~) => {
      if where_clause is Some(_) {
        unsupported("where clause", loc)
      }
      Sexpr::SForIn(
        pos_of_loc(loc),
        lower_label(label),
        lower_patterns(patterns),
        lower_expr(expr),
        lower_bindings(init),
        lower_bindings(continue_block),
        lower_expr(body),
        lower_opt_expr(else_block),
      )
    }
    // ---- milestone M4: errors ----
    Raise(err_value~, loc~) => Sexpr::SRaise(pos_of_loc(loc), lower_expr(err_value))
    Try(body~, catch_~, try_else~, loc~, ..) => {
      let nr = match try_else {
        Some(cs) => Some(lower_cases(cs, loc))
        None => None
      }
      Sexpr::STry(pos_of_loc(loc), lower_expr(body), lower_cases(catch_, loc), nr)
    }
    TryOperator(body~, kind=Exclamation, loc~, ..) =>
      Sexpr::STryBang(pos_of_loc(loc), lower_expr(body))
    Defer(expr~, body~, loc~) =>
      Sexpr::SDefer(pos_of_loc(loc), false, lower_expr(expr), lower_expr(body))
    ErrDefer(expr~, body~, loc~) =>
      Sexpr::SDefer(pos_of_loc(loc), true, lower_expr(expr), lower_expr(body))
    LabelledBlock(label~, body~, loc~) =>
      Sexpr::SBlock(pos_of_loc(loc), ident_of_string(label.name), lower_expr(body))
    Break(arg~, label~, loc~) =>
      Sexpr::SBreak(pos_of_loc(loc), lower_label(label), lower_opt_expr(arg))
    Continue(args~, label~, loc~) =>
      Sexpr::SContinue(pos_of_loc(loc), lower_label(label), lower_exprs(args))
    Return(return_value~, loc~) =>
      Sexpr::SReturn(pos_of_loc(loc), lower_opt_expr(return_value))
    _ => {
      unsupported(expr_kind(e), e.loc())
      Sexpr::SLit(pos_of_loc(e.loc()), Slit::SLUnit)
    }
  }
}

///|
fn lower_cases(
  cases : @list.List[@syntax.Case],
  loc : @basic.Location,
) -> List[(Spat, Sexpr)] raise Unsupported {
  let cs = []
  for c in cases {
    if c.guard_ is Some(_) {
      unsupported("match guard", loc)
    }
    cs.push((lower_pattern(c.pattern), lower_expr(c.body)))
  }
  list_of_array(cs)
}

///|
fn lower_opt_expr(e : @syntax.Expr?) -> Sexpr? raise Unsupported {
  match e {
    Some(e) => Some(lower_expr(e))
    None => None
  }
}

///|
/// Operator of an augmented assignment (`+` for `+=`).
fn lower_op(op : @syntax.Var?) -> String0? raise Unsupported {
  match op {
    Some(v) => Some(ident_of_string(var_name(v)))
    None => None
  }
}

///|
fn lower_label(l : @syntax.Label?) -> String0? {
  match l {
    Some(l) => Some(ident_of_string(l.name))
    None => None
  }
}

///|
fn lower_bindings(
  bs : @list.List[(@syntax.Binder, @syntax.Expr)],
) -> List[(String0, Sexpr)] raise Unsupported {
  let out = []
  for b in bs {
    let (x, e) = b
    out.push((ident_of_string(x.name), lower_expr(e)))
  }
  list_of_array(out)
}

///|
fn lower_args(
  args : @list.List[@syntax.Argument],
  loc : @basic.Location,
) -> List[Sexpr] raise Unsupported {
  let out = []
  for a in args {
    match a.kind {
      Positional => out.push(lower_expr(a.value))
      _ => unsupported("labelled argument", loc)
    }
  }
  list_of_array(out)
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
  "expression `" + s.clamped_view(start=0, end=n).to_owned() + "`"
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
    lower_eff(d.error_type, loc),
    lower_expr(body),
  )
}

///|
fn lower_ctors(
  cs : @list.List[@syntax.ConstrDecl],
) -> List[(String0, List[Sty])] raise Unsupported {
  let out = []
  for c in cs {
    if c.tag is Some(_) {
      unsupported("constructor tag", c.loc)
    }
    let fs = []
    match c.args {
      Some(ps) =>
        for p in ps {
          if p.mut_ {
            unsupported("mutable constructor field", c.loc)
          }
          if p.label is Some(_) {
            unsupported("labelled constructor field", c.loc)
          }
          fs.push(lower_type(p.ty))
        }
      None => ()
    }
    out.push((ident_of_string(c.name.name), list_of_array(fs)))
  }
  list_of_array(out)
}

///|
fn lower_typedecl(d : @syntax.TypeDecl) -> Stype raise Unsupported {
  let tps = []
  for b in d.params {
    match b.name {
      Some(n) => tps.push(ident_of_string(n))
      None => unsupported("anonymous type parameter", b.loc)
    }
  }
  let body = match d.components {
    Variant(cs) => Sdecl::SDEnum(lower_ctors(cs))
    Record(fields~, constr_decl~) => {
      if constr_decl is Some(_) {
        unsupported("struct constructor declaration", d.loc)
      }
      let out = []
      for f in fields {
        out.push(((ident_of_string(f.name.label), f.mut_), lower_type(f.ty)))
      }
      Sdecl::SDStruct(list_of_array(out))
    }
    TupleStruct(tys) => Sdecl::SDTupleStruct(lower_types(tys))
    Alias(_) => {
      unsupported("type alias", d.loc)
      Sdecl::SDEnum(List::Nil)
    }
    Error(NoPayload) =>
      Sdecl::SDError(List::Cons((ident_of_string(d.tycon), List::Nil), List::Nil))
    Error(EnumPayload(cs)) => Sdecl::SDError(lower_ctors(cs))
    _ => {
      unsupported("this kind of type declaration", d.loc)
      Sdecl::SDEnum(List::Nil)
    }
  }
  Stype::Mk_stype(
    pos_of_loc(d.loc),
    ident_of_string(d.tycon),
    list_of_array(tps),
    body,
  )
}

///|
fn lower_impls_exn(impls : @list.List[@syntax.Impl]) -> Sprog raise Unsupported {
  let types = []
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
      TopTypeDef(d) => types.push(lower_typedecl(d))
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
  Sprog::Mk_sprog(list_of_array(types), list_of_array(funs), main)
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
