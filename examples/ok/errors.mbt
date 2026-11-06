// Milestone M4: suberror, raise, try/catch/noraise, try!, defer/errdefer,
// raise?, fail, promotion to Error.
suberror DivError { DivError(String) }

suberror E2

suberror E3 {
  A
  B(Int, String)
}

fn div(x : Int, y : Int) -> Int raise DivError {
  if y == 0 {
    raise DivError("division by zero")
  }
  x / y
}

fn div_reraise(x : Int, y : Int) -> Int raise DivError {
  div(x, y)
}

fn f2() -> Unit raise E2 {
  raise E2
}

fn mixed(b : Bool) -> Int raise {
  if b {
    f2()
  }
  div(1, 0)
}

fn describe(e : Error) -> String {
  match e {
    E2 => "E2"
    A => "A"
    B(_, s) => s
    DivError(m) => m
    _ => "unknown"
  }
}

fn safe(x : Int, y : Int) -> Int {
  try div(x, y) catch {
    DivError(_) => 0
  } noraise {
    v => v + 1
  }
}

fn[T] map_poly(xs : Array[T], f : (T) -> T raise?) -> Array[T] raise? {
  let out : Array[T] = []
  for x in xs {
    out.push(f(x))
  }
  out
}

fn counted() -> Int {
  let mut n = 0
  try {
    defer { n = n + 1 }
    errdefer { n = n + 10 }
    f2()
  } catch {
    _ => ()
  }
  n
}

fn fail_test() -> Int raise Failure {
  fail("boom")
}

fn main {
  let a = div(4, 2) catch { _ => 0 }
  let r : Result[Int, DivError] = Ok(div(6, 3)) catch { e => Err(e) }
  let all : Result[Int, Error] = try { Ok(mixed(true)) } catch { e => Err(e) }
  let e : Error = E3::B(1, "x")
  let doubled = map_poly([1, 2], fn(x) { x * 2 })
  let s = try! div_reraise(1, 1)
  let msg = fail_test() catch { Failure(_) => 1 }
  ignore((a, r, all, describe(e), doubled, s, safe(1, 0), counted(), msg))
}
