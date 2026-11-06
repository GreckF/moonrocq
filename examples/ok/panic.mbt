// panic() and abort(msg) stop the program; they have any type.
fn checked_div(a : Int, b : Int) -> Int {
  if b == 0 {
    abort("division by zero")
  } else {
    a / b
  }
}

fn nth(xs : Array[Int], i : Int) -> Int {
  if i < 0 || i >= xs.length() {
    panic()
  }
  xs[i]
}

fn unwrap(o : Int?) -> Int {
  match o {
    Some(x) => x
    None => panic()
  }
}

fn main {
  let s : String = if checked_div(4, 2) > 1 { "big" } else { panic() }
  let t = if nth([1, 2], 0) == 1 { panic() } else { unwrap(Some(3)) }
  ignore((s, t))
}
