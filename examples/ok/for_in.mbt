// for .. in over ranges and arrays, with loop state; Ref.
fn sum(xs : Array[Int]) -> Int {
  for x in xs; acc = 0; acc = acc + x {

  } nobreak {
    acc
  }
}

fn index_of(xs : FixedArray[String], s : String) -> Int {
  for i, x in xs {
    if x == s {
      return i
    }
  }
  -1
}

fn count_down(n : Int64) -> Int64 {
  let mut total = 0L
  for i in n>=..0L {
    total = total + i
  }
  for i in n>..0L {
    if i == 1L {
      continue
    }
    total = total - i
  }
  total
}

fn first_big(xs : Array[(Int, String)]) -> String {
  for (n, name) in xs {
    if n > 10 {
      break name
    }
  } nobreak {
    "none"
  }
}

fn skip_evens(n : Int) -> Int {
  outer~: for i in 0..<=n; seen = 0 {
    for j in 0..<i {
      if j == 2 {
        continue outer~ seen
      }
    }
    if i % 2 == 0 {
      continue seen + 1
    }
  } nobreak {
    seen
  }
}

fn main {
  let counter = Ref::new(0)
  let r : Ref[Int] = { val: 2 }
  let alias = r
  alias.val += 1
  counter.val = counter.val + r.val
  let { val } = counter
  let total = sum([1, 2, 3]) + index_of(["a", "b"], "b") + skip_evens(6) + val
  ignore((total, count_down(3L), first_big([(1, "x"), (20, "y")])))
}
