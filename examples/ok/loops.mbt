// Milestone M3: mutable variables, loops, labelled jumps and return.
fn sum_to(n : Int) -> Int {
  let mut acc = 0
  let mut i = 1
  while i <= n {
    acc += i
    i = i + 1
  }
  acc
}

fn first_even(limit : Int) -> Int {
  let mut i = 1
  while i < limit {
    if i % 2 == 0 {
      break i
    }
    i = i + 1
  } nobreak {
    -1
  }
}

fn sum_odd(n : Int) -> Int {
  for i = 0, acc = 0; i < n; i = i + 1 {
    if i % 2 == 0 {
      continue i + 1, acc
    }
    if i > 100 {
      break acc
    }
  } nobreak {
    acc
  }
}

fn count_pairs(n : Int) -> Int {
  let mut count = 0
  outer~: for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      if j > i {
        continue outer~
      }
      if i + j > 10 {
        break outer~
      }
      count = count + 1
    }
  }
  count
}

fn abs(n : Int) -> Int {
  result~: {
    if n < 0 {
      break result~ -n
    }
    n
  }
}

fn find(xs : Array[Int], x : Int) -> Int {
  for i = 0; i < xs.length(); i = i + 1 {
    if xs[i] == x {
      return i
    }
  }
  -1
}

fn make_counter() -> () -> Int {
  let mut n = 0
  fn() {
    n = n + 1
    n
  }
}

fn main {
  let c = make_counter()
  ignore(c())
  let total = sum_to(10) + first_even(9) + sum_odd(10) + count_pairs(5) + abs(-3) +
    find([4, 5, 6], 5) + c()
  ignore(total)
}
