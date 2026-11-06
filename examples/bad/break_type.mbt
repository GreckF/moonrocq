fn f(n : Int) -> Int {
  let mut i = 0
  while i < n {
    if i == 3 {
      break "three"
    }
    i = i + 1
  } nobreak {
    0
  }
}
