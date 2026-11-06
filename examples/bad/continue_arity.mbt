fn f(n : Int) -> Int {
  for i = 0, acc = 0; i < n; i = i + 1 {
    continue i + 1
  } nobreak {
    acc
  }
}
