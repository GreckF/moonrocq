fn main {
  let mut n = 0
  for c in "abc" {
    ignore(c)
    n = n + 1
  }
  ignore(n)
}
