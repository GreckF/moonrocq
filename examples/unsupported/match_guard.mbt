fn sign(n : Int) -> Int {
  match n {
    x if x < 0 => -1
    0 => 0
    _ => 1
  }
}
