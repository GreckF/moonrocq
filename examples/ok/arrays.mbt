// Milestone M3: arrays and structs with mutable fields.
struct Counter {
  name : String
  mut count : Int
}

fn bump(c : Counter, by : Int) -> Unit {
  c.count += by
}

fn squares(n : Int) -> Array[Int] {
  let xs : Array[Int] = []
  for i = 0; i < n; i = i + 1 {
    xs.push(i * i)
  }
  xs
}

fn main {
  let xs = squares(4)
  xs[0] = 10
  xs[1] += 5
  let fixed : FixedArray[Bool] = FixedArray::make(3, false)
  fixed[2] = true
  let grid = Array::make(2, 'x')
  let c = { name: "c", count: 0 }
  let alias = c
  bump(alias, xs[0] + xs.length())
  let { count, .. } = c
  let positive = match c {
    { count: 0, .. } => false
    _ => true
  }
  ignore((count, positive, fixed[2], grid[1], c.name))
}
