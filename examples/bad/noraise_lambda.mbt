suberror E1 { E1(Int) }
suberror E2
fn f2() -> Unit raise E2 { raise E2 }

fn twice(g : () -> Unit) -> Unit {
  g()
  g()
}

fn main {
  twice(fn() { f2() })
}
