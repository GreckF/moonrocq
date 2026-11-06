suberror E1 { E1(Int) }
suberror E2
fn f2() -> Unit raise E2 { raise E2 }

fn main {
  f2()
}
