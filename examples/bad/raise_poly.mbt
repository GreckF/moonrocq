suberror E1 { E1(Int) }
suberror E2
fn f2() -> Unit raise E2 { raise E2 }

fn poly(g : () -> Unit raise?) -> Unit raise? {
  g()
  raise E2
}
