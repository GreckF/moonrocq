enum Answer {
  Yes
  No
}

fn f(a : Answer) -> Int {
  match a {
    Yes => 1
    No => "zero"
  }
}
