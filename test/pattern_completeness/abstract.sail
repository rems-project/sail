type xlen : Int

constraint xlen in {32, 64}

function foo(n : range(0, 1)) -> bool =
  match n {
    0 => true,
    1 => false,
  }
