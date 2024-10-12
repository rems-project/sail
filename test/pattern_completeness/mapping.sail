struct bool2 = {
    field: bool,
}

mapping m : bool <-> bool2 = {
   true <-> struct { field = true },
   false <->  struct{ field = false },
}

let foo = m(true)
