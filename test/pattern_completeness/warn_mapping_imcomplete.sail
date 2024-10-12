struct bool2 = {
    field: bool,
}

mapping complete : bool <-> bool2 = {
   true <-> struct { field = false },
   false <->  struct{ field = true },
}

mapping imcomplete_oneside : bool <-> bool2 = {
   true <-> struct { field = false },
   false <-> struct { field = false },
}

mapping imcomplete_both_side : bool <-> bool2 = {
   true <-> struct { field = false },
   true <-> struct { field = false },
}

mapping forwords_unreachable : bool <-> int = {
   forwards _ => 1,
}

mapping backwords_unreachable : bool <-> int = {
   backwards _ => false,
}

mapping multi_warning : bool <-> int = {
   backwards 2 => false,
}

register enabled : bool

val encdec : bool <-> bool2

scattered mapping encdec

mapping clause encdec = true if enabled <-> struct { field = false } if enabled

end encdec
