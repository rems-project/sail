
union Test = {
  Ctor1 : int,
  Ctor2 : (int, int)
}

$[sv_module { stdout = true }]
val "print_endline" : string -> unit

function main() -> unit = {
  print_endline("ok")
}
