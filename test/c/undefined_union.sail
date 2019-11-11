
union Test = {
  Ctor1 : int,
  Ctor2 : (int, int)
}

val "print_endline" : string -> unit

function main() -> unit = {
  print_endline("ok")
}
