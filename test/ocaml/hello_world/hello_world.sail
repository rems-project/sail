
val unit -> string effect pure hello_world

function hello_world () = {
  return "Hello, World!";
  "Unreachable"
}

val unit -> unit effect {wreg, rreg} main

register string REG

function main () = {
  REG := "Hello, Sail!";
  print(REG);
  REG := hello_world ();
  print(REG);
  return ()
}
