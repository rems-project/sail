val hello_world : unit -> string

function hello_world () = {
  return("Hello, World!");
  "Unreachable"
}

val main : unit -> unit effect {wreg, rreg}

register REG : string

function main () = {
  REG = "Hello, Sail!";
  print(REG);
  REG = hello_world();
  print(REG);
  return(())
}
