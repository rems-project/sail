
val "print_int" : (string, int) -> unit

let 'cap_size = 32

val main : unit -> unit

function main() = {
  print_int("cap_size = ", cap_size);
}