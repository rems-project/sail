val print_int : int -> unit

val print_string : string -> unit

overload print = {print_int, print_string}

function main() : unit -> unit = {
  print("Hello, World!");
  print(4)
}