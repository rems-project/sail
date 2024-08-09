default Order dec

val print_endline = "print_endline" : string -> unit

newtype X = X : string

val f : X -> string

function f X(str) = {
  print_endline(str);
  "Test"
}

val main : unit -> unit

function main () = {
  print_endline(f(X("Hello, World")));
}
