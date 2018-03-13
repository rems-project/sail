default Order dec

val print = "print_endline" : string -> unit

newtype X = X : string

val f : X -> string

function f X(str) = {
  print(str);
  "Test"
}

val main : unit -> unit

function main () = {
  print(f(X("Hello, World")));
}