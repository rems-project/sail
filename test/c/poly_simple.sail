default Order dec

val "print" : string -> unit

union Poly ('a : Type) = {
  Ctor : 'a
}

function main() : unit -> unit = {
  let x = Ctor(3 : int);
  let y = Ctor("Hello, World!\n");
  match y {
    Ctor(str) => print(str)
  }
}