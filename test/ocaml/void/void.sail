
val void : forall 'n, 'n == 'n + 1. atom('n) -> unit

function void _ = ()

val main : unit -> unit

function main () = {
  print("Before");
  if false then {
    print("After");
    void(0);
  }
}