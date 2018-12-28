
val "print_int" : (string, int) -> unit

val hd : forall ('a : Type). ('a, list('a)) -> 'a

function hd (def, xs) =
  match xs {
    y :: ys => y,
    [||]    => def
  }

val tl : forall ('a : Type). list('a) -> list('a)

function tl xs = match xs {
    y :: ys => ys,
    [||]    => [||]
  }

val main : unit -> unit

function main () = {
  let x : list(int) = [|1, 2, 3|];
  let y : int = hd(0, x);
  print_int("y = ", y);
  print_int("hd(tl(x)) = ", hd(0, tl(x)) : int);
  print_int("hd(tl(tl(x))) = ", hd(0, tl(tl(x))) : int);
}