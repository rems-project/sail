val f : int -> int

function f(x) = {
  y : int = x;
  z : int = 0;
  y = y+1;
  let 'y = y in {(); z = y};
  z + y
}

val main : unit -> unit

function main () = {
  print (if f(5) == 12 then "pass" else "fail")
}
