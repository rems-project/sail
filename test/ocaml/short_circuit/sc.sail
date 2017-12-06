
val fail : unit -> bool effect {escape}

function fail () = {
  assert(false);
  true
}

val main : unit -> unit effect {escape}

function main () = {
  assert(~(false & fail()));
  assert(true | fail());
  print("ok")
}