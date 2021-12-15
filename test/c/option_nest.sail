$sail_internal

union test ('a : Type) = {
  Just : 'a,
  Nothing : unit 
}

union option ('a : Type) = {
  None : unit,
  Some : 'a
}

val "print_endline" : string -> unit

function main() : unit -> unit = {
  let _ : test(option(int)) = Just(None());
  let Just(Some(x)) = Just(Some("test"));
  print_endline(x)
}
