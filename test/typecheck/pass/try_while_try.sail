default Order dec
$include <prelude.sail>

union exception = {
  Error_again : unit,
  Error_fail : unit
}

register state : int

val step : unit -> unit effect {rreg,escape}

function step () = {
  match state {
  0 => throw(Error_again(())),
  1 => throw(Error_fail(())),
  _ => ()
  }
}

val myloop : unit -> bool effect {rreg,escape}

function myloop () = {
  try {
    var cont : bool = true;
    while cont do {
      try {
        step();
	cont = false;
      } catch {
        Error_again(_) => (),
	exn => throw(exn)
      }
    };
    true
  } catch {
    _ => false
  }
}
