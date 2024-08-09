$include <flow.sail>

val print_endline = "print_endline" : string -> unit
val print_int = "print_int" : (string, int) -> unit

union exception = {
  Epair : (range(0, 255), range(0, 255)),
  Eunknown : unit,
  Estring : string
}

val f : unit -> unit effect {escape}

function f () = throw(Estring("test"))

val g : unit -> string effect {escape}

function g () = {
  print_endline("in g()");
  return("g return");
  throw(Estring("never thrown from g"));
}

val main : unit -> unit effect {escape}

function main () = {
  try {
    print_endline(g());
    f(); // will throw Estring
    throw(Epair(42, 24));
    throw(Eunknown());
  } catch {
    Eunknown()   => print_endline("Caught Eunknown"),
    Epair(x, y)  => print_endline("Caught Epair"),
    Estring(str) => {
      print_endline("Caught Estring");
      print_endline(str)
    }
  };
  try () catch {
    _ => print_endline("Unreachable!")
  };
  try throw(Epair(33, 1)) catch {
    Epair(x, _)  => {
      print_endline("2nd try Caught Epair");
      print_int("x = ", x);
    },
    _            => ()
  };
  try throw(Eunknown()) catch {
    _ => try let _ = g() in () catch {
      _ => print_endline("caught old exception")
    }
  };
  try
    try throw Eunknown() catch {
      Estring(_) => ()
    }
  catch {
    Eunknown() => print_endline("Fall through OK"),
    _ => ()
  };
  f();
  ()
}
