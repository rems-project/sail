default Order dec

$include <prelude.sail>
$include <mapping.sail>

infixl 5 ++

overload operator ++ = concat_str

function main() -> unit = {
  match " " {
    spc() => print_endline("ok"),
    _ => print_endline("fail 1"),
  };
  match "" {
    spc() => print_endline("fail 2"),
    _ => print_endline("ok"),
  };
  match " not spaces" {
    spc() => print_endline("fail 3"),
    _ => print_endline("ok"),
  };
  match "    " {
    spc() => print_endline("ok"),
    _ => print_endline("fail 4"),
  };

  match " " {
    opt_spc() => print_endline("ok"),
    _ => print_endline("fail 5"),
  };
  match "" {
    opt_spc() => print_endline("ok"),
    _ => print_endline("fail 6"),
  };
  match "    " {
    opt_spc() => print_endline("ok"),
    _ => print_endline("fail 7"),
  };

  match " " {
    def_spc() => print_endline("ok"),
    _ => print_endline("fail 8"),
  };
  match "" {
    def_spc() => print_endline("ok"),
    _ => print_endline("fail 9"),
  };
  match "    " {
    def_spc() => print_endline("ok"),
    _ => print_endline("fail 10"),
  };

  match ((), (), ()) {
    (spc(s1), opt_spc(s2), def_spc(s3)) => {
      print_endline(">" ++ s1 ++ "<");
      print_endline(">" ++ s2 ++ "<");
      print_endline(">" ++ s3 ++ "<");
    },
    _ => print_endline("fail 11"),
  }
}
