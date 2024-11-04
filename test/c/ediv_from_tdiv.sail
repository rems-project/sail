default Order dec

$include <arith.sail>
$include <smt.sail>
$include <string.sail>

val my_ediv_int : (int, int) -> int

function my_ediv_int(n, m) = {
  if n < 0 & m < 0 then {
    tdiv_int(abs_int_plain(n) - 1, abs_int_plain(m)) + 1
  } else if n < 0 then {
    tdiv_int(n + 1, m) - 1
  } else {
    tdiv_int(n, m)
  }
}

val my_emod_int : (int, int) -> int

function my_emod_int(n, m) = {
  n - (m * my_ediv_int(n, m))
}

function main (() : unit) -> unit = {
  foreach (n from -100 to 100) {
    foreach (m from -100 to 100) {
      if m != 0 then {
        let d = ediv_int(n, m);
        let r = emod_int(n, m);

        let my_d = my_ediv_int(n, m);
        let my_r = my_emod_int(n, m);

        assert(d == my_d);
        assert(r == my_r);
        assert(n == m * d + r);
      }
    }
  };

  print_endline("ediv from tdiv ok")
}
