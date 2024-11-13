default Order dec

$include <prelude.sail>
$include <string.sail>

overload operator ^ = {xor_vec}
overload operator ^ = {add_bits}
overload operator ^ = {concat_str}

register R : vector(10, bool)

val main : unit -> unit

function main() = {
  R = vector_init(false);

  let x =
    (if R[0] then "0" else "1")
    ^ (if R[1] then "0" else "1")
    ^ (if R[2] then "0" else "1")
    ^ (if R[3] then "0" else "1")
    ^ (if R[4] then "0" else "1")
    ^ (if R[5] then "0" else "1")
    ^ (if R[6] then "0" else "1")
    ^ (if R[7] then "0" else "1")
    ^ (if R[8] then "0" else "1")
    ^ (if R[9] then "0" else "1");

  print_endline(x)
}
