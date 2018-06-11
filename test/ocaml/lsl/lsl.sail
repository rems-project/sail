
val lslc : forall ('n : Int) ('shift : Int), 'n >= 1.
  (bits('n), atom('shift)) -> (bits('n), bit) effect {escape}

function lslc (vec, shift) = {
  assert(constraint('shift >= 1), "shift must be positive");
  extended : bits('shift + 'n) = vec @ sail_zeros(shift);
  result : bits('n) = extended[sizeof('n - 1) .. 0];
  c : bit = extended['n];
  return((result, c))
}

val lsl : forall ('n : Int) ('shift : Int), 'n >= 1.
  (bits('n), atom('shift)) -> bits('n) effect {escape}

function lsl (vec, shift) = if shift == 0 then vec else let (result, _) = lslc(vec, shift) in result

val main : unit -> unit effect {escape}

function main () = {
  print(if lsl(0b0110, 1) == 0b1100 then "pass" else "fail");
  print(if lsl(0b1111, 2) == 0b1100 then "pass" else "fail");
  print(if lsl(0x0F, 4) == 0xF0 then "pass" else "fail");
  let (result, c) = lslc(0xF000, 2) in print(if (result == 0xC000) & (c == bitone) then "pass" else "fail")
}
