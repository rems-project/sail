
val forall Num 'n, 'n >= 0. [:'n:] -> bit['n] effect pure zeros

function zeros n = replicate_bits(0b0, sizeof 'n)

val forall Num 'n, Num 'shift, 'n >= 0. (bit['n], [:'shift:]) -> (bit['n], bit) effect pure lslc

function lslc (vec, shift) = {
  assert(constraint('shift >= 1), "shift must be positive");
  (bit['shift + 'n]) extended := vec : zeros(shift);
  (bit['n]) result := extended[sizeof 'n - 1 .. 0];
  (bit) c := extended[sizeof 'n];
  return (result, c)
}

val forall Num 'n, Num 'shift, 'n >= 0. (bit['n], [:'shift:]) -> bit['n] effect pure lsl

function lsl (vec, shift) =
  if shift == 0
  then vec
  else let (result, _) = lslc(vec, shift) in result

val unit -> unit effect pure main

function main () = {
  print(if lsl(0b0110,1) == 0b1100 then "pass" else "fail");
  print(if lsl(0b1111,2) == 0b1100 then "pass" else "fail");
  print(if lsl(0x0F,4) == 0xF0 then "pass" else "fail");
  let (result, c) = lslc(0xF000,2) in
  print(if result == 0xC000 & c == bitone then "pass" else "fail")
}
