default Order dec

$include <prelude.sail>

val zeros : forall 'n, 'n >= 0 . implicit('n) -> bits('n)
function zeros (n) = sail_zeros (n)

function main() -> unit = {
  let b : bool = true;
  let _ = if b then 0x12 else zeros();
  let _ = if b then zeros() else 0x12;
  let _ = if b then 1 else 2;

  let _ = if true then 0x12 else zeros();
  let _ = if true then zeros() else 0x12;
  let _ = if true then 1 else 2;
}
