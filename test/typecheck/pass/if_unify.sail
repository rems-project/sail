default Order dec

$include <prelude.sail>

val zero_extend : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
val zeros : forall 'n, 'n >= 0 . implicit('n) -> bits('n)

type pte_bits('v) = bits(if 'v == 32 then 34 else 56)

function translate forall 'v . (_pte_addr : pte_bits('v)) -> unit = ()

function pt_walk forall 'v . (sv_width : int('v)) -> unit = {
    let pte_addr : pte_bits('v) = zeros(if 'v == 32 then 34 else 56);
    translate(pte_addr);
   ()
}
