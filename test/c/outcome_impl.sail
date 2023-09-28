default Order dec
$include <prelude.sail>

$target_set emulator c ocaml interpreter lem

outcome test_ev1 : forall 'n, 'n > 0. ('a, bits('n)) -> unit
with
  'a: Type
= {
    val to_bits : 'a -> bits(64)

    impl emulator(x, y) = {
        match x {
            w: 'a => print_bits("w = ", to_bits(w))
        };
        print_bits("x = ", to_bits(x : 'a));
        let z: bits('n + 8) = 0xFF @ y;
        print_bits("z = ", z)
    }
}

function instance_to_bits(x: bits(32)) -> bits(64) = {
    sail_zero_extend(x, 64)
}

instantiation test_ev1 with
  'a = bits(32),
  to_bits = instance_to_bits

val main : unit -> unit

function main() = {
    test_ev1(0xABCD_0000, 0xFF)
}
