default Order dec

$include <prelude.sail>

$option --abstract-types
$option --instantiate w=32

type w : Int

constraint w in {32, 64}

bitfield foo : bits(w) = {
  field1 : w - 1 .. 16,
  field2 : 15 .. 0
}

val main : unit -> unit

function main() = {
    var x = Mk_foo(sail_zeros(sizeof(w)));
    x[field1] = sail_ones(sizeof(w) - 16);
    x[field2] = 0xABCD;
    if sizeof(w) == 64 then {
        print_bits("x = ", x.bits)
    }
}
