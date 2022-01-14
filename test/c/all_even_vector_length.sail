default Order dec
$include <prelude.sail>
$include <string.sail>

val all_even : forall 'n, 'n > 0. (vector('n, dec, bits(5))) -> bool

function all_even (registers) = {
    foreach (x from 0 to (length(registers) - 1)) {
        if (registers[x][0] == bitone) then return false
    };
    true
}

val main : unit -> unit

function main() = {
    let regs = [0b00010, 0b00000];
    print_int("length = ", length(regs));
    if all_even(regs) then {
        print_endline("ok")
    };
    ()
}