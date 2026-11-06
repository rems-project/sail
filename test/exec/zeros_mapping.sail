default Order dec

$include <prelude.sail>

type regbits = bits(5)

mapping zeros_16 : unit <-> bits(16) = { () <-> 0x0000 }

scattered union ast

val encdec : ast <-> bits(32)

scattered mapping encdec

union clause ast = Add : (regbits, regbits, regbits)

mapping clause encdec = Add(dest, src1, src2) <-> zeros_16() @ dest @ src1 @ src2 @ 0b1

val main : unit -> unit

function main() = {
    let instr = encdec(0x0000FFFF);
    match instr {
        Add(dest, src1, src2) => {
            print_bits("dest = ", dest);
            print_bits("src1 = ", dest);
            print_bits("src2 = ", dest);
        }
    }
}
