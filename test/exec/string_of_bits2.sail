default Order dec

$include <prelude.sail>
$include <string.sail>

infixl 1 ++

overload operator ++ = {concat_str}

val main : unit -> unit

function main() = {
    print(bits_str(0b0) ++ "\n");
    print(bits_str(0b1) ++ "\n");
    print(bits_str(0b001) ++ "\n");
    print(bits_str(0b00001) ++ "\n");
    print(bits_str(0b0001) ++ "\n");
    print(bits_str(0b1001) ++ "\n");
    print(bits_str(0xAB) ++ "\n");
    print(bits_str(0x00AB) ++ "\n")
}