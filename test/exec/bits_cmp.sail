default Order dec
$include <prelude.sail>

// Compare wrappers like the ones in the sail-riscv prelude. The C backend
// compiles calls on bitvectors of at most 64 bits without integers.

infix 4 <_u
infix 4 <=_u
infix 4 >_u
infix 4 >=_u
infix 4 <_s
infix 4 >=_s

val operator <_u : forall 'n. (bits('n), bits('n)) -> bool
val operator <=_u : forall 'n. (bits('n), bits('n)) -> bool
val operator >_u : forall 'n. (bits('n), bits('n)) -> bool
val operator >=_u : forall 'n. (bits('n), bits('n)) -> bool
val operator <_s : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator >=_s : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool

function operator <_u (x, y) = unsigned(x) < unsigned(y)
function operator <=_u (x, y) = unsigned(x) <= unsigned(y)
function operator >_u (x, y) = unsigned(x) > unsigned(y)
function operator >=_u (x, y) = unsigned(x) >= unsigned(y)
function operator <_s (x, y) = signed(x) < signed(y)
function operator >=_s (x, y) = signed(x) >= signed(y)

val print_bool : (string, bool) -> unit

function print_bool(s, b) = print_endline(concat_str(s, if b then "true" else "false"))

val cmp : forall 'n, 0 < 'n <= 64. (bits('n), bits('n)) -> unit

function cmp(x, y) = {
    print_bool("<_u ", x <_u y);
    print_bool("<=_u ", x <=_u y);
    print_bool(">_u ", x >_u y);
    print_bool(">=_u ", x >=_u y);
    print_bool("<_s ", x <_s y);
    print_bool(">=_s ", x >=_s y)
}

val main : unit -> unit

function main() = {
    let a : bits(64) = 0xFFFFFFFFFFFFFFFF;
    let b : bits(64) = 0x0000000000000001;
    print_bool("fixed <_u ", a <_u b);
    print_bool("fixed >_u ", a >_u b);
    print_bool("fixed <_s ", a <_s b);
    print_bool("fixed >=_s ", a >=_s b);
    let c : bits(12) = 0x800;
    let d : bits(12) = 0x7FF;
    print_bool("fixed12 <_u ", c <_u d);
    print_bool("fixed12 <_s ", c <_s d);
    cmp(a, b);
    cmp(c, d);
    cmp(0b1, 0b0);
    cmp(0x5, 0x5)
}
