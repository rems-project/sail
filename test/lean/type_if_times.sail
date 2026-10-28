default Order dec

$include <prelude.sail>

// Non-atomic operands of type-level arithmetic must be parenthesised in
// the Lean output: Lean parses `if c then 8 else 4 * 8` as
// `if c then 8 else (4 * 8)`, and `3 * flen / 24` as `(3 * flen) / 24`.
// (The pattern is from sail-riscv, where `flen_bytes` depends on whether
// the D extension is enabled.)

type d_supported : Bool = true

type flen_bytes : Int = if d_supported then 8 else 4
type flen       : Int = flen_bytes * 8
type flenbits         = bits(flen)

type flen_plus  : Int = 8 + flen_bytes
type flen_div   : Int = 3 * div(flen, 24)

register F : flenbits

val read_f : unit -> bits(64)
function read_f() = F

val write_f : bits(64) -> unit
function write_f(v) = F = v

val div_width : bits(flen_div) -> bits(6)
function div_width(v) = v

val plus_width : bits(flen_plus) -> bits(16)
function plus_width(v) = v
