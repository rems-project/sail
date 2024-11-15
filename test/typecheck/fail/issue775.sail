default Order dec
$include <prelude.sail>

struct regidx = { regidx : bits(5) }

scattered union ast

val encdec : ast <-> bits(32)
scattered mapping encdec

union clause ast = UTYPE : (bits(20), regidx)
mapping clause encdec = UTYPE(imm, rd) <-> imm @ rd @ 0b0010111
