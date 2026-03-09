default Order dec
$include <prelude.sail>

/*type reg = {'n, 0 <= 'n < 16. int('n)}*/
type reg = range(0,15)

union instr = {
  Mov : {'d, 'd in {8,16}. (int('d), reg, bits('d))}
}

register regs : vector(16,dec,bits(32))

val exec : instr -> unit effect {wreg}

function exec(Mov(sz,r,imm)) =
  regs[r] = sail_zero_extend(imm,32)

val decode : bits(32) -> instr

function decode(0x0000 @ (x : bits(16))) = Mov(16,0,x)
and      decode(0x10000 @ (r : bits(4)) @ (x : bits(8))) = Mov(8, unsigned(r), x)

/* Versions that construct/match the tuple separately from the variant.
   Not currently supported.
val exec2 : instr -> unit effect {wreg}

function exec2(Mov(tuple)) =
  let (sz,r,imm) = tuple in
  regs[r] = sail_zero_extend(imm,32)

val decode2 : bits(32) -> instr

function decode2(0x0000 @ (x : bits(16))) =
  let tup : {'d, 'd in {8,16}. (int('d), reg, bits('d))} = (16,0,x) in
  Mov(tup)
and      decode2(0x10000 @ (r : bits(4)) @ (x : bits(8))) = Mov(8, unsigned(r), x)
*/
