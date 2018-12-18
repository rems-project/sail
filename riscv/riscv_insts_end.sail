/* End definitions */
end ast
end execute
end assembly
end encdec
end encdec_compressed

val cast print_insn : ast -> string
function print_insn insn = assembly(insn)

val decode : bits(32) -> option(ast) effect pure
function decode bv = Some(encdec(bv))

val decodeCompressed : bits(16) -> option(ast) effect pure
function decodeCompressed bv = Some(encdec_compressed(bv))
