/* From RISC-V */

default Order dec
$include <prelude.sail>
$include <string.sail>
$include <mapping.sail>

enum word_width = {BYTE, HALF, WORD, DOUBLE}

mapping size_mnemonic : word_width <-> string = {
  BYTE   <-> "b",
  HALF   <-> "h",
  WORD   <-> "w",
  DOUBLE <-> "d"
}

