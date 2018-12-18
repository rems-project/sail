// "RISC-V Formal Interface - Direct Instruction Injection" support
// For use with https://github.com/CTSRD-CHERI/TestRIG

$define RVFI_DII

bitfield RVFI_DII_Instruction_Packet : bits(64) = {
   padding   : 63 .. 56, // [7]
   rvfi_cmd  : 55 .. 48, // [6] This token is a trace command.  For example, reset device under test.
   rvfi_time : 47 .. 32, // [5 - 4] Time to inject token.  The difference between this and the previous
                         // instruction time gives a delay before injecting this instruction.
                         // This can be ignored for models but gives repeatability for implementations
                         // while shortening counterexamples.
   rvfi_insn : 31 ..  0, // [0 - 3] Instruction word: 32-bit instruction or command. The lower 16-bits
                         // may decode to a 16-bit compressed instruction.
}

register rvfi_instruction : RVFI_DII_Instruction_Packet

val rvfi_set_instr_packet : bits(64) -> unit effect {wreg}

function rvfi_set_instr_packet(p) =
  rvfi_instruction = Mk_RVFI_DII_Instruction_Packet(p)

val rvfi_get_cmd : unit -> bits(8) effect {rreg}

function rvfi_get_cmd () = rvfi_instruction.rvfi_cmd()

val print_instr_packet : bits(64) -> unit

function print_instr_packet(bs) = {
  let p = Mk_RVFI_DII_Instruction_Packet(bs);
  print_bits("command", p.rvfi_cmd());
  print_bits("instruction", p.rvfi_insn())
}

bitfield RVFI_DII_Execution_Packet : bits(704) = {
   rvfi_intr      : 703 .. 696, // [87] Trap handler:            Set for first instruction in trap handler.
   rvfi_halt      : 695 .. 688, // [86] Halt indicator:          Marks the last instruction retired 
                                //                                      before halting execution.
   rvfi_trap      : 687 .. 680, // [85] Trap indicator:          Invalid decode, misaligned access or
                                //                                      jump command to misaligned address.
   rvfi_rd_addr   : 679 .. 672, // [84]      Write register address:  MUST be 0 if not used.
   rvfi_rs2_addr  : 671 .. 664, // [83]                          otherwise set as decoded.
   rvfi_rs1_addr  : 663 .. 656, // [82]      Read register addresses: Can be arbitrary when not used,
   rvfi_mem_wmask : 655 .. 648, // [81]      Write mask:              Indicates valid bytes written. 0 if unused.
   rvfi_mem_rmask : 647 .. 640, // [80]      Read mask:               Indicates valid bytes read. 0 if unused.
   rvfi_mem_wdata : 639 .. 576, // [72 - 79] Write data:              Data written to memory by this command.
   rvfi_mem_rdata : 575 .. 512, // [64 - 71] Read data:               Data read from mem_addr (i.e. before write)
   rvfi_mem_addr  : 511 .. 448, // [56 - 63] Memory access addr:      Points to byte address (aligned if define
                                //                                      is set). *Should* be straightforward.
                                //                                      0 if unused.
   rvfi_rd_wdata  : 447 .. 384, // [48 - 55] Write register value:    MUST be 0 if rd_ is 0.
   rvfi_rs2_data  : 383 .. 320, // [40 - 47]                          above. Must be 0 if register ID is 0.
   rvfi_rs1_data  : 319 .. 256, // [32 - 39] Read register values:    Values as read from registers named
   rvfi_insn      : 255 .. 192, // [24 - 31] Instruction word:        32-bit command value.
   rvfi_pc_wdata  : 191 .. 128, // [16 - 23] PC after instr:          Following PC - either PC + 4 or jump/trap target.
   rvfi_pc_rdata  : 127 ..  64, // [08 - 15] PC before instr:         PC for current instruction
   rvfi_order     :  63 ..   0, // [00 - 07] Instruction number:      INSTRET value after completion.
}

register rvfi_exec : RVFI_DII_Execution_Packet

val rvfi_zero_exec_packet : unit -> unit effect {wreg}

function rvfi_zero_exec_packet () =
  rvfi_exec = Mk_RVFI_DII_Execution_Packet(zero_extend(0b0,704))

val rvfi_halt_exec_packet : unit -> unit effect {wreg}

function rvfi_halt_exec_packet () =
  rvfi_exec->rvfi_halt() = 0x01

val rvfi_get_exec_packet : unit -> bits(704) effect {rreg}

function rvfi_get_exec_packet() = rvfi_exec.bits()

val print_rvfi_exec : unit -> unit effect {rreg}

function print_rvfi_exec () = {
  print_bits("rvfi_intr     : ", rvfi_exec.rvfi_intr());
  print_bits("rvfi_halt     : ", rvfi_exec.rvfi_halt());
  print_bits("rvfi_trap     : ", rvfi_exec.rvfi_trap());
  print_bits("rvfi_rd_addr  : ", rvfi_exec.rvfi_rd_addr());
  print_bits("rvfi_rs2_addr : ", rvfi_exec.rvfi_rs2_addr());
  print_bits("rvfi_rs1_addr : ", rvfi_exec.rvfi_rs1_addr());
  print_bits("rvfi_mem_wmask: ", rvfi_exec.rvfi_mem_wmask());
  print_bits("rvfi_mem_rmask: ", rvfi_exec.rvfi_mem_rmask());
  print_bits("rvfi_mem_wdata: ", rvfi_exec.rvfi_mem_wdata());
  print_bits("rvfi_mem_rdata: ", rvfi_exec.rvfi_mem_rdata());
  print_bits("rvfi_mem_addr : ", rvfi_exec.rvfi_mem_addr());
  print_bits("rvfi_rd_wdata : ", rvfi_exec.rvfi_rd_wdata());
  print_bits("rvfi_rs2_data : ", rvfi_exec.rvfi_rs2_data());
  print_bits("rvfi_rs1_data : ", rvfi_exec.rvfi_rs1_data());
  print_bits("rvfi_insn     : ", rvfi_exec.rvfi_insn());
  print_bits("rvfi_pc_wdata : ", rvfi_exec.rvfi_pc_wdata());
  print_bits("rvfi_pc_rdata : ", rvfi_exec.rvfi_pc_rdata());
  print_bits("rvfi_order    : ", rvfi_exec.rvfi_order());
}
