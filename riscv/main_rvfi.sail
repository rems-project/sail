// Alternative fetch and step for RVFI DII mode.

val rvfi_fetch : unit -> FetchResult effect {escape, rmem, rreg, wmv, wreg}

function rvfi_fetch() = {
  let i = rvfi_instruction.rvfi_insn();
  rvfi_exec->rvfi_order() = minstret;
  rvfi_exec->rvfi_pc_rdata() = PC;
  rvfi_exec->rvfi_insn() = zero_extend(i,64);
  /* TODO: should we write these even if they're not really registers? */
  rvfi_exec->rvfi_rs1_data() = X(i[19 .. 15]);
  rvfi_exec->rvfi_rs2_data() = X(i[24 .. 20]);
  rvfi_exec->rvfi_rs1_addr() = zero_extend(i[19 .. 15],8);
  rvfi_exec->rvfi_rs2_addr() = zero_extend(i[24 .. 20],8);
  if (i[1 .. 0] == 0b11)
  then F_Base(i)
  else F_RVC(i[15 .. 0])
}

// This should be kept in sync with the normal step - at the moment the only
// changes are to replace fetch by rvfi_fetch and record the next PC.

/* returns whether to increment the step count in the trace */
val rvfi_step : int -> bool effect {barr, eamem, escape, exmem, rmem, rreg, wmv, wreg}
function rvfi_step(step_no) = {
  minstret_written = false;     /* see note for minstret */
  let (retired, stepped) : (bool, bool) =
    match curInterrupt(cur_privilege, mip, mie, mideleg) {
      Some(intr, priv) => {
        print_bits("Handling interrupt: ", intr);
        handle_interrupt(intr, priv);
        (false, false)
      },
      None() => {
        match rvfi_fetch() {
          F_Error(e, addr) => {
            handle_mem_exception(addr, e);
            (false, false)
          },
          F_RVC(h) => {
            match decodeCompressed(h) {
              None() => {
                print("[" ^ string_of_int(step_no) ^ "] [" ^ cur_privilege ^ "]: " ^ BitStr(PC) ^ " (" ^ BitStr(h) ^ ") <no-decode>");
                instbits = EXTZ(h);
                handle_illegal();
                (false, true)
              },
              Some(ast) => {
                print("[" ^ string_of_int(step_no) ^ "] [" ^ cur_privilege ^ "]: " ^ BitStr(PC) ^ " (" ^ BitStr(h) ^ ") " ^ ast);
                nextPC = PC + 2;
                (execute(ast), true)
              }
            }
          },
          F_Base(w) => {
            match decode(w) {
              None() => {
                print("[" ^ string_of_int(step_no) ^ "] [" ^ cur_privilege ^ "]: " ^ BitStr(PC) ^ " (" ^ BitStr(w) ^ ") <no-decode>");
                instbits = EXTZ(w);
                handle_illegal();
                (false, true)
              },
              Some(ast) => {
                print("[" ^ string_of_int(step_no) ^ "] [" ^ cur_privilege ^ "]: " ^ BitStr(PC) ^ " (" ^ BitStr(w) ^ ") " ^ ast);
                nextPC = PC + 4;
                (execute(ast), true)
              }
            }
          }
        }
      }
    };
  PC = nextPC;
  rvfi_exec->rvfi_pc_wdata() = PC;
//print_rvfi_exec();
  if retired then retire_instruction();
  stepped
}


/* Dummy to make sure that sail doesn't throw functions away */

val main : unit -> unit effect {barr, eamem, escape, exmem, rmem, rreg, wmv, wreg}

function main () = {

  // PC = __GetSlice_int(64, elf_entry(), 0);
  rvfi_set_instr_packet(0x0000000000000000);
  print_bits("", rvfi_get_cmd());
  let _ = rvfi_step(0);
  rvfi_zero_exec_packet();
  rvfi_halt_exec_packet();
  let _ = rvfi_get_exec_packet();
  PC = zero_extend(0x1000, 64);
  print_bits("PC = ", PC);
  try {
    init_platform();
    init_sys();
    loop()
  } catch {
    Error_not_implemented(s) => print_string("Error: Not implemented: ", s),
    Error_internal_error() => print("Error: internal error")
  }
}
