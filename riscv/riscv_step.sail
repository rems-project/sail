union FetchResult = {
  F_Base : word,                       /* Base ISA */
  F_RVC : half,                        /* Compressed ISA */
  F_Error : (ExceptionType, xlenbits)  /* exception and PC */
}

function isRVC(h : half) -> bool =
 ~ (h[1 .. 0] == 0b11)

val fetch : unit -> FetchResult effect {escape, rmem, rreg, wmv, wreg}
function fetch() -> FetchResult = {
  /* check for legal PC */
  if (PC[0] != 0b0 | (PC[1] != 0b0 & (~ (haveRVC()))))
  then F_Error(E_Fetch_Addr_Align, PC)
  else match translateAddr(PC, Execute, Instruction) {
    TR_Failure(e)  => F_Error(e, PC),
    TR_Address(ppclo) => {
      /* split instruction fetch into 16-bit granules to handle RVC, as
       * well as to generate precise fault addresses in any fetch
       * exceptions.
       */
      match checked_mem_read(Instruction, ppclo, 2) {
        MemException(e) => F_Error(E_Fetch_Access_Fault, PC),
        MemValue(ilo) => {
          if isRVC(ilo) then F_RVC(ilo)
          else {
            PChi : xlenbits = PC + 2;
            match translateAddr(PChi, Execute, Instruction) {
              TR_Failure(e) => F_Error(e, PChi),
              TR_Address(ppchi) => {
                match checked_mem_read(Instruction, ppchi, 2) {
                  MemException(e) => F_Error(E_Fetch_Access_Fault, PChi),
                  MemValue(ihi) => F_Base(append(ihi, ilo))
                }
              }
            }
          }
        }
      }
    }
  }
}

/* returns whether an instruction was executed */
val step : unit -> bool effect {barr, eamem, escape, exmem, rmem, rreg, wmv, wreg}
function step() = {
  match curInterrupt(mip, mie, mideleg) {
    Some(intr, priv) => {
      print_bits("Handling interrupt: ", intr);
      handle_interrupt(intr, priv);
      false
    },
    None() => {
      print_bits("PC: ", PC);
      match fetch() {
        F_Error(e, addr) => {
          handle_mem_exception(addr, e);
          false
        },
        F_RVC(h) => {
          match decodeCompressed(h) {
            None() => {
              print(BitStr(h) ^ " :  <no-decode>");
              handle_decode_exception(EXTZ(h));
              false
            },
            Some(ast) => {
              print(BitStr(h) ^ " :  " ^ ast);
              nextPC = PC + 2;
              execute(ast);
              true
            }
          }
        },
        F_Base(w) => {
          match decode(w) {
            None() => {
              print(BitStr(w) ^ " :  <no-decode>");
              handle_decode_exception(EXTZ(w));
              false
            },
            Some(ast) => {
              print(BitStr(w) ^ " :  " ^ ast);
              nextPC = PC + 4;
              execute(ast);
              true
            }
          }
        }
      }
    }
  }
}
