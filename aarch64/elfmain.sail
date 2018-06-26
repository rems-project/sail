$include <elf.sail>

val read_register = "reg_deref" : forall ('a : Type). register('a) -> 'a effect {rreg}

//             EL1 physical        EL2 physical        EL3 physical        EL1 virtual,       EL2 virtual
let CNT_CVAL = [ref CNTP_CVAL_EL0, ref CNTHP_CVAL_EL2, ref CNTPS_CVAL_EL1, ref CNTV_CVAL_EL0, ref CNTHV_CVAL_EL2]
let CNT_TVAL = [ref CNTP_TVAL_EL0, ref CNTHP_TVAL_EL2, ref CNTPS_TVAL_EL1, ref CNTV_TVAL_EL0, ref CNTHV_TVAL_EL2]
let CNT_CTL  = [ref CNTP_CTL_EL0,  ref CNTHP_CTL_EL2,  ref CNTPS_CTL_EL1,  ref CNTV_CTL_EL0,  ref CNTHV_CTL_EL2 ]
let CNT_CTL  = [ref CNTP_CTL_EL0,  ref CNTHP_CTL_EL2,  ref CNTPS_CTL_EL1,  ref CNTV_CTL_EL0,  ref CNTHV_CTL_EL2 ]
let CNT_IRQ  = [0x0000_000d,       0x0000_000a,        0x0000_03ff,        0x0000_000b,       0x0000_03ff       ]
//                                                     No IRQ                                 No IRQ?

// SGI Interrupts are 0-15, PPI interrupts are 16-31, so SPI interrupts have an offset of 32.
let SPI_OFFSET = 32

// Simple top level fetch and execute loop.
val fetch_and_execute : unit -> unit effect {escape, undef, wreg, rreg, rmem, wmem}

function fetch_and_execute () = {
  var cycle_counter : int = 0;
  while true do {
    cycle_counter = cycle_counter + 1;
    try {
      // Increment the counter
      CNTPCT_EL0 = CNTPCT_EL0 + 1;
      CNTVCT_EL0 = CNTPCT_EL0 - CNTVOFF_EL2;

      // Timer value view for each timer
      foreach (timer from 0 to 4) {
        let TVAL = CNT_TVAL[timer];
        let nextTVAL = read_register(TVAL) - 1;
        (*TVAL) = nextTVAL;

        if nextTVAL == 0x0000_0000 then {
	  _IRQPending = true;
          AArch64_TakePhysicalIRQException()
        }
      };

      // Handle the Kernel event stream, if enabled by CNTKCTL_EL1[2].
      if CNTKCTL_EL1[2] == bitone then {
        let mask = LSL(ZeroExtend(0x1, 64), UInt(CNTKCTL_EL1[7 .. 4]));

        // Trigger event stream on either rising bit (0-1, bitzero) or falling (1-0, bitone)
        let trigger : bool = if CNTKCTL_EL1[3] == bitzero then {
          ((CNTVCT_EL0 - 1) & mask) == Zeros() & (CNTVCT_EL0 & mask) != Zeros()
        } else {
          ((CNTVCT_EL0 - 1) & mask) != Zeros() & (CNTVCT_EL0 & mask) == Zeros()
        };

        if trigger & PSTATE.I == bitzero then {
	  _IRQPending = true;
          AArch64_TakePhysicalIRQException()
        }
      };

      // Handle the Hypervisor event stream, if enabled by CNTHCTL_EL2[2].
      if CNTHCTL_EL2[2] == bitone then {
	let mask = LSL(ZeroExtend(0x1, 64), UInt(CNTHCTL_EL2[7 .. 4]));

        // Trigger event stream on either rising bit (0-1, bitzero) or falling (1-0, bitone)
        let trigger : bool = if CNTHCTL_EL2[3] == bitzero then {
          ((CNTPCT_EL0 - 1) & mask) == Zeros() & (CNTPCT_EL0 & mask) != Zeros()
        } else {
          ((CNTPCT_EL0 - 1) & mask) != Zeros() & (CNTPCT_EL0 & mask) == Zeros()
        };

	if trigger & PSTATE.I == bitzero then {
	  prerr("[Clock] Tick\n");
	  _IRQPending = true;
          AArch64_TakePhysicalIRQException()
        }
      };

      var prevEL = PSTATE.EL;
      var prevI = PSTATE.I;

      // Store the old values of the Counter-timer Kernel/Hypervisor Control
      // registers, as we want to figure out when they changes.
      var prevCNTKCTL_EL1 = CNTKCTL_EL1;
      var prevCNTHCTL_EL2 = CNTHCTL_EL2;

      if ~(__Sleeping()) then {

          // Check for pending interrupts
          var interrupt_req : InterruptReq = undefined;
          interrupt_req.take_SE  = true; interrupt_req.take_vSE  = true;
          interrupt_req.take_IRQ = true; interrupt_req.take_vIRQ = true;
          interrupt_req.take_FIQ = true; interrupt_req.take_vFIQ = true;
          if TakePendingInterrupts(interrupt_req) then {
              print("Pending interrupt taken\n");
          } else {
              var ok = false;
              try {
                  __currentInstr = __fetchA64();
                  ok = true;
              } catch {
                  Error_ExceptionTaken() => {
                    print(concat_str("Exception taken during IFetch from PC=", concat_str(HexStr(UInt(aget_PC())), "\n")));
                  },
                  _ => {
                    print("Exiting due to unhandled exception during fetch\n");
                    exit()
                  }
              };
              if ok then {
                  try {
                      ok = false;
                      __PC_changed = false;
                      ShouldAdvanceIT = (PSTATE.nRW == [bitone]) & (PSTATE.T == [bitone]);
                      decode(__currentInstr);
                      if ~(__PC_changed) then _PC = _PC + 4 else ();
                      if ShouldAdvanceIT then AArch32_ITAdvance() else ();
                      SSAdvance();
                      __UpdateSystemCounter(); // should this happen even if sleeping?
                      ok = true;
                  } catch {
                      Error_See(_)              => UndefinedFault(),
                      Error_ReservedEncoding(_) => UndefinedFault(),
                      Error_Undefined()         => UndefinedFault(),
                      Error_ExceptionTaken() => {
                        print(concat_str("Exception taken during Decode/Execute from PC=", concat_str(HexStr(UInt(aget_PC())), "\n")));
                      },
                      _ => {
                        print("Exiting due to unhandled exception during decode/execute\n");
                        exit()
                      }
                  }
              };
              if ~(ok) then {
                  print(concat_str("Yoiks: something went wrong at ", concat_str(DecStr(cycle_counter), "\n")));
              }
          }
      };

      // We want to keep track of what exception level we are in for debugging purposes.
      if UInt(prevEL) > UInt(PSTATE.EL) then {
        prerr_bits("[Sail] Exception level dropped to: ", PSTATE.EL)
      };
      if prevI != PSTATE.I then {
	prerr_bits("[Sail] PSTATE.I changed to: ", PSTATE.I);
      };
      if prevCNTKCTL_EL1 != CNTKCTL_EL1 then {
        prerr_bits("[Clock] CNTKCTL_EL1 changed to ", CNTKCTL_EL1);
      };
      if prevCNTHCTL_EL2 != CNTHCTL_EL2 then {
        prerr_bits("[Clock] CNTHCTL_EL2 changed to ", CNTHCTL_EL2);
      }

    } catch {
      Error_See(str) if str == "HINT" => (),
      Error_ExceptionTaken(_) => {
	// enable_tracing()
        ()
      },
      _ => {
        prerr("Exiting due to unhandled exception\n");
        exit()
      }
    };
    __EndCycle()
  }
}

let COLD_RESET : bool = true

val "load_raw" : (bits(64), string) -> unit

val init : unit -> unit effect {escape, undef, rreg, wreg}

function init() = {
  __currentInstrLength = 4;
  TakeReset(COLD_RESET);
  _PC = CFG_RVBAR;
}

val main : unit -> unit effect {escape, undef, wreg, rreg, rmem, wmem}

function main() = {
  init();
  fetch_and_execute()
}
