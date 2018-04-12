/* machine mode registers */

/* FIXME: currently we have only those used by riscv-tests. */

bitfield Misa : bits(64) = {
  MXL  : 63 .. 62,

  Z    : 25,
  Y    : 24,
  X    : 23,
  W    : 22,
  V    : 21,
  U    : 20,
  T    : 19,
  S    : 18,
  R    : 17,
  Q    : 16,
  P    : 15,
  O    : 14,
  N    : 13,
  M    : 12,
  L    : 11,
  K    : 10,
  J    : 9,
  I    : 8,
  H    : 7,
  G    : 6,
  F    : 5,
  E    : 4,
  D    : 3,
  C    : 2,
  B    : 1,
  A    : 0
}
register misa : Misa

bitfield Mstatus : bits(64) = {
  SD   : 63,

  SXL  : 35 .. 34,
  UXL  : 33 .. 32,

  TSR  : 22,
  TW   : 21,
  TVM  : 20,
  MXR  : 19,
  SUM  : 18,
  MPRV : 17,

  XS   : 16 .. 15,
  FS   : 14 .. 13,

  MPP  : 12 .. 11,
  SPP  : 8,

  MPIE : 7,
  SPIE : 5,
  UPIE : 4,

  MIE  : 3,
  SIE  : 1,
  UIE  : 0
}
register mstatus : Mstatus

/* interrupt registers */

bitfield Minterrupts : bits(64) = {
  MEI : 11, /* external interrupts */
  SEI : 9,
  UEI : 8,

  MTI : 7,  /* timers interrupts */
  STI : 5,
  UTI : 4,

  MSI : 3,  /* software interrupts */
  SSI : 1,
  USI : 0,

}
register mip     : Minterrupts /* Pending */
register mie     : Minterrupts /* Enabled */
register mideleg : Minterrupts /* Delegation to S-mode */

/* exception registers */

bitfield Medeleg : bits(64) = {
  SAMO_Page_Fault   : 15,
  Load_Page_Fault   : 13,
  Fetch_Page_Fault  : 12,
  MEnvCall          : 10,
  SEnvCall          : 9,
  UEnvCall          : 8,
  SAMO_Access_Fault : 7,
  SAMO_Addr_Align   : 6,
  Load_Access_Fault : 5,
  Load_Addr_Align   : 4,
  Breakpoint        : 3,
  Illegal_Instr     : 2,
  Fetch_Access_Fault: 1,
  Fetch_Addr_Align  : 0
}
register medeleg : Medeleg  /* Delegation to S-mode */

bitfield Mcause : bits(64) = {
  IsInterrupt : 63,
  Cause       : 62 .. 0
}
register mcause : Mcause

bitfield Mtvec : bits(64) = {
  Base : 63 .. 2,
  Mode :  1 .. 0
}
register mtvec : Mtvec  /* Trap Vector */

/* Interpreting the trap-vector address */
function tvec_addr(m : Mtvec, c : Mcause) -> option(xlenbits) = {
  let base : xlenbits = m.Base() @ 0b00;
  match (trapVectorMode_of_bits(m.Mode())) {
    TV_Direct => Some(base),
    TV_Vector => if   mcause.IsInterrupt() == 0b1  /* FIXME: Why not already boolean? */
                 then Some(base + (EXTZ(c.Cause()) << 0b10))
                 else Some(base),
    TV_Reserved => None()
  }
}

/* auxiliary exception registers */
register mepc : xlenbits
register mtval : xlenbits
register mscratch : xlenbits

/* time/cycles */
register mcycle : xlenbits
register mtime : xlenbits
register minstret : xlenbits

/* informational registers */
register mvendorid : xlenbits
register mimpid : xlenbits
register marchid : xlenbits
/* TODO: this should be readonly, and always 0 for now */
register mhartid : xlenbits

/* physical memory protection configuration */
register pmpaddr0 : xlenbits
register pmpcfg0 : xlenbits

/* supervisor mode registers */

bitfield Sstatus : bits(64) = {
  SD   : 63,
  UXL  : 33 .. 32,
  MXR  : 19,
  SUM  : 18,
  XS   : 16 .. 15,
  FS   : 14 .. 13,
  SPP  : 8,
  SPIE : 5,
  UPIE : 4,
  SIE  : 1,
  UIE  : 0
}
/* This is a view, so there is no register defined. */

bitfield Sedeleg : bits(64) = {
  UEnvCall          : 8,
  SAMO_Access_Fault : 7,
  SAMO_Addr_Align   : 6,
  Load_Access_Fault : 5,
  Load_Addr_Align   : 4,
  Breakpoint        : 3,
  Illegal_Instr     : 2,
  Fetch_Access_Fault: 1,
  Fetch_Addr_Align  : 0
}
register sedeleg : Sedeleg

/* TODO: handle views for interrupt delegation */
register sideleg : Minterrupts
register sip     : Minterrupts
register sie     : Minterrupts

bitfield satp64 : bits(64) = {
  Mode : 63 .. 60,
  Asid : 59 .. 44,
  PPN  : 43 .. 0
}

register stvec : Mtvec
register sscratch : xlenbits
register sepc : xlenbits
register scause : Mcause
register stval : xlenbits
register satp : xlenbits

/* instruction control flow */

struct sync_exception = {
  trap : ExceptionType,
  excinfo : option(xlenbits)
}

union ctl_result = {
  CTL_TRAP : sync_exception,
/* TODO:
  CTL_URET,
  CTL_SRET,
*/
  CTL_MRET : unit
}

/* privilege level */

register cur_privilege : Privilege

/* handle exceptional ctl flow by updating nextPC */

function handle_exception_ctl(cur_priv : Privilege, ctl : ctl_result,
                              pc: xlenbits) -> xlenbits =
  /* TODO: check delegation */
  match (cur_priv, ctl) {
    (_, CTL_TRAP(e)) => {
      mepc            = pc;

      mcause->IsInterrupt() = false;
      mcause->Cause()       = EXTZ(exceptionType_to_bits(e.trap));

      mstatus->MPIE() = mstatus.MIE();
      mstatus->MIE()  = false;
      mstatus->MPP()  = privLevel_to_bits(cur_priv);
      cur_privilege   = Machine;

      match (e.trap) {
        E_Fetch_Addr_Align => {
          match (e.excinfo) {
            Some(a) => mtval = a,
            None()  => throw Error_internal_error()
          }
        },
        E_Fetch_Access_Fault => {
          match (e.excinfo) {
            Some(a) => mtval = a,
            None()  => throw Error_internal_error()
          }
        },
        E_Illegal_Instr => {
          match (e.excinfo) {
            Some(a) => mtval = a,
            None()  => throw Error_internal_error()
          }
        },

        E_Breakpoint => not_implemented("breakpoint"),

        E_Load_Addr_Align => {
          match (e.excinfo) {
            Some(a) => mtval = a,
            None()  => throw Error_internal_error()
          }
        },
        E_Load_Access_Fault => {
          match (e.excinfo) {
            Some(a) => mtval = a,
            None()  => throw Error_internal_error()
          }
        },
        E_SAMO_Addr_Align => {
          match (e.excinfo) {
            Some(a) => mtval = a,
            None()  => throw Error_internal_error()
          }
        },
        E_SAMO_Access_Fault => {
          match (e.excinfo) {
            Some(a) => mtval = a,
            None()  => throw Error_internal_error()
          }
        },

        E_U_EnvCall => {
          mtval  = EXTZ(0b0)
        },
        E_S_EnvCall => {
          mtval  = EXTZ(0b0)
        },
        E_M_EnvCall => {
          mtval  = EXTZ(0b0)
        },

        E_Fetch_Page_Fault => {
          match (e.excinfo) {
            Some(a) => mtval = a,
            None()  => throw Error_internal_error()
          }
        },
        E_Load_Page_Fault => {
          match (e.excinfo) {
            Some(a) => mtval = a,
            None()  => throw Error_internal_error()
          }
        },
        E_SAMO_Page_Fault => {
          match (e.excinfo) {
            Some(a) => mtval = a,
            None()  => throw Error_internal_error()
          }
        },
        _ => throw Error_internal_error() /* Don't expect ReservedExc0 etc. here */
      };
      /* TODO: make register read explicit */
      match (tvec_addr(mtvec, mcause)) {
        Some(addr) => addr,
        None()     => throw Error_internal_error()
      }
    },
    (_, CTL_MRET()) => {
      mstatus->MIE()  = mstatus.MPIE();
      mstatus->MPIE() = true;
      cur_privilege   = privLevel_of_bits(mstatus.MPP());
      mstatus->MPP()  = privLevel_to_bits(User);
      mepc
    }
  }

function init_sys () : unit -> unit = {
  cur_privilege = Machine;
  misa->C() = true;
}
