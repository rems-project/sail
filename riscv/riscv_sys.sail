/* exception codes */

enum Interrupts = {
  UserSWIntr,
  SupervisorSWIntr,
  ReservedIntr0,
  MachineSWIntr,

  UserTimerIntr,
  SupervisorTimerIntr,
  ReservedIntr1,
  MachineTimerIntr,

  UserExternalIntr,
  SupervisorExternalIntr,
  ReservedIntr2,
  MachineExternalIntr
}

enum ExceptionCode = {
  Misaligned_Fetch,
  Fetch_Access,
  Illegal_Instr,
  Breakpoint,
  Misaligned_Load,

  Load_Access,
  Misaligned_Store,
  Store_Access,

  User_ECall,
  Supervisor_ECall,
  ReservedExc0,
  Machine_ECall,

  Fetch_PageFault,
  Load_PageFault,
  ReservedExc1,
  Store_PageFault
}

/* machine mode registers */

/* FIXME: currently we have only those used by riscv-tests. */

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

bitfield Mip : bits(64) = {
  MEIP : 11,
  SEIP : 9,
  UEIP : 8,

  MTIP : 7,
  STIP : 5,
  UTIP : 4,

  MSIP : 3,
  SSIP : 1,
  USIP : 0,

}
register mip : Mip

bitfield Mie : bits(64) = {
  MEIE : 11,
  SEIE : 9,
  UEIE : 8,

  MTIE : 7,
  STIE : 5,
  UTIE : 4,

  MSIE : 3,
  SSIE : 1,
  USIE : 0,

}
register mie : Mie

bitfield Mideleg : bits(64) = {
  MEID : 6,
  SEID : 5,
  UEID : 4,

  MTID : 6,
  STID : 5,
  UTID : 4,

  MSID : 3,
  SSID : 1,
  USID : 0
}
register mideleg : Mideleg

bitfield Medeleg : bits(64) = {
  STORE_PAGE_FAULT  : 15,
  LOAD_PAGE_FAULT   : 13,
  FETCH_PAGE_FAULT  : 12,
  MACHINE_ECALL     : 10,
  SUPERVISOR_ECALL  : 9,
  USER_ECALL        : 8,
  STORE_ACCESS      : 7,
  MISALIGNED_STORE  : 6,
  LOAD_ACCESS       : 5,
  MISALIGNED_LOAD   : 4,
  BREAKPOINT        : 3,
  ILLEGAL_INSTR     : 2,
  FETCH_ACCESS      : 1,
  MISALIGNED_FETCH  : 0
}
register medeleg : Medeleg

/* exception registers */
register mepc : regval
register mtval : regval
register mtvec : regval
register mscratch : regval

/* other registers */

register pmpaddr0 : regval
register pmpcfg0 : regval
/* TODO: this should be readonly, and always 0 for now */
register mhartid : regval

/* instruction control flow */

struct sync_exception = {
  trap : ExceptionCode,
  badaddr : option(regval)
}

union ctl_result = {
  CTL_TRAP : sync_exception,
/* TODO:
  CTL_URET,
  CTL_SRET,
*/
  CTL_MRET
}

/* privilege level */

union privilege = {
  MACHINE,
  USER
}
register cur_privilege : privilege

function priv_to_bits(p : privilege) -> bits(2) =
  match (p) {
    USER    => 0b00,
    MACHINE => 0b11
  }
function bits_to_priv(b : bits(2)) -> privilege =
  match (b) {
    0b00    => USER,
    0b11    => MACHINE
  }

/* handle exceptional ctl flow by updating nextPC */

function handle_exception_ctl(cur_priv : privilege, ctl : ctl_result,
                              pc: regval) -> regval =
  /* TODO: check delegation */
  match (cur_priv, ctl) {
    (_, CTL_TRAP(e)) => {
      mepc            = pc;
      mcause          = e.trap;

      mstatus->MPIE() = mstatus.MIE();
      mstatus->MIE()  = false;
      mstatus->MPP()  = priv_to_bits(cur_priv);
      cur_privilege   = MACHINE;

      match (e.trap) {
        Misaligned_Fetch => {
          match (e.badaddr) {
            Some(a) => mtval = a,
            None    => throw(Error_internal_error)
          }
        },
        Fetch_Access => {
          match (e.badaddr) {
            Some(a) => mtval = a,
            None    => throw(Error_internal_error)
          }
        },
        Illegal_Instr => {
          match (e.badaddr) {
            Some(a) => mtval = a,
            None    => throw(Error_internal_error)
          }
        },

        Breakpoint => not_implemented("breakpoint"),

        Misaligned_Load => {
          match (e.badaddr) {
            Some(a) => mtval = a,
            None    => throw(Error_internal_error)
          }
        },
        Load_Access => {
          match (e.badaddr) {
            Some(a) => mtval = a,
            None    => throw(Error_internal_error)
          }
        },
        Misaligned_Store => {
          match (e.badaddr) {
            Some(a) => mtval = a,
            None    => throw(Error_internal_error)
          }
        },
        Store_Access => {
          match (e.badaddr) {
            Some(a) => mtval = a,
            None    => throw(Error_internal_error)
          }
        },

        User_ECall => {
          mtval  = EXTZ(0b0)
        },
        Supervisor_ECall => {
          mtval  = EXTZ(0b0)
        },
        Machine_ECall => {
          mtval  = EXTZ(0b0)
        },

        Fetch_PageFault => {
          match (e.badaddr) {
            Some(a) => mtval = a,
            None    => throw(Error_internal_error)
          }
        },
        Load_PageFault => {
          match (e.badaddr) {
            Some(a) => mtval = a,
            None    => throw(Error_internal_error)
          }
        },
        Store_PageFault => {
          match (e.badaddr) {
            Some(a) => mtval = a,
            None    => throw(Error_internal_error)
          }
        }
      };
      /* TODO: make register read explicit */
      mtvec
    },
    (_, CTL_MRET) => {
      mstatus->MIE()  = mstatus.MPIE();
      mstatus->MPIE() = true;
      cur_privilege   = bits_to_priv(mstatus.MPP());
      mstatus->MPP()  = priv_to_bits(USER);
      mepc
    }
  }
