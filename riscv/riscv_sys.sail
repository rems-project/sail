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
register mepc : xlenbits
register mtval : xlenbits
register mtvec : xlenbits
register mcause : xlenbits
register mscratch : xlenbits

/* other registers */

register pmpaddr0 : xlenbits
register pmpcfg0 : xlenbits
/* TODO: this should be readonly, and always 0 for now */
register mhartid : xlenbits

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
      mcause          = EXTZ(exceptionType_to_bits(e.trap));

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
      mtvec
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
