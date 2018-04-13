/* machine mode registers */

/* privilege level */

register cur_privilege : Privilege

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

function legalize_misa(m : Misa, v : xlenbits) -> Misa =
  /* Ignore all writes for now. */
  m

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

function legalize_mstatus(o : Mstatus, v : xlenbits) -> Mstatus = {
  let m : Mstatus = Mk_Mstatus(v);
  /* We don't have any extension context yet. */
  let m = update_XS(m, extStatus_to_bits(Off));
  let m = update_SD(m, extStatus_of_bits(m.FS()) == Dirty
                     | extStatus_of_bits(m.XS()) == Dirty);
  /* For now, we don't allow SXL and UXL to be changed, for Spike compatibility. */
  let m = update_SXL(m, o.SXL());
  let m = update_UXL(m, o.UXL());
  /* Hardwired to zero in the absence of 'N'. */
  let m = update_UPIE(m, false);
  let m = update_UIE(m, false);
  m
}

/* machine state utilities */

function cur_Architecture() -> Architecture = {
  let a : arch_xlen =
    match (cur_privilege) {
      Machine => misa.MXL(),
      Supervisor => mstatus.SXL(),
      User => mstatus.UXL()
    };
  match architecture(a) {
    Some(a) => a,
    None()  => internal_error("Invalid current architecture")
  }
}

function in32BitMode() -> bool = {
  cur_Architecture() == RV32
}

function haveAtomics() -> bool = { misa.A() == true }
function haveRVC()     -> bool = { misa.C() == true }
function haveMulDiv()  -> bool = { misa.M() == true }
function haveFP()      -> bool = { misa.F() == true | misa.D() == true }

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

function legalize_mip(o : Minterrupts, v : xlenbits) -> Minterrupts = {
  /* The only writable bits are the S-mode bits, and with the 'N'
   * extension, the U-mode bits. */
  let v = Mk_Minterrupts(v);
  let m = update_SEI(o, v.SEI());
  let m = update_STI(m, v.STI());
  let m = update_SSI(m, v.SSI());
  m
}

function legalize_mie(o : Minterrupts, v : xlenbits) -> Minterrupts = {
  let v = Mk_Minterrupts(v);
  let m = update_MEI(o, v.MEI());
  let m = update_MTI(m, v.MTI());
  let m = update_MSI(m, v.MSI());
  let m = update_SEI(m, v.SEI());
  let m = update_STI(m, v.STI());
  let m = update_SSI(m, v.SSI());
  /* The U-mode bits will be modified if we have the 'N' extension. */
  m
}

function legalize_mideleg(o : Minterrupts, v : xlenbits) -> Minterrupts = {
  Mk_Minterrupts(v)
}

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

function legalize_medeleg(o : Medeleg, v : xlenbits) -> Medeleg = {
  let m = Mk_Medeleg(v);
  /* M-EnvCalls delegation is not supported */
  let m = update_MEnvCall(m, false);
  m
}

bitfield Mtvec : bits(64) = {
  Base : 63 .. 2,
  Mode :  1 .. 0
}
register mtvec : Mtvec  /* Trap Vector */

function legalize_tvec(o : Mtvec, v : xlenbits) -> Mtvec = {
 let v = Mk_Mtvec(v);
 match (trapVectorMode_of_bits(v.Mode())) {
   TV_Direct => v,
   TV_Vector => v,
   _         => update_Mode(v, o.Mode())
 }
}

bitfield Mcause : bits(64) = {
  IsInterrupt : 63,
  Cause       : 62 .. 0
}
register mcause : Mcause

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

function legalize_xepc(v : xlenbits) -> xlenbits = {
  v & EXTS(if haveRVC() then 0b110 else 0b100)
}

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
function lower_mstatus(m : Mstatus) -> Sstatus = {
  let s = Mk_Sstatus(EXTZ(0b0));
  let s = update_SD(s, m.SD());
  let s = update_UXL(s, m.UXL());
  let s = update_MXR(s, m.MXR());
  let s = update_SUM(s, m.SUM());
  let s = update_XS(s, m.XS());
  let s = update_FS(s, m.FS());
  let s = update_SPP(s, m.SPP());
  let s = update_SPIE(s, m.SPIE());
  let s = update_UPIE(s, m.UPIE());
  let s = update_SIE(s, m.SIE());
  let s = update_UIE(s, m.UIE());
  s
}

function lift_sstatus(m : Mstatus, s : Sstatus) -> Mstatus = {
  let m = update_SD(m, s.SD());
  let m = update_UXL(m, s.UXL());
  let m = update_MXR(m, s.MXR());
  let m = update_SUM(m, s.SUM());
  let m = update_XS(m, s.XS());
  let m = update_FS(m, s.FS());
  let m = update_SPP(m, s.SPP());
  let m = update_SPIE(m, s.SPIE());
  let m = update_UPIE(m, s.UPIE());
  let m = update_SIE(m, s.SIE());
  let m = update_UIE(m, s.UIE());
  m
}

function legalize_sstatus(m : Mstatus, v : xlenbits) -> Mstatus = {
  lift_sstatus(m, Mk_Sstatus(v))
}

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

function legalize_sedeleg(s : Sedeleg, v : xlenbits) -> Sedeleg = {
  Mk_Sedeleg(EXTZ(v[8..0]))
}

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

/* csr access control */

function csrAccess(csr : csreg) -> csrRW = csr[11..10]
function csrPriv(csr : csreg) -> priv_level = csr[9..8]

function is_CSR_defined (csr : bits(12), p : Privilege) -> bool =
  match (csr) {
    /* machine mode: informational */
    0xf11 => p == Machine, // mvendorid
    0xf12 => p == Machine, // marchdid
    0xf13 => p == Machine, // mimpid
    0xf14 => p == Machine, // mhartid
    /* machine mode: trap setup */
    0x300 => p == Machine, // mstatus
    0x301 => p == Machine, // misa
    0x302 => p == Machine, // medeleg
    0x303 => p == Machine, // mideleg
    0x304 => p == Machine, // mie
    0x305 => p == Machine, // mtvec
    0x306 => p == Machine, // mcounteren
    /* machine mode: trap handling */
    0x340 => p == Machine, // mscratch
    0x341 => p == Machine, // mepc
    0x342 => p == Machine, // mcause
    0x343 => p == Machine, // mtval
    0x344 => p == Machine, // mip

    /* supervisor mode: trap setup */
    0x100 => p == Machine | p == Supervisor, // sstatus
    0x102 => p == Machine | p == Supervisor, // sedeleg
    0x103 => p == Machine | p == Supervisor, // sideleg
    0x104 => p == Machine | p == Supervisor, // sie
    0x105 => p == Machine | p == Supervisor, // stvec
    0x106 => p == Machine | p == Supervisor, // scounteren

    /* supervisor mode: trap handling */
    0x140 => p == Machine | p == Supervisor, // sscratch
    0x141 => p == Machine | p == Supervisor, // sepc
    0x142 => p == Machine | p == Supervisor, // scause
    0x143 => p == Machine | p == Supervisor, // stval
    0x144 => p == Machine | p == Supervisor, // sip

    /* supervisor mode: address translation */
    0x180 => p == Machine | p == Supervisor, // satp

    _     => false
  }

val check_CSR_access : (csrRW, priv_level, Privilege, bool) -> bool
function check_CSR_access(csrrw, csrpr, p, isWrite) =
    (~ (isWrite == true & csrrw == 0b11))  /* read/write */
  & (privLevel_to_bits(p) >=_u csrpr)      /* privilege */

function check_TVM_SATP(csr : csreg, p : Privilege) -> bool =
  ~ (csr == 0x180 & p == Supervisor & mstatus.TVM() == true)

function check_CSR(csr : csreg, p : Privilege, isWrite : bool) -> bool =
    is_CSR_defined(csr, p)
  & check_CSR_access(csrAccess(csr), csrPriv(csr), p, isWrite)
  & check_TVM_SATP(csr, p)

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
