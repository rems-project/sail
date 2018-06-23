/* PageSize */

let PAGESIZE_BITS = 12

/* PTE attributes, permission checks and updates */

type pteAttribs = bits(8)

bitfield PTE_Bits : pteAttribs = {
  D : 7,
  A : 6,
  G : 5,
  U : 4,
  X : 3,
  W : 2,
  R : 1,
  V : 0
}

function isPTEPtr(p : pteAttribs) -> bool = {
  let a = Mk_PTE_Bits(p);
  a.R() == false & a.W() == false & a.X() == false
}

function isInvalidPTE(p : pteAttribs) -> bool = {
  let a = Mk_PTE_Bits(p);
  a.V() == false | (a.W() == true & a.R() == false)
}

function checkPTEPermission(ac : AccessType, priv : Privilege, mxr : bool, do_sum : bool, p : PTE_Bits) -> bool = {
  match (ac, priv) {
    (Read, User)      => p.U() == true & (p.R() == true | (p.X() == true & mxr)),
    (Write, User)     => p.U() == true & p.W() == true,
    (ReadWrite, User) => p.U() == true & p.W() == true & (p.R() == true | (p.X() == true & mxr)),
    (Execute, User)   => p.U() == true & p.X() == true,

    (Read, Supervisor)      => (p.U() == false | do_sum) & (p.R() == true | (p.X() == true & mxr)),
    (Write, Supervisor)     => (p.U() == false | do_sum) & p.W() == true,
    (ReadWrite, Supervisor) => (p.U() == false | do_sum) & p.W() == true & (p.R() == true | (p.X() == true & mxr)),
    (Execute, Supervisor)   => p.U() == false & p.X() == true,

    (_, Machine)      => internal_error("m-mode mem perm check")
  }
}

function update_PTE_Bits(p : PTE_Bits, a : AccessType) -> option(PTE_Bits) = {
  let update_d = (a == Write | a == ReadWrite) & p.D() == false;
  let update_a = p.A() == false;
  if update_d | update_a then {
    let np = update_A(p, true);
    let np = if update_d then update_D(p, true) else np;
    Some(np)
  } else None()
}

/* failure modes for address-translation/page-table-walks */
enum PTW_Error = {
  PTW_Access,       /* physical memory access error for a PTE */
  PTW_Invalid_PTE,
  PTW_No_Permission,
  PTW_Misaligned,   /* misaligned superpage */
  PTW_PTE_Update    /* PTE update needed but not enabled */
}

/* conversion of these translation/PTW failures into architectural exceptions */
function translationException(a : AccessType, f : PTW_Error) -> ExceptionType =
  match (a, f) {
    (Read, PTW_Access)  => E_Load_Access_Fault,
    (Read, _)           => E_Load_Page_Fault,
    (Write, PTW_Access) => E_SAMO_Access_Fault,
    (Write, _)          => E_SAMO_Page_Fault,
    (Fetch, PTW_Access) => E_Fetch_Access_Fault,
    (Fetch, _)          => E_Fetch_Page_Fault,
    /* atomics never raise Load exceptions */
    (ReadWrite, PTW_Access) => E_SAMO_Access_Fault,
    (ReadWrite, _)          => E_SAMO_Page_Fault
  }

/* address translation: Sv39 */

let SV39_LEVEL_BITS = 9
let SV39_LEVELS = 3
let PTE39_LOG_SIZE = 3
let PTE39_SIZE = 8

type vaddr39 = bits(39)
type paddr39 = bits(56)
type pte39   = xlenbits

bitfield SV39_Vaddr : vaddr39 = {
  VPNi  : 38 .. 12,
  PgOfs : 11 .. 0
}

bitfield SV39_Paddr : paddr39 = {
  PPNi  : 55 .. 12,
  PgOfs : 11 .. 0
}

bitfield SV39_PTE : pte39 = {
  PPNi  : 53 .. 10,
  RSW   : 9 .. 8,
  BITS  : 7 .. 0
}

/* ASID */

type asid64 = bits(16)

function curAsid64() -> asid64 = {
  let satp64 = Mk_Satp64(satp);
  satp64.Asid()
}

/* Current page table base from satp */
function curPTB39() -> paddr39 = {
  let satp64 = Mk_Satp64(satp);
  EXTZ(shiftl(satp64.PPN(), PAGESIZE_BITS))
}

/* Page-table walk. */

union PTW_Result = {
  PTW_Success: (paddr39, SV39_PTE, paddr39, nat, bool),
  PTW_Failure: PTW_Error
}

val walk39 : (vaddr39, AccessType, Privilege, bool, bool, paddr39, nat, bool) -> PTW_Result effect {rmem, escape}
function walk39(vaddr, ac, priv, mxr, do_sum, ptb, level, global) -> PTW_Result = {
  let va = Mk_SV39_Vaddr(vaddr);
  let pt_ofs : paddr39 = shiftl(EXTZ(shiftr(va.VPNi(), (level * SV39_LEVEL_BITS))[(SV39_LEVEL_BITS - 1) .. 0]),
                                PTE39_LOG_SIZE);
  let pte_addr = ptb + pt_ofs;
  /* FIXME: we assume here that walks only access memory-backed addresses. */
  match (phys_mem_read(Data, EXTZ(pte_addr), 8)) {
    MemException(_) => PTW_Failure(PTW_Access),
    MemValue(v) => {
      let pte = Mk_SV39_PTE(v);
      let pbits = pte.BITS();
      let pattr = Mk_PTE_Bits(pbits);
      let is_global = global | (pattr.G() == true);
      if isInvalidPTE(pbits) then {
        PTW_Failure(PTW_Invalid_PTE)
      } else {
        if isPTEPtr(pbits) then {
          if level == 0 then {
            /* last-level PTE contains a pointer instead of a leaf */
            PTW_Failure(PTW_Invalid_PTE)
          } else {
            /* walk down the pointer to the next level */
            walk39(vaddr, ac, priv, mxr, do_sum, EXTZ(shiftl(pte.PPNi(), PAGESIZE_BITS)), level - 1, is_global)
          }
        } else { /* leaf PTE */
          if ~ (checkPTEPermission(ac, priv, mxr, do_sum, pattr)) then {
            PTW_Failure(PTW_No_Permission)
          } else {
            if level > 0 then { /* superpage */
              /* fixme hack: to get a mask of appropriate size */
              let mask = shiftl(pte.PPNi() ^ pte.PPNi() ^ EXTZ(0b1), level * SV39_LEVEL_BITS) - 1;
              if (pte.PPNi() & mask) != EXTZ(0b0) then {
                /* misaligned superpage mapping */
                PTW_Failure(PTW_Misaligned)
              } else {
                /* add the appropriate bits of the VPN to the superpage PPN */
                let ppn = pte.PPNi() | (EXTZ(va.VPNi()) & mask);
                PTW_Success(append(ppn, va.PgOfs()), pte, pte_addr, level, is_global)
              }
            } else {
              /* normal leaf PTE */
              PTW_Success(append(pte.PPNi(), va.PgOfs()), pte, pte_addr, level, is_global)
            }
          }
        }
      }
    }
  }
}

/* idealized TLB to model fence.vm and also speed up simulation. */

struct TLB39_Entry = {
  asid : asid64,
  global : bool,
  vAddr : vaddr39,      /* VPN */
  pAddr : paddr39,      /* PPN */
  vMatchMask : vaddr39, /* matching mask for superpages */
  vAddrMask : vaddr39,  /* selection mask for superpages */
  pte : SV39_PTE,       /* permissions */
  pteAddr : paddr39,    /* for dirty writeback */
  age : xlenbits
}

/* the rreg effect is an artifact of using the cycle counter to provide the age */
val make_TLB39_Entry : (asid64, bool, vaddr39, paddr39, SV39_PTE, nat, paddr39) -> TLB39_Entry effect {rreg}

function make_TLB39_Entry(asid, global, vAddr, pAddr, pte, level, pteAddr) = {
  let shift : nat = PAGESIZE_BITS + (level * SV39_LEVEL_BITS);
  /* fixme hack: use a better idiom for masks */
  let vAddrMask : vaddr39 = shiftl(vAddr ^ vAddr ^ EXTZ(0b1), shift) - 1;
  let vMatchMask : vaddr39 = ~ (vAddrMask);
  struct {
    asid = asid,
    global = global,
    pte = pte,
    pteAddr = pteAddr,
    vAddrMask = vAddrMask,
    vMatchMask = vMatchMask,
    vAddr = vAddr & vMatchMask,
    pAddr = shiftl(shiftr(pAddr, shift), shift),
    age = mcycle
  }
}

/* TODO: make this a vector or array of entries */
let TLBEntries = 32
register tlb39 : option(TLB39_Entry)

val lookupTLB39 : (asid64, vaddr39) -> option((int, TLB39_Entry)) effect {rreg}
function lookupTLB39(asid, vaddr) = {
  match tlb39 {
    None()  => None(),
    Some(e) => if  (e.global | (e.asid == asid))
                 & (e.vAddr == (e.vMatchMask & vaddr))
               then Some((0, e))
               else None()
  }
}

val addToTLB39 : (asid64, vaddr39, paddr39, SV39_PTE, paddr39, nat, bool) -> unit effect {wreg, rreg}
function addToTLB39(asid, vAddr, pAddr, pte, pteAddr, level, global) = {
  let ent = make_TLB39_Entry(asid, global, vAddr, pAddr, pte, level, pteAddr);
  tlb39 = Some(ent)
}

function writeTLB39(idx : int, ent : TLB39_Entry) -> unit =
  tlb39 = Some(ent)

val flushTLB : (option(asid64), option(vaddr39)) -> unit effect {rreg, wreg}
function flushTLB(asid, addr) = {
  let ent : option(TLB39_Entry) =
    match (tlb39, asid, addr) {
      (None(),       _,      _)   => None(),
      (Some(e), None(), None())   => None(),
      (Some(e), None(), Some(a))  => if e.vAddr == (e.vMatchMask & a)
                                     then None() else Some(e),
      (Some(e), Some(i), None())  => if (e.asid == i) & (~ (e.global))
                                     then None() else Some(e),
      (Some(e), Some(i), Some(a)) => if (e.asid == i) & (e.vAddr == (a & e.vMatchMask))
                                        & (~ (e.global))
                                     then None() else Some(e)
    };
  tlb39 = ent
}

union TR39_Result = {
  TR39_Address : paddr39,
  TR39_Failure : PTW_Error
}

val translate39 : (vaddr39, AccessType, Privilege, bool, bool, nat) -> TR39_Result effect {rreg, wreg, wmv, escape, rmem}
function translate39(vAddr, ac, priv, mxr, do_sum, level) = {
  let asid = curAsid64();
  match lookupTLB39(asid, vAddr) {
    Some(idx, ent) => {
      let pteBits = Mk_PTE_Bits(ent.pte.BITS());
      if ~ (checkPTEPermission(ac, priv, mxr, do_sum, pteBits))
      then TR39_Failure(PTW_No_Permission)
      else {
        match update_PTE_Bits(pteBits, ac) {
          None() => TR39_Address(ent.pAddr | EXTZ(vAddr & ent.vAddrMask)),
          Some(pbits) => {
            if ~ (plat_enable_dirty_update ())
            then {
              /* pte needs dirty/accessed update but that is not enabled */
              TR39_Failure(PTW_PTE_Update)
            } else {
              /* update PTE entry and TLB */
              n_ent : TLB39_Entry = ent;
              n_ent.pte = update_BITS(ent.pte, pbits.bits());
              writeTLB39(idx, n_ent);
              /* update page table */
              match checked_mem_write(EXTZ(ent.pteAddr), 8, ent.pte.bits()) {
                MemValue(_) => (),
                MemException(e) => internal_error("invalid physical address in TLB")
              };
              TR39_Address(ent.pAddr | EXTZ(vAddr & ent.vAddrMask))
            }
          }
        }
      }
    },
    None() => {
      match walk39(vAddr, ac, priv, mxr, do_sum, curPTB39(), level, false) {
        PTW_Failure(f) => TR39_Failure(f),
        PTW_Success(pAddr, pte, pteAddr, level, global) => {
          match update_PTE_Bits(Mk_PTE_Bits(pte.BITS()), ac) {
            None() => {
              addToTLB39(asid, vAddr, pAddr, pte, pteAddr, level, global);
              TR39_Address(pAddr)
            },
            Some(pbits) =>
              if ~ (plat_enable_dirty_update ())
              then {
                /* pte needs dirty/accessed update but that is not enabled */
                TR39_Failure(PTW_PTE_Update)
              } else {
                w_pte : SV39_PTE = update_BITS(pte, pbits.bits());
                match checked_mem_write(EXTZ(pteAddr), 8, w_pte.bits()) {
                  MemValue(_) => {
                    addToTLB39(asid, vAddr, pAddr, w_pte, pteAddr, level, global);
                    TR39_Address(pAddr)
                  },
                  MemException(e) => {
                    /* pte is not in valid memory */
                    TR39_Failure(PTW_Access)
                  }
                }
              }
          }
        }
      }
    }
  }
}

/* Address translation mode */

val translationMode : (Privilege) -> SATPMode effect {rreg, escape}
function translationMode(priv) = {
  if priv == Machine then Sbare
  else {
    let arch = architecture(mstatus.SXL());
    match arch {
      Some(RV64) => {
        let mbits : satp_mode = Mk_Satp64(satp).Mode();
        match satpMode_of_bits(RV64, mbits) {
          Some(m) => m,
          None()  => internal_error("invalid RV64 translation mode in satp")
        }
      },
      _    => internal_error("unsupported address translation arch")
    }
  }
}

union TR_Result = {
  TR_Address : xlenbits,
  TR_Failure : ExceptionType
}

/* Top-level address translation dispatcher */

val translateAddr : (xlenbits, AccessType, ReadType) -> TR_Result effect {escape, rmem, rreg, wmv, wreg}
function translateAddr(vAddr, ac, rt) = {
  let effPriv : Privilege = match rt {
    Instruction => cur_privilege,
    Data => if mstatus.MPRV() == true
            then privLevel_of_bits(mstatus.MPP())
            else cur_privilege
  };
  let mxr : bool = mstatus.MXR() == true;
  let do_sum : bool = mstatus.SUM() == true;
  let mode : SATPMode = translationMode(effPriv);
  match mode {
    Sbare => TR_Address(vAddr),
    SV39  => match translate39(vAddr[38 .. 0], ac, effPriv, mxr, do_sum, SV39_LEVELS - 1) {
               TR39_Address(pa) => TR_Address(EXTZ(pa)),
               TR39_Failure(f)  => TR_Failure(translationException(ac, f))
             },
    _     => internal_error("unsupported address translation scheme")
  }
}
