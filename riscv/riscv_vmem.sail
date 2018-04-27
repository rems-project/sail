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

function checkPTEPermissions(ac : AccessType, priv : Privilege, mxr : bool, sum : bool, p : PTE_Bits) -> bool = {
  match (ac, priv) {
    (Read, User)      => p.U() == true & (p.R() == true | (p.X() == true & mxr)),
    (Write, User)     => p.U() == true & p.W() == true,
    (ReadWrite, User) => p.U() == true & p.W() == true & (p.R() == true | (p.X() == true & mxr)),
    (Execute, User)   => p.U() == true & p.X() == true,

    (Read, Supervisor)      => (p.U() == false | sum) & (p.R() == true | (p.X() == true & mxr)),
    (Write, Supervisor)     => (p.U() == false | sum) & p.W() == true,
    (ReadWrite, Supervisor) => (p.U() == false | sum) & p.W() == true & (p.R() == true | (p.X() == true & mxr)),
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
function walk39(vaddr, ac, priv, mxr, sum, ptb, level, global) -> PTW_Result = {
  let va = Mk_SV39_Vaddr(vaddr);
  let pt_ofs : paddr39 = shiftl(EXTZ(shiftr(va.VPNi(), (level * SV39_LEVEL_BITS))[SV39_LEVEL_BITS .. 0]),
                                PTE39_LOG_SIZE);
  let pte_addr = ptb + pt_ofs;
  match (checked_mem_read(Data, EXTZ(pte_addr), 8)) {
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
          if level == 0 then PTW_Failure(PTW_Invalid_PTE)
          else walk39(vaddr, ac, priv, mxr, sum, EXTZ(pte.PPNi()), level - 1, is_global)
        } else { /* leaf PTE */
          if ~ (checkPTEPermissions(ac, priv, mxr, sum, pattr)) then
            PTW_Failure(PTW_No_Permission)
          else {
            if level > 0 then { /* superpage */
              let masked = pte.PPNi() & EXTZ(shiftl(0b1, level * SV39_LEVEL_BITS) - 1);
              if masked != EXTZ(0b0) then
                PTW_Failure(PTW_Misaligned)
              else {
                let ppn = pte.PPNi() | (EXTZ(va.VPNi()) & EXTZ(shiftl(0b1, level * SV39_LEVEL_BITS) - 1));
                PTW_Success(append(ppn, va.PgOfs()), pte, pte_addr, level, is_global)
              }
            } else
              PTW_Success(append(pa, va.PgOfs()), pte, pte_addr, level, is_global)
          }
        }
      }
    }
  }
}
