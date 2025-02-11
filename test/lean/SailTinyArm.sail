// Taken from https://github.com/rems-project/sail-tiny-arm/commit/b8bf6a7d6e20f0c9fd624bab0697a9f0c6dc192c

default Order dec

$include <prelude.sail>

val rMem : bits(64) -> bits(64)
val iFetch : bits(64) -> bits(32)
val wMem_Addr : bits(64) -> unit
val wMem : (bits(64), bits(64)) -> unit
val dataMemoryBarrier : unit -> unit

overload operator ^ = {xor_vec}
 
bitfield MAIRType : bits(64) =
  {
    Attr0 : 7..0,
    Attr1 : 15..8,
    Attr2 : 23..16,
    Attr3 : 31..24,
    Attr4 : 39..32,
    Attr5 : 47..40,
    Attr6 : 55..48,
    Attr7 : 63..56
  }

bitfield S1PIRType : bits(64) =
  {
    Perm0 : 3..0,
    Perm1 : 7..4,
    Perm2 : 11..8,
    Perm3 : 15..12,
    Perm4 : 19..16,
    Perm5 : 23..20,
    Perm6 : 27..24,
    Perm7 : 31..28,
    Perm8 : 35..32,
    Perm9 : 39..36,
    Perm10 : 43..40,
    Perm11 : 47..44,
    Perm12 : 51..48,
    Perm13 : 55..52,
    Perm14 : 59..56,
    Perm15 : 63..60
  }

bitfield S2PIRType : bits(64) =
  {
    Perm0 : 3..0,
    Perm1 : 7..4,
    Perm2 : 11..8,
    Perm3 : 15..12,
    Perm4 : 19..16,
    Perm5 : 23..20,
    Perm6 : 27..24,
    Perm7 : 31..28,
    Perm8 : 35..32,
    Perm9 : 39..36,
    Perm10 : 43..40,
    Perm11 : 47..44,
    Perm12 : 51..48,
    Perm13 : 55..52,
    Perm14 : 59..56,
    Perm15 : 63..60
  }

enum SecurityState = {SS_NonSecure, SS_Root, SS_Realm, SS_Secure}

type PARTIDtype = bits(16)

type PMGtype = bits(8)

enum PARTIDspaceType = {
  PIdSpace_Secure,
  PIdSpace_Root,
  PIdSpace_Realm,
  PIdSpace_NonSecure
}

struct MPAMinfo = {
  mpam_sp : PARTIDspaceType,
  partid : PARTIDtype,
  pmg : PMGtype
}

enum AccessType = {
  AccessType_IFETCH,
  AccessType_GPR,
  AccessType_ASIMD,
  AccessType_SVE,
  AccessType_SME,
  AccessType_IC,
  AccessType_DC,
  AccessType_DCZero,
  AccessType_AT,
  AccessType_NV2,
  AccessType_SPE,
  AccessType_GCS,
  AccessType_GPTW,
  AccessType_TTW
}

enum VARange = {VARange_LOWER, VARange_UPPER}

enum MemAtomicOp = {
  MemAtomicOp_GCSSS1,
  MemAtomicOp_ADD,
  MemAtomicOp_BIC,
  MemAtomicOp_EOR,
  MemAtomicOp_ORR,
  MemAtomicOp_SMAX,
  MemAtomicOp_SMIN,
  MemAtomicOp_UMAX,
  MemAtomicOp_UMIN,
  MemAtomicOp_SWP,
  MemAtomicOp_CAS
}

enum CacheOp = {CacheOp_Clean, CacheOp_Invalidate, CacheOp_CleanInvalidate}

enum CacheOpScope = {
  CacheOpScope_SetWay,
  CacheOpScope_PoU,
  CacheOpScope_PoC,
  CacheOpScope_PoE,
  CacheOpScope_PoP,
  CacheOpScope_PoDP,
  CacheOpScope_PoPA,
  CacheOpScope_ALLU,
  CacheOpScope_ALLUIS
}

enum CacheType = {
  CacheType_Data,
  CacheType_Tag,
  CacheType_Data_Tag,
  CacheType_Instruction
}

enum CachePASpace = {
  CPAS_NonSecure,
  CPAS_Any,
  CPAS_RealmNonSecure,
  CPAS_Realm,
  CPAS_Root,
  CPAS_SecureNonSecure,
  CPAS_Secure
}

struct AccessDescriptor = {
  acctype : AccessType,
  el : bits(2),
  ss : SecurityState,
  acqsc : bool,
  acqpc : bool,
  relsc : bool,
  limitedordered : bool,
  exclusive : bool,
  atomicop : bool,
  modop : MemAtomicOp,
  nontemporal : bool,
  read : bool,
  write : bool,
  cacheop : CacheOp,
  opscope : CacheOpScope,
  cachetype : CacheType,
  pan : bool,
  transactional : bool,
  nonfault : bool,
  firstfault : bool,
  first : bool,
  contiguous : bool,
  streamingsve : bool,
  ls64 : bool,
  mops : bool,
  rcw : bool,
  rcws : bool,
  toplevel : bool,
  varange : VARange,
  a32lsmd : bool,
  tagchecked : bool,
  tagaccess : bool,
  mpam : MPAMinfo
}

enum MemType = {MemType_Normal, MemType_Device}

enum DeviceType = {
  DeviceType_GRE,
  DeviceType_nGRE,
  DeviceType_nGnRE,
  DeviceType_nGnRnE
}

struct MemAttrHints = {attrs : bits(2), hints : bits(2), transient : bool}

enum Shareability = {Shareability_NSH, Shareability_ISH, Shareability_OSH}

enum MemTagType = {
  MemTag_Untagged,
  MemTag_AllocationTagged,
  MemTag_CanonicallyTagged
}

struct MemoryAttributes = {
  memtype : MemType,
  device : DeviceType,
  inner : MemAttrHints,
  outer : MemAttrHints,
  shareability : Shareability,
  tags : MemTagType,
  notagaccess : bool,
  xs : bits(1)
}

enum PASpace = {PAS_NonSecure, PAS_Secure, PAS_Root, PAS_Realm}

struct FullAddress = {paspace : PASpace, address : bits(56)}

enum GPCF = {GPCF_None, GPCF_AddressSize, GPCF_Walk, GPCF_EABT, GPCF_Fail}

struct GPCFRecord = {gpf : GPCF, level : int}

enum Fault = {
  Fault_None,
  Fault_AccessFlag,
  Fault_Alignment,
  Fault_Background,
  Fault_Domain,
  Fault_Permission,
  Fault_Translation,
  Fault_AddressSize,
  Fault_SyncExternal,
  Fault_SyncExternalOnWalk,
  Fault_SyncParity,
  Fault_SyncParityOnWalk,
  Fault_GPCFOnWalk,
  Fault_GPCFOnOutput,
  Fault_AsyncParity,
  Fault_AsyncExternal,
  Fault_TagCheck,
  Fault_Debug,
  Fault_TLBConflict,
  Fault_BranchTarget,
  Fault_HWUpdateAccessFlag,
  Fault_Lockdown,
  Fault_Exclusive,
  Fault_ICacheMaint
}

enum ErrorState = {
  ErrorState_UC,
  ErrorState_UEU,
  ErrorState_UEO,
  ErrorState_UER,
  ErrorState_CE,
  ErrorState_Uncategorized,
  ErrorState_IMPDEF
}

struct FaultRecord = {
  statuscode : Fault,
  access : AccessDescriptor,
  ipaddress : FullAddress,
  gpcf : GPCFRecord,
  paddress : FullAddress,
  gpcfs2walk : bool,
  s2fs1walk : bool,
  write : bool,
  s1tagnotdata : bool,
  tagaccess : bool,
  level : int,
  extflag : bits(1),
  secondstage : bool,
  assuredonly : bool,
  toplevel : bool,
  overlay : bool,
  dirtybit : bool,
  domain : bits(4),
  merrorstate : ErrorState,
  debugmoe : bits(4)
}

enum MBReqDomain = {
  MBReqDomain_Nonshareable,
  MBReqDomain_InnerShareable,
  MBReqDomain_OuterShareable,
  MBReqDomain_FullSystem
}

enum MBReqTypes = {MBReqTypes_Reads, MBReqTypes_Writes, MBReqTypes_All}

struct CacheRecord = {
  acctype : AccessType,
  cacheop : CacheOp,
  opscope : CacheOpScope,
  cachetype : CacheType,
  regval : bits(64),
  paddress : FullAddress,
  vaddress : bits(64),
  setnum : int,
  waynum : int,
  level : int,
  shareability : Shareability,
  translated : bool,
  is_vmid_valid : bool,
  vmid : bits(16),
  is_asid_valid : bool,
  asid : bits(16),
  security : SecurityState,
  cpas : CachePASpace
}

enum Regime = {Regime_EL3, Regime_EL30, Regime_EL2, Regime_EL20, Regime_EL10}

enum TGx = {TGx_4KB, TGx_16KB, TGx_64KB}

struct S1TTWParams = {
  ha : bits(1),
  hd : bits(1),
  tbi : bits(1),
  tbid : bits(1),
  nfd : bits(1),
  e0pd : bits(1),
  d128 : bits(1),
  aie : bits(1),
  mair2 : MAIRType,
  ds : bits(1),
  ps : bits(3),
  txsz : bits(6),
  epan : bits(1),
  dct : bits(1),
  nv1 : bits(1),
  cmow : bits(1),
  pnch : bits(1),
  disch : bits(1),
  haft : bits(1),
  mtx : bits(1),
  skl : bits(2),
  pie : bits(1),
  pir : S1PIRType,
  pire0 : S1PIRType,
  emec : bits(1),
  amec : bits(1),
  t0sz : bits(3),
  t1sz : bits(3),
  uwxn : bits(1),
  tgx : TGx,
  irgn : bits(2),
  orgn : bits(2),
  sh : bits(2),
  hpd : bits(1),
  ee : bits(1),
  wxn : bits(1),
  ntlsmd : bits(1),
  dc : bits(1),
  sif : bits(1),
  mair : MAIRType
}

struct S2TTWParams = {
  ha : bits(1),
  hd : bits(1),
  sl2 : bits(1),
  ds : bits(1),
  d128 : bits(1),
  sw : bits(1),
  nsw : bits(1),
  sa : bits(1),
  nsa : bits(1),
  ps : bits(3),
  txsz : bits(6),
  fwb : bits(1),
  cmow : bits(1),
  skl : bits(2),
  s2pie : bits(1),
  s2pir : S2PIRType,
  tl0 : bits(1),
  tl1 : bits(1),
  assuredonly : bits(1),
  haft : bits(1),
  emec : bits(1),
  s : bits(1),
  t0sz : bits(4),
  tgx : TGx,
  sl0 : bits(2),
  irgn : bits(2),
  orgn : bits(2),
  sh : bits(2),
  ee : bits(1),
  ptw : bits(1),
  vm : bits(1)
}

struct TranslationInfo = {
  regime : Regime,
  vmid : option(bits(16)),
  asid : option(bits(16)),
  va : bits(64),
  s1level : option(int),
  s2info : option((bits(64), int)),
  s1params : option(S1TTWParams),
  s2params : option(S2TTWParams),
  memattrs : MemoryAttributes
}

enum TLBILevel = {TLBILevel_Any, TLBILevel_Last}

enum TLBIOp = {
  TLBIOp_DALL,
  TLBIOp_DASID,
  TLBIOp_DVA,
  TLBIOp_IALL,
  TLBIOp_IASID,
  TLBIOp_IVA,
  TLBIOp_ALL,
  TLBIOp_ASID,
  TLBIOp_IPAS2,
  TLBIPOp_IPAS2,
  TLBIOp_VAA,
  TLBIOp_VA,
  TLBIPOp_VAA,
  TLBIPOp_VA,
  TLBIOp_VMALL,
  TLBIOp_VMALLS12,
  TLBIOp_RIPAS2,
  TLBIPOp_RIPAS2,
  TLBIOp_RVAA,
  TLBIOp_RVA,
  TLBIPOp_RVAA,
  TLBIPOp_RVA,
  TLBIOp_RPA,
  TLBIOp_PAALL
}

enum TLBIMemAttr = {TLBI_AllAttr, TLBI_ExcludeXS}

struct TLBIRecord = {
  op : TLBIOp,
  from_aarch64 : bool,
  security : SecurityState,
  regime : Regime,
  vmid : bits(16),
  asid : bits(16),
  level : TLBILevel,
  attr : TLBIMemAttr,
  ipaspace : PASpace,
  address : bits(64),
  end_address_name : bits(64),
  d64 : bool,
  d128 : bool,
  ttl : bits(4),
  tg : bits(2)
}

union arm_acc_type = {
  SAcc_ASIMD : bool,
  SAcc_SVE : bool,
  SAcc_SME : bool,
  SAcc_IC : unit,
  SAcc_DC : unit,
  SAcc_DCZero : unit,
  SAcc_AT : unit,
  SAcc_NV2 : unit,
  SAcc_SPE : unit,
  SAcc_GCS : unit,
  SAcc_GPTW : unit
}

struct TLBIInfo = {rec : TLBIRecord, shareability : Shareability}

struct DxB = {domain : MBReqDomain, types : MBReqTypes, nXS : bool}

union Barrier = {
  Barrier_DSB : DxB,
  Barrier_DMB : DxB,
  Barrier_ISB : unit,
  Barrier_SSBB : unit,
  Barrier_PSSBB : unit,
  Barrier_SB : unit
}
type boolean = bit
type integer = int
type uinteger = nat

type reg_index = range(0, 31)

register _PC : bits(64)

/* General purpose registers */

register R30 : bits(64)
register R29 : bits(64)
register R28 : bits(64)
register R27 : bits(64)
register R26 : bits(64)
register R25 : bits(64)
register R24 : bits(64)
register R23 : bits(64)
register R22 : bits(64)
register R21 : bits(64)
register R20 : bits(64)
register R19 : bits(64)
register R18 : bits(64)
register R17 : bits(64)
register R16 : bits(64)
register R15 : bits(64)
register R14 : bits(64)
register R13 : bits(64)
register R12 : bits(64)
register R11 : bits(64)
register R10 : bits(64)
register R9 : bits(64)
register R8 : bits(64)
register R7 : bits(64)
register R6 : bits(64)
register R5 : bits(64)
register R4 : bits(64)
register R3 : bits(64)
register R2 : bits(64)
register R1 : bits(64)
register R0 : bits(64)

let GPRs : vector(31, register(bits(64))) = [
  ref R30,
  ref R29,
  ref R28,
  ref R27,
  ref R26,
  ref R25,
  ref R24,
  ref R23,
  ref R22,
  ref R21,
  ref R20,
  ref R19,
  ref R18,
  ref R17,
  ref R16,
  ref R15,
  ref R14,
  ref R13,
  ref R12,
  ref R11,
  ref R10,
  ref R9,
  ref R8,
  ref R7,
  ref R6,
  ref R5,
  ref R4,
  ref R3,
  ref R2,
  ref R1,
  ref R0,
]

val wX : (reg_index, bits(64)) -> unit

function wX(n, value) = {
  if n != 31 then
    *GPRs[n] = value;
}

val rX : reg_index -> bits(64)

function rX(n) = {
  if n != 31 then
    *GPRs[n]
  else
    0x0000000000000000;
}

overload X = {rX, wX}

function rPC() -> bits(64) = _PC
function wPC(pc : bits(64)) -> unit = _PC = pc

overload PC = {rPC, wPC}
union ast =  {
  LoadRegister : (reg_index, reg_index, reg_index),
  StoreRegister : (reg_index, reg_index, reg_index),
  ExclusiveOr : (reg_index, reg_index, reg_index),
  DataMemoryBarrier : unit,
  CompareAndBranch : (reg_index, bits(64)),
}

val decode : bits(32) -> option(ast)

scattered function decode

val execute : ast -> unit

scattered function execute

/* LoadStoreRegister: LDR and STR */
val decodeLoadStoreRegister : (bits(2), bits(5), bits(3), bit, bits(5), bits(5)) -> option(ast)

function clause decode (0b11@0b111@0b0@0b00@(opc:bits(2))@0b1@(Rm:bits(5))@(option_v:bits(3))@[S]@0b10@(Rn:bits(5))@(Rt:bits(5))) = {
  decodeLoadStoreRegister(opc, Rm, option_v, S, Rn, Rt)
}
function decodeLoadStoreRegister (opc, Rm, option_v, S, Rn, Rt) = {
  let t : reg_index = unsigned(Rt);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);
  /* option_v == 0b011 and S == 1 means that the offset in Rm is used as is and not shifted or extended */
  if option_v != 0b011 | S == bitone then None ()
  else if opc == 0b00
  then Some(LoadRegister((t,n,m)))
  else if opc == 0b01
  then Some(StoreRegister((t,n,m)))
  else None ();
}

/* LDR Xt, [Xn, Xm] */
function clause execute LoadRegister(t, n, m) = {
  _PC = _PC + 4;
  /* Ask for the value of register Xn and record it in the local
   * variable base_addr */
  let base_addr = X(n);
  /* Ask for the value of register Xm and record it in the local
   * variable offset */
  let offset = X(m);
  /* Compute the address */
  let addr = base_addr + offset;
  /* Ask for the eight-byte value in memory starting from location
  addr and record it in the local variable data */
  let data = rMem(addr);
  /* Ask for the value of data to be written to register Xt */
  X(t) = data;
}

/* STR Xt, [Xn, Xm] */
function clause execute StoreRegister(t, n, m) = {
  _PC = _PC + 4;
  /* Ask for the value of register Xn and record it in the local
   * variable base_addr */
  let base_addr = X(n);
  /* Ask for the value of register Xm and record it in the local
   * variable offset */
  let offset = X(m);
  /* Compute the address */
  let addr = base_addr + offset;
  /* Announce that a store into the eight bytes of memory starting
   * from location addr will be performed later */
  wMem_Addr(addr);
  /* Ask for the value of register Xt and record it in the local
   * variable data */
  let data = X(t);
  /* Ask for the value of data to be stored into the eight bytes of
   * memory starting from location addr */
  wMem(addr, data);
}

/* Exclusive OR: EOR */
val decodeExclusiveOr : (bit, bits(2), bit, bits(5), bits(6), bits(5), bits(5)) -> option(ast)

function clause decode ([sf]@0b10@0b01010@(shift:bits(2))@[N]@(Rm:bits(5))@(imm6:bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  decodeExclusiveOr(sf, shift, N, Rm, imm6, Rn, Rd)
}
function decodeExclusiveOr (sf, shift, N, Rm, imm6, Rn, Rd) = {
  let d : reg_index = unsigned(Rd);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);

  if sf == bitzero & imm6[5] == bitone then None ()
  else if imm6 != 0b000000 then None ()
  else Some(ExclusiveOr((d,n,m)));
}

/* EOR Xd, Xn, Xm */
function clause execute ExclusiveOr(d, n, m) = {
  /* Ask for the value of register Xn and record it in the local
   * variable operand1 */
  let operand1 = X(n);
  /* Ask for the value of register Xm and record it in the local
   * variable operand2 */
  let operand2 = X(m);
  /* Compute the bitwise exclusive OR, and ask for the value of
   * the result to be written to register Xd */
  X(d) = operand1 ^ operand2;
}

/* DMB */
val decodeDataMemoryBarrier : bits(4) -> option(ast)

function clause decode (0b1101010100@0b0@0b00@0b011@0b0011@(CRm : bits(4))@0b1@0b01@0b11111) = {
  decodeDataMemoryBarrier(CRm)
}

function decodeDataMemoryBarrier(CRm) = {
  if CRm != 0b1111 then None ()
  else Some(DataMemoryBarrier());
}

function clause execute DataMemoryBarrier() = {
  dataMemoryBarrier();
}

/* CompareAndBranch: CBZ */
val decodeCompareAndBranch : (bits(19), bits(5)) -> option(ast)

function clause decode (0b1@0b011010@0b0@(imm19:bits(19))@(Rt:bits(5))) = {
  decodeCompareAndBranch(imm19, Rt)
}

function decodeCompareAndBranch(imm19, Rt) = {
  let t : reg_index = unsigned(Rt);
  let offset : bits(64) = sail_sign_extend(imm19@0b00,64);

  Some(CompareAndBranch(t,offset));
}

/* CBZ Xt, <offset> */
function clause execute CompareAndBranch(t, offset) = {
  /* Ask for the value of register Xt and record it in the local
   * variable operand */
  let operand = X(t);
  /* Check if operand is 0 */
  if operand == 0x0000000000000000 then {
    /* Ask for the value of the program counter register and record it
     * in the local variable base */
    let base = PC();
    /* Compute the address */
    let addr = base + offset;
    /* Ask for the value of result to be written to the program counter
     * register */
    PC() = addr;
  }
  else _PC = _PC + 4;
}

// This needs to be the last clause
function clause decode(_) = { None() }

// Simple top level fetch and execute loop.
val fetch_and_execute : unit -> unit

function fetch_and_execute () = {
  let machineCode = iFetch(_PC);
  let instr = decode(machineCode);
  match instr {
    Some (instr) => execute(instr),
    None () => assert (false, "Unsupported Encoding")
  }
}

$include <concurrency_interface.sail>
$include <concurrency_interface/tlbi.sail>
$include <concurrency_interface/exception.sail>
$include <concurrency_interface/cache_op.sail>

val pa_bits : bits(56) -> bits(64)

function pa_bits(bv) = sail_zero_extend(bv, 64)

instantiation sail_mem_read with
  'pa = bits(56),
  'translation_summary = option(TranslationInfo),
  'arch_ak = arm_acc_type,
  'abort = Fault,
  pa_bits = pa_bits

instantiation sail_mem_write with
  'pa = bits(56),
  'translation_summary = option(TranslationInfo),
  'arch_ak = arm_acc_type,
  'abort = Fault,
  pa_bits = pa_bits

function rMem(addr) = {
  let req : Mem_read_request(8, 64, bits(56), option(TranslationInfo), arm_acc_type) = struct {
    access_kind = AK_explicit(struct { variety = AV_plain, strength = AS_normal }),
    va = Some(addr),
    pa = truncate(addr, 56),
    translation = None(),
    size = 8,
    tag = false
  };
  match sail_mem_read(req) {
    Ok((value, _)) => value,
    Err(_) => exit(),
  }
}

function iFetch(addr) = {
  let req : Mem_read_request(4, 64, bits(56), option(TranslationInfo), arm_acc_type) = struct {
    access_kind = AK_ifetch(),
    va = Some(addr),
    pa = truncate(addr, 56),
    translation = None(),
    size = 4,
    tag = false
  };
  match sail_mem_read(req) {
    Ok((value, _)) => value,
    Err(_) => exit(),
  }
}

function wMem_Addr(addr) = sail_address_announce(64, addr)

function wMem(addr, value) = {
  let req : Mem_write_request(8, 64, bits(56), option(TranslationInfo), arm_acc_type) = struct {
    access_kind = AK_explicit(struct { variety = AV_plain, strength = AS_normal }),
    va = Some(addr),
    pa = truncate(addr, 56),
    translation = None(),
    size = 8,
    value = Some(value),
    tag = None()
  };
  match sail_mem_write(req) {
    Ok(_) => (),
    Err(_) => exit(),
  }
}

instantiation sail_barrier with
  'barrier = Barrier

function dataMemoryBarrier() = sail_barrier(
  Barrier_DMB(struct{
    domain = MBReqDomain_FullSystem,
    types = MBReqTypes_All,
    nXS = false}))

instantiation sail_cache_op with
  'cache_op = CacheRecord

instantiation sail_tlbi with
  'tlbi = TLBIInfo

instantiation sail_return_exception

instantiation sail_take_exception with
  'fault = option(FaultRecord)
