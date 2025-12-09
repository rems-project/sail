// Generated from commit 2018b8a4 of sail-tiny-arm, in November 2025

default Order dec

$define CONCURRENCY_INTERFACE_V2

$include <prelude.sail>

val eq_any = pure {ocaml: "(fun (x, y) -> x = y)", interpreter: "eq_anything", lem: "eq", coq: "generic_eq", lean: "BEq.beq", c: "eq_anything"} : forall ('a : Type). ('a, 'a) -> bool

val eq_bits_int : forall 'n 'm, 'n >= 0 & 'm >= 0. (bits('n), int('m)) -> bool
function eq_bits_int (x, y) = (unsigned(x) == y)

overload operator == = {eq_any, eq_bits_int}

overload operator ^ = {xor_vec}

/* BSD 3-clause Clear License

Copyright (c) 2022
  Arm Limited (or its affiliates),
  Thomas Bauereiss,
  Brian Campbell,
  Alasdair Armstrong,
  Alastair Reid,
  Peter Sewell

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted (subject to the limitations in the
disclaimer below) provided that the following conditions are met:

  * Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.
  * Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in the
    documentation and/or other materials provided with the distribution.
  * Neither the name of ARM Limited nor the names of its contributors
    may be used to endorse or promote products derived from this
    software without specific prior written permission.

NO EXPRESS OR IMPLIED LICENSES TO ANY PARTY'S PATENT RIGHTS ARE GRANTED
BY THIS LICENSE. THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING,
BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE
COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

// Generated from the official sail-arm repo:
// - version 9.4
// - sail commit 38371c9f
// - sail-arm commit 17e64fb
// - command (in armv9.4 folder): make interface_types.sail

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

struct TLBContext = {
  ss : SecurityState,
  regime : Regime,
  vmid : bits(16),
  asid : bits(16),
  nG : bits(1),
  ipaspace : PASpace,
  includes_s1_name : bool,
  includes_s2_name : bool,
  includes_gpt_name : bool,
  ia : bits(64),
  tg : TGx,
  cnp : bits(1),
  level : int,
  isd128 : bool,
  xs : bits(1)
}

struct AddressDescriptor = {
  fault : FaultRecord,
  memattrs : MemoryAttributes,
  paddress : FullAddress,
  tlbcontext : TLBContext,
  s1assured : bool,
  s2fs1mro : bool,
  mecid : bits(16),
  vaddress : bits(64)
}

struct TranslationStartInfo = {
  ss : SecurityState,
  regime : Regime,
  vmid : bits(16),
  asid : bits(16),
  va : bits(64),
  cnp : bits(1),
  accdesc : AccessDescriptor,
  size : int
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

$ifdef SYSTEM_TINY_ARM

struct ProcState = {
  N : bits(1),
  Z : bits(1),
  C : bits(1),
  V : bits(1),
  D : bits(1),
  A : bits(1),
  I : bits(1),
  F : bits(1),
  EXLOCK : bits(1),
  PAN : bits(1),
  UAO : bits(1),
  DIT : bits(1),
  TCO : bits(1),
  PM : bits(1),
  PPEND : bits(1),
  BTYPE : bits(2),
  ZA : bits(1),
  SM : bits(1),
  ALLINT : bits(1),
  SS : bits(1),
  IL : bits(1),
  EL : bits(2),
  nRW : bits(1),
  SP : bits(1),
  Q : bits(1),
  GE : bits(4),
  SSBS : bits(1),
  IT : bits(8),
  J : bits(1),
  T : bits(1),
  E : bits(1),
  M : bits(5)
}

// We fix the size to 64 and happyly ignore 128 bits register extension for VMSA128

register SP_EL0 : bits(64)
register SP_EL1 : bits(64)
register SP_EL2 : bits(64)
register SP_EL3 : bits(64)

register ELR_EL1 : bits(64)
register ELR_EL2 : bits(64)
register ELR_EL3 : bits(64)

$ifdef SYSTEM_TINY_ARM
register PSTATE : ProcState
$else
register PSTATE : bits(64)
$endif

register ESR_EL1 : bits(64)
register ESR_EL2 : bits(64)
register ESR_EL3 : bits(64)

register FAR_EL1 : bits(64)
register FAR_EL2 : bits(64)
register FAR_EL3 : bits(64)

register PAR_EL1 : bits(64)

register TTBR0_EL1 : bits(64)
register TTBR1_EL1 : bits(64)
register TTBR0_EL2 : bits(64)
register TTBR1_EL2 : bits(64)
register TTBR0_EL3 : bits(64)
register VTTBR_EL2 : bits(64)

register VBAR_EL1 : bits(64)
register VBAR_EL2 : bits(64)
register VBAR_EL3 : bits(64)

register SPSR_EL1 : bits(64)
register SPSR_EL2 : bits(64)
register SPSR_EL3 : bits(64)

register ID_AA64MMFR0_EL1 : bits(64)
register ID_AA64MMFR1_EL1 : bits(64)
register ID_AA64MMFR2_EL1 : bits(64)
register ID_AA64MMFR3_EL1 : bits(64)
register ID_AA64MMFR4_EL1 : bits(64)

register TCR_EL1 : bits(64)
register TCR_EL2 : bits(64)
register TCR_EL3 : bits(64)
register VTCR_EL2 : bits(64)

register SCTLR_EL1 : bits(64)
register SCTLR_EL2 : bits(64)
register SCTLR_EL3 : bits(64)

$endif

val dataMemoryBarrier : MBReqTypes -> unit

$include <concurrency_interface.sail>
$include <concurrency_interface/tlbi.sail>
$include <concurrency_interface/exception.sail>
$include <concurrency_interface/cache_op.sail>
$include <concurrency_interface/translation.sail>

$ifdef SYSTEM_TINY_ARM
type addr_size : Int = 56
let addr_size' : int(56) = 56
$else
type addr_size : Int = 64
let addr_size' : int(64) = 64
$endif

$ifdef SYSTEM_TINY_ARM
instantiation sail_cache_op with
  'cache_op = CacheRecord

instantiation sail_tlbi with
  'tlbi = TLBIInfo

instantiation sail_return_exception

instantiation sail_take_exception with
  'exn = option(FaultRecord)

instantiation sail_translation_start with
  'trans_start = TranslationStartInfo

instantiation sail_translation_end with
  'trans_end = AddressDescriptor
$endif

function mem_acc_is_explicit     (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR
function mem_acc_is_ifetch       (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_IFETCH
function mem_acc_is_ttw          (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_TTW
function mem_acc_is_relaxed      (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & not_bool(acc.acqpc) & not_bool(acc.acqsc) & not_bool(acc.relsc)
function mem_acc_is_rel_acq_rcpc (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & acc.acqpc
function mem_acc_is_rel_acq_rcsc (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & (acc.acqsc | acc.relsc)
function mem_acc_is_standalone   (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & not_bool(acc.exclusive) & not_bool(acc.atomicop)
function mem_acc_is_exclusive    (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & acc.exclusive
function mem_acc_is_atomic_rmw   (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & acc.atomicop

function base_AccessDescriptor (acctype : AccessType) -> AccessDescriptor = struct {
  acctype = acctype,
  el = sail_zeros(2),
  ss = SS_NonSecure,
  acqsc = false,
  acqpc = false,
  relsc = false,
  limitedordered = false,
  exclusive = false,
  atomicop = false,
  modop = MemAtomicOp_ADD,
  nontemporal = false,
  read = false,
  write = false,
  cacheop = CacheOp_Clean,
  opscope = CacheOpScope_ALLU,
  cachetype = CacheType_Data,
  pan = false,
  transactional = false,
  nonfault = false,
  firstfault = false,
  first = false,
  contiguous = false,
  streamingsve = false,
  ls64 = false,
  mops = false,
  rcw = false,
  rcws = false,
  toplevel = false,
  varange = VARange_LOWER,
  a32lsmd = false,
  tagchecked = false,
  tagaccess = false,
  mpam = struct {
    mpam_sp = PIdSpace_NonSecure,
    partid = 0x0000,
    pmg = 0x00
  }
}

$ifdef SYSTEM_TINY_ARM
function create_writeAccessDescriptor() -> AccessDescriptor = {
  var accdesc = base_AccessDescriptor(AccessType_GPR);
  accdesc.write = true;
  accdesc.read = false;
  accdesc.el = PSTATE.EL;
  accdesc
}

function create_readAccessDescriptor() -> AccessDescriptor = {
  var accdesc = base_AccessDescriptor(AccessType_GPR);
  accdesc.read = true;
  accdesc.write = false;
  accdesc.el = PSTATE.EL;
  accdesc
}

function create_iFetchAccessDescriptor() -> AccessDescriptor = {
  var accdesc = base_AccessDescriptor(AccessType_IFETCH);
  accdesc.read = true;
  accdesc.write = false;
  accdesc.el = PSTATE.EL;
  accdesc
}
$else
function create_writeAccessDescriptor() -> AccessDescriptor = {
  var accdesc = base_AccessDescriptor(AccessType_GPR);
  accdesc.write = true;
  accdesc.read = false;
  accdesc.el = 0b00;
  accdesc
}

function create_readAccessDescriptor() -> AccessDescriptor = {
  var accdesc = base_AccessDescriptor(AccessType_GPR);
  accdesc.read = true;
  accdesc.write = false;
  accdesc.el = 0b00;
  accdesc
}

function create_iFetchAccessDescriptor() -> AccessDescriptor = {
  var accdesc = base_AccessDescriptor(AccessType_IFETCH);
  accdesc.read = true;
  accdesc.write = false;
  accdesc.el = 0b00;
  accdesc
}
$endif

$ifdef SYSTEM_TINY_ARM
enum DescriptorType = {
  DescriptorType_Table,
  DescriptorType_Leaf,
  DescriptorType_Invalid
}

function base_FullAddress () -> FullAddress = struct {
  paspace = PAS_NonSecure,
  address = sail_zeros(56)
}

function base_FaultRecord (accdesc : AccessDescriptor) -> FaultRecord = struct {
  statuscode = Fault_None,
  access = accdesc,
  ipaddress = base_FullAddress(),
  gpcf = struct {
    gpf = GPCF_None,
    level = 0
  },
  paddress = base_FullAddress(),
  gpcfs2walk = false,
  s2fs1walk = false,
  write = not_bool(accdesc.read) & accdesc.write,
  s1tagnotdata = false,
  tagaccess = false,
  level = 0,
  extflag = sail_zeros(1),
  secondstage = false,
  assuredonly = false,
  toplevel = false,
  overlay = false,
  dirtybit = false,
  domain = sail_zeros(4),
  merrorstate = ErrorState_UC,
  debugmoe = sail_zeros(4)
}

function base_MemoryAttributes () -> MemoryAttributes = struct {
  memtype = MemType_Normal,
  device = DeviceType_GRE,
  inner = struct {
    attrs = sail_zeros(2),
    hints = sail_zeros(2),
    transient = false,
  },
  outer = struct {
    attrs = sail_zeros(2),
    hints = sail_zeros(2),
    transient = false,
  },
  shareability = Shareability_ISH,
  tags = MemTag_Untagged,
  notagaccess = false,
  xs = sail_zeros(1),
}

function base_TLBContext () -> TLBContext = struct {
  ss = SS_NonSecure,
  regime = Regime_EL10,
  vmid = sail_zeros(16),
  asid = sail_zeros(16),
  nG = sail_zeros(1),
  ipaspace = PAS_NonSecure,
  includes_s1_name = false,
  includes_s2_name = false,
  includes_gpt_name = false,
  ia = sail_zeros(64),
  tg = TGx_4KB,
  cnp = sail_zeros(1),
  level = 0,
  isd128 = false,
  xs = sail_zeros(1),
}

function base_AddressDescriptor (accdesc: AccessDescriptor) -> AddressDescriptor = struct {
  fault = base_FaultRecord(accdesc),
  memattrs = base_MemoryAttributes(),
  paddress = base_FullAddress(),
  tlbcontext = base_TLBContext(),
  s1assured = false,
  s2fs1mro = false,
  mecid = sail_zeros(16),
  vaddress = sail_zeros(64)
}
$endif

$ifdef SYSTEM_TINY_ARM
type addr_space : Type = PASpace
let addr_space_def = PAS_NonSecure
$else
type addr_space : Type = unit
let addr_space_def = ()
$endif

$ifdef SYSTEM_TINY_ARM
type abort = Fault
$else
type abort = unit
$endif


instantiation sail_mem_read with
  'addr_size = addr_size,
  'addr_space = addr_space,
  'mem_acc = AccessDescriptor,
  'abort = abort,
  'CHERI = false,
  'cap_size_log = 0,
  mem_acc_is_explicit = mem_acc_is_explicit,
  mem_acc_is_ifetch = mem_acc_is_ifetch,
  mem_acc_is_ttw = mem_acc_is_ttw,
  mem_acc_is_relaxed = mem_acc_is_relaxed,
  mem_acc_is_rel_acq_rcpc = mem_acc_is_rel_acq_rcpc,
  mem_acc_is_rel_acq_rcsc = mem_acc_is_rel_acq_rcsc,
  mem_acc_is_standalone = mem_acc_is_standalone,
  mem_acc_is_exclusive = mem_acc_is_exclusive,
  mem_acc_is_atomic_rmw = mem_acc_is_atomic_rmw

instantiation sail_mem_write with
  'addr_size = addr_size,
  'addr_space = addr_space,
  'mem_acc = AccessDescriptor,
  'abort = abort,
  'CHERI = false,
  'cap_size_log = 0,
  mem_acc_is_explicit = mem_acc_is_explicit,
  mem_acc_is_ifetch = mem_acc_is_ifetch,
  mem_acc_is_ttw = mem_acc_is_ttw,
  mem_acc_is_relaxed = mem_acc_is_relaxed,
  mem_acc_is_rel_acq_rcpc = mem_acc_is_rel_acq_rcpc,
  mem_acc_is_rel_acq_rcsc = mem_acc_is_rel_acq_rcsc,
  mem_acc_is_standalone = mem_acc_is_standalone,
  mem_acc_is_exclusive = mem_acc_is_exclusive,
  mem_acc_is_atomic_rmw = mem_acc_is_atomic_rmw

instantiation sail_mem_address_announce with
  'addr_size = addr_size,
  'addr_space = addr_space,
  'mem_acc = AccessDescriptor,
  'abort = abort,
  'CHERI = false,
  'cap_size_log = 0

  /* See tiny-arm for descriptions, interface for definitions */
val iFetch : (bits(addr_size), AccessDescriptor) -> bits(32)
val rMem : (bits(addr_size), AccessDescriptor) -> bits(64)
val wMem_Addr : bits(addr_size) -> unit
val wMem : (bits(addr_size), bits(64), AccessDescriptor) -> unit
val translate_address : (bits(64), AccessDescriptor) -> option(bits(addr_size))

val read_memory : forall 'N, 'N > 0.
  (int('N), bits(addr_size), AccessDescriptor) -> bits('N * 8)

function read_memory(N, addr, accdesc) = {
  let req : Mem_request('N, 0, addr_size, addr_space, AccessDescriptor) = struct {
    access_kind   = accdesc,
    address       = truncate(addr, addr_size'),
    address_space = addr_space_def,
    size          = N,
    num_tag       = 0
  };

  match sail_mem_read(req) {
    Ok((bytes, _)) => from_bytes_le(bytes),
    Err(_e) => { exit() }
  }
}

function iFetch(addr, accdesc) = read_memory(4, addr, accdesc)

function rMem(addr, accdesc) = read_memory(8, addr, accdesc)

function wMem_Addr(addr) = sail_address_announce(64, sail_zero_extend(addr, 64))

function wMem(addr, value, accdesc) = {
  let req : Mem_request(8, 0, addr_size, addr_space, AccessDescriptor) = struct {
    access_kind = accdesc,
    address = truncate(addr, addr_size'),
    address_space = addr_space_def,
    size = 8,
    num_tag = 0
  };
  match sail_mem_write(req, to_bytes_le(8, value), []) {
    Ok(_) => (),
    Err(_) => exit(),
  }
}

instantiation sail_barrier with
  'barrier = Barrier

function dataMemoryBarrier(types) = sail_barrier(
  Barrier_DMB(struct{
    domain = MBReqDomain_FullSystem,
    types = types,
    nXS = false}))

$ifdef SYSTEM_TINY_ARM
struct Permissions = {
  allow_write : bool,
  allow_unprivileged_data : bool,
  allow_unprivileged_exec : bool, // also just "allow_exec" in single EL translation regimes
  allow_privileged_exec : bool,
}

function extract_perms_table(descriptor : bits(64)) -> Permissions = {
  let ap_table = descriptor[62..61];

  return struct {
    allow_write = [ap_table[1]] == 0b0,
    allow_unprivileged_data = [ap_table[0]] == 0b0,
    allow_unprivileged_exec = [descriptor[60]] == 0b0,
    allow_privileged_exec = [descriptor[59]] == 0b0,
  }
}

function extract_perms_leaf(descriptor : bits(64)) -> Permissions = {
  let ap = descriptor[7..6];

  return struct {
    allow_write = [ap[1]] == 0b0,
    allow_unprivileged_data = [ap[0]] == 0b1,
    allow_unprivileged_exec = [descriptor[54]] == 0b0,
    allow_privileged_exec = [descriptor[53]] == 0b0,
  }
}

function create_AccessDescriptorTTW (toplevel : bool, varange : VARange) -> AccessDescriptor = {
  var accdesc : AccessDescriptor = base_AccessDescriptor(AccessType_TTW);
  accdesc.el = PSTATE.EL;
  accdesc.read = true;
  accdesc.toplevel = toplevel;
  accdesc.varange = varange;
  return(accdesc)
}

function get_VARange (va : bits(64)) -> VARange = {
  if [va[48]] == 0b0 then {
    VARange_LOWER
  } else {
    VARange_UPPER
  }
}

function va_out_of_range (va : bits(64)) -> bool = {
  not_bool(va[63..48] == 0x0000 | va[63..48] == 0xFFFF)
}

function get_translation_base_address (varange : VARange) -> bits(56) = {
  let ttbr : bits(64) = match varange {
    VARange_LOWER => TTBR0_EL1,
    VARange_UPPER => TTBR1_EL1
  };
  var baddr = sail_zeros(56);
  baddr[47 .. 5] = ttbr[47 .. 5];
  return baddr
}

function ASID_read () -> bits(16) = {
  if slice(TCR_EL1, 22, 1) == sail_zeros(1) then
    slice(TTBR0_EL1, 48, 16)
  else
    slice(TTBR1_EL1, 48, 16)
}

function is_fault (addrdesc : AddressDescriptor) -> bool = {
  match addrdesc.fault.statuscode {
    Fault_None => false,
    _ => true
  }
}

/* If it returns true, the access is allowed */
function check_permission (
  perms : Permissions,
  accdesc : AccessDescriptor
) -> bool = {
  let at_el0 = accdesc.el == 0b00;

  if accdesc.acctype == AccessType_IFETCH then {
    if at_el0 then {
      return perms.allow_unprivileged_exec;
    } else {
      return perms.allow_privileged_exec;
    }
  };

  if accdesc.write & not_bool(perms.allow_write) then {
    return false;
  };

  if at_el0 & not_bool(perms.allow_unprivileged_data) then {
    return false;
  };

  return true;
}

function get_TTEntryAddress (level : range(0, 3), ia : bits(64), baseaddress : bits(56)) -> bits(56) = {
  let 'stride = 9;
  let 'lsb = (3 - level) * stride + 12;
  let 'msb = lsb + stride - 1;
  let index = sail_zero_extend(ia[msb .. lsb] @ sail_zeros(3), 56);
  let descaddress : bits(56) = baseaddress | index;
  return descaddress
}

function decode_desc_type(descriptor : bits(64), level : int) -> DescriptorType = {
  if [descriptor[0]] == 0b0 then {
    return(DescriptorType_Invalid)
  } else {
    if [descriptor[1]] == 0b1 then {
      if level == 3 then {
        DescriptorType_Leaf
      } else {
        DescriptorType_Table
      }
    } else if [descriptor[1]] == 0b0 then { // The descriptor is a block
      if (level == 1 | level == 2) then {
        DescriptorType_Leaf
      } else {
        DescriptorType_Invalid
      }
    } else {
      DescriptorType_Invalid
    }
  }
}

function pgt_walk(va : bits(64), accdesc : AccessDescriptor) -> AddressDescriptor = {
  let varange = get_VARange(va);

  let baseaddress = get_translation_base_address(varange);
  var descaddress = get_TTEntryAddress(0, va, baseaddress);

  // Address descriptor to be returned from the page table walk
  var addrdesc = base_AddressDescriptor(accdesc);
  addrdesc.vaddress = va;
  addrdesc.fault.write = accdesc.write;
  addrdesc.fault.access = accdesc;

  foreach (level from 0 to 3) {
    addrdesc.fault.level = level;

    let walkaccess = create_AccessDescriptorTTW(level == 0, varange);
    let descriptor = read_memory(8, descaddress, walkaccess);

    match decode_desc_type(descriptor, level) {
      DescriptorType_Table => {
        let perms = extract_perms_table(descriptor);
        if not_bool(check_permission(perms, accdesc)) then {
          addrdesc.fault.statuscode = Fault_Permission;
          return addrdesc
        };

        let next_baseaddress = 0x00 @ descriptor[47..12] @ 0x000;
        assert (level < 3, "Table entry at level 3");
        descaddress = get_TTEntryAddress(level + 1, va, next_baseaddress);
        ()
      },
      DescriptorType_Leaf => {
        let perms = extract_perms_leaf(descriptor);
        if not_bool(check_permission(perms, accdesc)) then {
          addrdesc.fault.statuscode = Fault_Permission;
          return addrdesc
        };

        let offset = 12 + (3 - level) * 9;
        let out_pa = 0x00 @ descriptor[47..offset] @ va[offset - 1 .. 0];
        addrdesc.paddress.address = out_pa;
        return addrdesc
      },
      DescriptorType_Invalid => {
        addrdesc.fault.statuscode = Fault_Translation;
        return addrdesc
      }
    }
  };
  exit()
}

function handle_fault (addrdesc : AddressDescriptor) -> unit = {
  let fault : FaultRecord = addrdesc.fault;
  let vaddress = addrdesc.vaddress;
  let source_el = fault.access.el;
  let target_el = 0b01; // We're handling at EL1

  let vect_offset =
    if source_el == target_el then {
      if PSTATE.SP == 0b0 then {
        0x000
      } else {
        0x200
      }
    } else {
      0x400
    };

  // Report the exception
  sail_take_exception(Some(fault));

  // Determine Exception Class (EC)
  var ec = 0b000000;
  let il = 0b1;

  if fault.access.acctype == AccessType_IFETCH then {
    ec = if source_el == target_el then 0b100001 else 0b100000;
  } else if fault.access.acctype == AccessType_GPR then {
    ec = if source_el == target_el then 0b100101 else 0b100100;
  } else {
    exit();
  };

  // Determine Fault Status Code (FSC) based on fault type and level
  let level_bit : bits(2) =
    match fault.level {
      0 => 0b00,
      1 => 0b01,
      2 => 0b10,
      3 => 0b11,
      _ => exit(),
    };
  let dfsc : bits(6) =
    if fault.statuscode == Fault_Translation then {
      // Translation faults: 0b0001xx (where xx is level)
      0b0001 @ level_bit
    } else if fault.statuscode == Fault_Permission then {
      // Permission faults: 0b0011xx (where xx is level)
      0b0011 @ level_bit
    } else {
      // Default/unknown fault
      0b000000
    };

  // Build ISS (Instruction Specific Syndrome)
  let wnr = if fault.write then 0b1 else 0b0;
  let iss = sail_zero_extend(wnr @ dfsc, 25);
  ESR_EL1 = sail_zero_extend((ec @ il) @ iss, 64);
  FAR_EL1 = vaddress;
  ELR_EL1 = _PC;

  _PC = slice(VBAR_EL1, 12, 52) @ vect_offset;
}

function translate_address(va, accdesc) = {
  // Check SCTLR_EL1.M to check if MMU is enabled
  if slice(SCTLR_EL1, 0, 1) == 0b0 then {
    return Some(truncate(va, addr_size'))
  };

  // Announce translation start
  let cnp =
    if get_VARange(va) == VARange_LOWER then {
      slice(TTBR0_EL1, 0, 1)
    } else {
      slice(TTBR1_EL1, 0, 1)
    };

  let tsi : TranslationStartInfo = struct {
    ss = SS_NonSecure,
    regime = Regime_EL10,
    vmid = 0x0000,
    asid = ASID_read(),
    va = va,
    cnp = cnp,
    accdesc = accdesc,
    size = 0
  };
  sail_translation_start(tsi);

  let addrdesc =
    if va_out_of_range(va) then {
      var addrdesc = base_AddressDescriptor(accdesc);
      addrdesc.fault.statuscode = Fault_Translation;
      addrdesc.fault.write = accdesc.write;
      addrdesc.fault.access = accdesc;
      addrdesc
    } else {
      // Actual translation
      pgt_walk(va, accdesc)
    };

  // Announce result
  sail_translation_end(addrdesc);

  if is_fault(addrdesc) then {
    handle_fault(addrdesc);
    return None()
  };

  return Some(addrdesc.paddress.address)
}
$else
function translate_address(va, accdesc) = {
  return Some(va)
}
$endif
union ast =  {
  LoadRegister : (reg_index, reg_index, reg_index),
  StoreRegister : (reg_index, reg_index, reg_index),
  ExclusiveOr : (reg_index, reg_index, reg_index),
  DataMemoryBarrier : MBReqTypes,
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
  else if opc == 0b01
  then Some(LoadRegister((t,n,m)))
  else if opc == 0b00
  then Some(StoreRegister((t,n,m)))
  else None ();
}

/* LDR Xt, [Xn, Xm] */
function clause execute LoadRegister(t, n, m) = {
  /* Ask for the value of register Xn and record it in the local
   * variable base_addr */
  let base_addr = X(n);
  /* Ask for the value of register Xm and record it in the local
   * variable offset */
  let offset = X(m);
  /* Compute the address */
  let addr = base_addr + offset;
  let accdesc = create_readAccessDescriptor();
  /* Translate the virtual address into the physical address.
   * In the user mode, `translate_address` returns input address. */
  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return () // A translation fault is handled in `translate_address`.
    };
  /* The instruction can't fault now (in a real model), so update the PC */
  _PC = _PC + 4;
  /* Ask for the eight-byte value in memory starting from location
  addr and record it in the local variable data */
  let data = rMem(addr, accdesc);
  /* Ask for the value of data to be written to register Xt */
  X(t) = data;
}

/* STR Xt, [Xn, Xm] */
function clause execute StoreRegister(t, n, m) = {
  /* Ask for the value of register Xn and record it in the local
   * variable base_addr */
  let base_addr = X(n);
  /* Ask for the value of register Xm and record it in the local
   * variable offset */
  let offset = X(m);
  /* Compute the address */
  let addr = base_addr + offset;
  let accdesc = create_writeAccessDescriptor();
  /* Translate the virtual address into the physical address.
   * In the user mode, `translate_address` returns input address. */
  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return () // A translation fault is handled in `translate_address`.
    };
  /* Announce that a store into the eight bytes of memory starting
   * from location addr will be performed later */
  wMem_Addr(addr);
  /* The instruction can't fault now (in a real model), so update the PC */
  _PC = _PC + 4;
  /* Ask for the value of register Xt and record it in the local
  * variable data */
  let data = X(t);
  /* Ask for the value of data to be stored into the eight bytes of
  * memory starting from location addr */
  wMem(addr, data, accdesc);
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
  /* Increment the program counter, at the start, since no branching out possible */
  _PC = _PC + 4;
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

function clause decodeDataMemoryBarrier(0b1111) =
  Some(DataMemoryBarrier(MBReqTypes_All))

function clause decodeDataMemoryBarrier(0b1110) =
  Some(DataMemoryBarrier(MBReqTypes_Writes))

function clause decodeDataMemoryBarrier(0b1101) =
  Some(DataMemoryBarrier(MBReqTypes_Reads))

function clause decodeDataMemoryBarrier(_) = None()

function clause execute DataMemoryBarrier(types) = {
  // Update the PC
  _PC = _PC + 4;
  // Then perform the barrier
  dataMemoryBarrier(types);
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
  let accdesc = create_iFetchAccessDescriptor();
  /* Translate the virtual address into the physical address.
   * In the user mode, `translate_address` returns input address. */
  let addr : bits(addr_size) =
    match translate_address(_PC, accdesc) {
      Some(addr) => addr,
      None() => return () // A translation fault is handled in `translate_address`.
    };
  let machineCode = iFetch(addr, accdesc);
  let instr = decode(machineCode);
  match instr {
    Some (instr) => execute(instr),
    None () => assert (false, "Unsupported Encoding")
  }
}

