import Out.Sail.Sail
import Out.Sail.BitVec

open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq

abbrev MAIRType := (BitVec 64)

abbrev S1PIRType := (BitVec 64)

abbrev S2PIRType := (BitVec 64)

inductive SecurityState where | SS_NonSecure | SS_Root | SS_Realm | SS_Secure
  deriving Inhabited, BEq

abbrev PARTIDtype := (BitVec 16)

abbrev PMGtype := (BitVec 8)

inductive PARTIDspaceType where | PIdSpace_Secure | PIdSpace_Root | PIdSpace_Realm | PIdSpace_NonSecure
  deriving Inhabited, BEq

structure MPAMinfo where
  mpam_sp : PARTIDspaceType
  partid : PARTIDtype
  pmg : PMGtype
  deriving Inhabited, BEq

inductive AccessType where | AccessType_IFETCH | AccessType_GPR | AccessType_ASIMD | AccessType_SVE | AccessType_SME | AccessType_IC | AccessType_DC | AccessType_DCZero | AccessType_AT | AccessType_NV2 | AccessType_SPE | AccessType_GCS | AccessType_GPTW | AccessType_TTW
  deriving Inhabited, BEq

inductive VARange where | VARange_LOWER | VARange_UPPER
  deriving Inhabited, BEq

inductive MemAtomicOp where | MemAtomicOp_GCSSS1 | MemAtomicOp_ADD | MemAtomicOp_BIC | MemAtomicOp_EOR | MemAtomicOp_ORR | MemAtomicOp_SMAX | MemAtomicOp_SMIN | MemAtomicOp_UMAX | MemAtomicOp_UMIN | MemAtomicOp_SWP | MemAtomicOp_CAS
  deriving Inhabited, BEq

inductive CacheOp where | CacheOp_Clean | CacheOp_Invalidate | CacheOp_CleanInvalidate
  deriving Inhabited, BEq

inductive CacheOpScope where | CacheOpScope_SetWay | CacheOpScope_PoU | CacheOpScope_PoC | CacheOpScope_PoE | CacheOpScope_PoP | CacheOpScope_PoDP | CacheOpScope_PoPA | CacheOpScope_ALLU | CacheOpScope_ALLUIS
  deriving Inhabited, BEq

inductive CacheType where | CacheType_Data | CacheType_Tag | CacheType_Data_Tag | CacheType_Instruction
  deriving Inhabited, BEq

inductive CachePASpace where | CPAS_NonSecure | CPAS_Any | CPAS_RealmNonSecure | CPAS_Realm | CPAS_Root | CPAS_SecureNonSecure | CPAS_Secure
  deriving Inhabited, BEq

structure AccessDescriptor where
  acctype : AccessType
  el : (BitVec 2)
  ss : SecurityState
  acqsc : Bool
  acqpc : Bool
  relsc : Bool
  limitedordered : Bool
  exclusive : Bool
  atomicop : Bool
  modop : MemAtomicOp
  nontemporal : Bool
  read : Bool
  write : Bool
  cacheop : CacheOp
  opscope : CacheOpScope
  cachetype : CacheType
  pan : Bool
  transactional : Bool
  nonfault : Bool
  firstfault : Bool
  first : Bool
  contiguous : Bool
  streamingsve : Bool
  ls64 : Bool
  mops : Bool
  rcw : Bool
  rcws : Bool
  toplevel : Bool
  varange : VARange
  a32lsmd : Bool
  tagchecked : Bool
  tagaccess : Bool
  mpam : MPAMinfo
  deriving Inhabited, BEq

inductive MemType where | MemType_Normal | MemType_Device
  deriving Inhabited, BEq

inductive DeviceType where | DeviceType_GRE | DeviceType_nGRE | DeviceType_nGnRE | DeviceType_nGnRnE
  deriving Inhabited, BEq

structure MemAttrHints where
  attrs : (BitVec 2)
  hints : (BitVec 2)
  transient : Bool
  deriving Inhabited, BEq

inductive Shareability where | Shareability_NSH | Shareability_ISH | Shareability_OSH
  deriving Inhabited, BEq

inductive MemTagType where | MemTag_Untagged | MemTag_AllocationTagged | MemTag_CanonicallyTagged
  deriving Inhabited, BEq

structure MemoryAttributes where
  memtype : MemType
  device : DeviceType
  inner : MemAttrHints
  outer : MemAttrHints
  shareability : Shareability
  tags : MemTagType
  notagaccess : Bool
  xs : (BitVec 1)
  deriving Inhabited, BEq

inductive PASpace where | PAS_NonSecure | PAS_Secure | PAS_Root | PAS_Realm
  deriving Inhabited, BEq

structure FullAddress where
  paspace : PASpace
  address : (BitVec 56)
  deriving Inhabited, BEq

inductive GPCF where | GPCF_None | GPCF_AddressSize | GPCF_Walk | GPCF_EABT | GPCF_Fail
  deriving Inhabited, BEq

structure GPCFRecord where
  gpf : GPCF
  level : Int
  deriving Inhabited, BEq

inductive Fault where | Fault_None | Fault_AccessFlag | Fault_Alignment | Fault_Background | Fault_Domain | Fault_Permission | Fault_Translation | Fault_AddressSize | Fault_SyncExternal | Fault_SyncExternalOnWalk | Fault_SyncParity | Fault_SyncParityOnWalk | Fault_GPCFOnWalk | Fault_GPCFOnOutput | Fault_AsyncParity | Fault_AsyncExternal | Fault_TagCheck | Fault_Debug | Fault_TLBConflict | Fault_BranchTarget | Fault_HWUpdateAccessFlag | Fault_Lockdown | Fault_Exclusive | Fault_ICacheMaint
  deriving Inhabited, BEq

inductive ErrorState where | ErrorState_UC | ErrorState_UEU | ErrorState_UEO | ErrorState_UER | ErrorState_CE | ErrorState_Uncategorized | ErrorState_IMPDEF
  deriving Inhabited, BEq

structure FaultRecord where
  statuscode : Fault
  access : AccessDescriptor
  ipaddress : FullAddress
  gpcf : GPCFRecord
  paddress : FullAddress
  gpcfs2walk : Bool
  s2fs1walk : Bool
  write : Bool
  s1tagnotdata : Bool
  tagaccess : Bool
  level : Int
  extflag : (BitVec 1)
  secondstage : Bool
  assuredonly : Bool
  toplevel : Bool
  overlay : Bool
  dirtybit : Bool
  domain : (BitVec 4)
  merrorstate : ErrorState
  debugmoe : (BitVec 4)
  deriving Inhabited, BEq

inductive MBReqDomain where | MBReqDomain_Nonshareable | MBReqDomain_InnerShareable | MBReqDomain_OuterShareable | MBReqDomain_FullSystem
  deriving Inhabited, BEq

inductive MBReqTypes where | MBReqTypes_Reads | MBReqTypes_Writes | MBReqTypes_All
  deriving Inhabited, BEq

structure CacheRecord where
  acctype : AccessType
  cacheop : CacheOp
  opscope : CacheOpScope
  cachetype : CacheType
  regval : (BitVec 64)
  paddress : FullAddress
  vaddress : (BitVec 64)
  setnum : Int
  waynum : Int
  level : Int
  shareability : Shareability
  translated : Bool
  is_vmid_valid : Bool
  vmid : (BitVec 16)
  is_asid_valid : Bool
  asid : (BitVec 16)
  security : SecurityState
  cpas : CachePASpace
  deriving Inhabited, BEq

inductive Regime where | Regime_EL3 | Regime_EL30 | Regime_EL2 | Regime_EL20 | Regime_EL10
  deriving Inhabited, BEq

inductive TGx where | TGx_4KB | TGx_16KB | TGx_64KB
  deriving Inhabited, BEq

structure S1TTWParams where
  ha : (BitVec 1)
  hd : (BitVec 1)
  tbi : (BitVec 1)
  tbid : (BitVec 1)
  nfd : (BitVec 1)
  e0pd : (BitVec 1)
  d128 : (BitVec 1)
  aie : (BitVec 1)
  mair2 : MAIRType
  ds : (BitVec 1)
  ps : (BitVec 3)
  txsz : (BitVec 6)
  epan : (BitVec 1)
  dct : (BitVec 1)
  nv1 : (BitVec 1)
  cmow : (BitVec 1)
  pnch : (BitVec 1)
  disch : (BitVec 1)
  haft : (BitVec 1)
  mtx : (BitVec 1)
  skl : (BitVec 2)
  pie : (BitVec 1)
  pir : S1PIRType
  pire0 : S1PIRType
  emec : (BitVec 1)
  amec : (BitVec 1)
  t0sz : (BitVec 3)
  t1sz : (BitVec 3)
  uwxn : (BitVec 1)
  tgx : TGx
  irgn : (BitVec 2)
  orgn : (BitVec 2)
  sh : (BitVec 2)
  hpd : (BitVec 1)
  ee : (BitVec 1)
  wxn : (BitVec 1)
  ntlsmd : (BitVec 1)
  dc : (BitVec 1)
  sif : (BitVec 1)
  mair : MAIRType
  deriving Inhabited, BEq

structure S2TTWParams where
  ha : (BitVec 1)
  hd : (BitVec 1)
  sl2 : (BitVec 1)
  ds : (BitVec 1)
  d128 : (BitVec 1)
  sw : (BitVec 1)
  nsw : (BitVec 1)
  sa : (BitVec 1)
  nsa : (BitVec 1)
  ps : (BitVec 3)
  txsz : (BitVec 6)
  fwb : (BitVec 1)
  cmow : (BitVec 1)
  skl : (BitVec 2)
  s2pie : (BitVec 1)
  s2pir : S2PIRType
  tl0 : (BitVec 1)
  tl1 : (BitVec 1)
  assuredonly : (BitVec 1)
  haft : (BitVec 1)
  emec : (BitVec 1)
  s : (BitVec 1)
  t0sz : (BitVec 4)
  tgx : TGx
  sl0 : (BitVec 2)
  irgn : (BitVec 2)
  orgn : (BitVec 2)
  sh : (BitVec 2)
  ee : (BitVec 1)
  ptw : (BitVec 1)
  vm : (BitVec 1)
  deriving Inhabited, BEq

structure TranslationInfo where
  regime : Regime
  vmid : (Option (BitVec 16))
  asid : (Option (BitVec 16))
  va : (BitVec 64)
  s1level : (Option Int)
  s2info : (Option ((BitVec 64) × Int))
  s1params : (Option S1TTWParams)
  s2params : (Option S2TTWParams)
  memattrs : MemoryAttributes
  deriving Inhabited, BEq

inductive TLBILevel where | TLBILevel_Any | TLBILevel_Last
  deriving Inhabited, BEq

inductive TLBIOp where | TLBIOp_DALL | TLBIOp_DASID | TLBIOp_DVA | TLBIOp_IALL | TLBIOp_IASID | TLBIOp_IVA | TLBIOp_ALL | TLBIOp_ASID | TLBIOp_IPAS2 | TLBIPOp_IPAS2 | TLBIOp_VAA | TLBIOp_VA | TLBIPOp_VAA | TLBIPOp_VA | TLBIOp_VMALL | TLBIOp_VMALLS12 | TLBIOp_RIPAS2 | TLBIPOp_RIPAS2 | TLBIOp_RVAA | TLBIOp_RVA | TLBIPOp_RVAA | TLBIPOp_RVA | TLBIOp_RPA | TLBIOp_PAALL
  deriving Inhabited, BEq

inductive TLBIMemAttr where | TLBI_AllAttr | TLBI_ExcludeXS
  deriving Inhabited, BEq

structure TLBIRecord where
  op : TLBIOp
  from_aarch64 : Bool
  security : SecurityState
  regime : Regime
  vmid : (BitVec 16)
  asid : (BitVec 16)
  level : TLBILevel
  attr : TLBIMemAttr
  ipaspace : PASpace
  address : (BitVec 64)
  end_address_name : (BitVec 64)
  d64 : Bool
  d128 : Bool
  ttl : (BitVec 4)
  tg : (BitVec 2)
  deriving Inhabited, BEq

inductive arm_acc_type where
  | SAcc_ASIMD (_ : Bool)
  | SAcc_SVE (_ : Bool)
  | SAcc_SME (_ : Bool)
  | SAcc_IC (_ : Unit)
  | SAcc_DC (_ : Unit)
  | SAcc_DCZero (_ : Unit)
  | SAcc_AT (_ : Unit)
  | SAcc_NV2 (_ : Unit)
  | SAcc_SPE (_ : Unit)
  | SAcc_GCS (_ : Unit)
  | SAcc_GPTW (_ : Unit)
  deriving Inhabited, BEq

structure TLBIInfo where
  rec' : TLBIRecord
  shareability : Shareability
  deriving Inhabited, BEq

structure DxB where
  domain : MBReqDomain
  types : MBReqTypes
  nXS : Bool
  deriving Inhabited, BEq

inductive Barrier where
  | Barrier_DSB (_ : DxB)
  | Barrier_DMB (_ : DxB)
  | Barrier_ISB (_ : Unit)
  | Barrier_SSBB (_ : Unit)
  | Barrier_PSSBB (_ : Unit)
  | Barrier_SB (_ : Unit)
  deriving Inhabited, BEq

abbrev boolean := (BitVec 1)

abbrev integer := Int

abbrev uinteger := Nat

abbrev reg_index := Nat

inductive ast where
  | LoadRegister (_ : (reg_index × reg_index × reg_index))
  | StoreRegister (_ : (reg_index × reg_index × reg_index))
  | ExclusiveOr (_ : (reg_index × reg_index × reg_index))
  | DataMemoryBarrier (_ : Unit)
  | CompareAndBranch (_ : (reg_index × (BitVec 64)))
  deriving Inhabited, BEq

inductive Register : Type where
  | R0
  | R1
  | R2
  | R3
  | R4
  | R5
  | R6
  | R7
  | R8
  | R9
  | R10
  | R11
  | R12
  | R13
  | R14
  | R15
  | R16
  | R17
  | R18
  | R19
  | R20
  | R21
  | R22
  | R23
  | R24
  | R25
  | R26
  | R27
  | R28
  | R29
  | R30
  | _PC
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .R0 => (BitVec 64)
  | .R1 => (BitVec 64)
  | .R2 => (BitVec 64)
  | .R3 => (BitVec 64)
  | .R4 => (BitVec 64)
  | .R5 => (BitVec 64)
  | .R6 => (BitVec 64)
  | .R7 => (BitVec 64)
  | .R8 => (BitVec 64)
  | .R9 => (BitVec 64)
  | .R10 => (BitVec 64)
  | .R11 => (BitVec 64)
  | .R12 => (BitVec 64)
  | .R13 => (BitVec 64)
  | .R14 => (BitVec 64)
  | .R15 => (BitVec 64)
  | .R16 => (BitVec 64)
  | .R17 => (BitVec 64)
  | .R18 => (BitVec 64)
  | .R19 => (BitVec 64)
  | .R20 => (BitVec 64)
  | .R21 => (BitVec 64)
  | .R22 => (BitVec 64)
  | .R23 => (BitVec 64)
  | .R24 => (BitVec 64)
  | .R25 => (BitVec 64)
  | .R26 => (BitVec 64)
  | .R27 => (BitVec 64)
  | .R28 => (BitVec 64)
  | .R29 => (BitVec 64)
  | .R30 => (BitVec 64)
  | ._PC => (BitVec 64)

instance : Inhabited (RegisterRef RegisterType (BitVec 64)) where
  default := .Reg _PC
abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception

instance : Arch where
  va_size := 64
  pa := (BitVec 56)
  abort := Fault
  translation := (Option TranslationInfo)
  fault := (Option FaultRecord)
  tlb_op := TLBIInfo
  cache_op := CacheRecord
  barrier := Barrier
  arch_ak := arm_acc_type
  sys_reg_id := Unit


XXXXXXXXX

import Out.ReadWrite

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace Out.Functions

open option
open ast
open arm_acc_type
open VARange
open TLBIOp
open TLBIMemAttr
open TLBILevel
open TGx
open Shareability
open SecurityState
open Register
open Regime
open PASpace
open PARTIDspaceType
open MemType
open MemTagType
open MemAtomicOp
open MBReqTypes
open MBReqDomain
open GPCF
open Fault
open ErrorState
open DeviceType
open CacheType
open CachePASpace
open CacheOpScope
open CacheOp
open Barrier
open AccessType

def pa_bits (bv : (BitVec 56)) : (BitVec 64) :=
  (Sail.BitVec.zeroExtend bv 64)

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg _PC (← (undefined_bitvector 64))
  writeReg R30 (← (undefined_bitvector 64))
  writeReg R29 (← (undefined_bitvector 64))
  writeReg R28 (← (undefined_bitvector 64))
  writeReg R27 (← (undefined_bitvector 64))
  writeReg R26 (← (undefined_bitvector 64))
  writeReg R25 (← (undefined_bitvector 64))
  writeReg R24 (← (undefined_bitvector 64))
  writeReg R23 (← (undefined_bitvector 64))
  writeReg R22 (← (undefined_bitvector 64))
  writeReg R21 (← (undefined_bitvector 64))
  writeReg R20 (← (undefined_bitvector 64))
  writeReg R19 (← (undefined_bitvector 64))
  writeReg R18 (← (undefined_bitvector 64))
  writeReg R17 (← (undefined_bitvector 64))
  writeReg R16 (← (undefined_bitvector 64))
  writeReg R15 (← (undefined_bitvector 64))
  writeReg R14 (← (undefined_bitvector 64))
  writeReg R13 (← (undefined_bitvector 64))
  writeReg R12 (← (undefined_bitvector 64))
  writeReg R11 (← (undefined_bitvector 64))
  writeReg R10 (← (undefined_bitvector 64))
  writeReg R9 (← (undefined_bitvector 64))
  writeReg R8 (← (undefined_bitvector 64))
  writeReg R7 (← (undefined_bitvector 64))
  writeReg R6 (← (undefined_bitvector 64))
  writeReg R5 (← (undefined_bitvector 64))
  writeReg R4 (← (undefined_bitvector 64))
  writeReg R3 (← (undefined_bitvector 64))
  writeReg R2 (← (undefined_bitvector 64))
  writeReg R1 (← (undefined_bitvector 64))
  writeReg R0 (← (undefined_bitvector 64))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())


end Out.Functions
