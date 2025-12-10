import Out.Sail.Sail
import Out.Sail.BitVec

open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV2

abbrev bit := (BitVec 1)

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq, Repr
  open option

inductive SecurityState where | SS_NonSecure | SS_Root | SS_Realm | SS_Secure
  deriving BEq, Inhabited, Repr
  open SecurityState

abbrev PARTIDtype := (BitVec 16)

abbrev PMGtype := (BitVec 8)

inductive PARTIDspaceType where | PIdSpace_Secure | PIdSpace_Root | PIdSpace_Realm | PIdSpace_NonSecure
  deriving BEq, Inhabited, Repr
  open PARTIDspaceType

structure MPAMinfo where
  mpam_sp : PARTIDspaceType
  partid : PARTIDtype
  pmg : PMGtype
  deriving BEq, Inhabited, Repr

inductive AccessType where | AccessType_IFETCH | AccessType_GPR | AccessType_ASIMD | AccessType_SVE | AccessType_SME | AccessType_IC | AccessType_DC | AccessType_DCZero | AccessType_AT | AccessType_NV2 | AccessType_SPE | AccessType_GCS | AccessType_GPTW | AccessType_TTW
  deriving BEq, Inhabited, Repr
  open AccessType

inductive VARange where | VARange_LOWER | VARange_UPPER
  deriving BEq, Inhabited, Repr
  open VARange

inductive MemAtomicOp where | MemAtomicOp_GCSSS1 | MemAtomicOp_ADD | MemAtomicOp_BIC | MemAtomicOp_EOR | MemAtomicOp_ORR | MemAtomicOp_SMAX | MemAtomicOp_SMIN | MemAtomicOp_UMAX | MemAtomicOp_UMIN | MemAtomicOp_SWP | MemAtomicOp_CAS
  deriving BEq, Inhabited, Repr
  open MemAtomicOp

inductive CacheOp where | CacheOp_Clean | CacheOp_Invalidate | CacheOp_CleanInvalidate
  deriving BEq, Inhabited, Repr
  open CacheOp

inductive CacheOpScope where | CacheOpScope_SetWay | CacheOpScope_PoU | CacheOpScope_PoC | CacheOpScope_PoE | CacheOpScope_PoP | CacheOpScope_PoDP | CacheOpScope_PoPA | CacheOpScope_ALLU | CacheOpScope_ALLUIS
  deriving BEq, Inhabited, Repr
  open CacheOpScope

inductive CacheType where | CacheType_Data | CacheType_Tag | CacheType_Data_Tag | CacheType_Instruction
  deriving BEq, Inhabited, Repr
  open CacheType

inductive CachePASpace where | CPAS_NonSecure | CPAS_Any | CPAS_RealmNonSecure | CPAS_Realm | CPAS_Root | CPAS_SecureNonSecure | CPAS_Secure
  deriving BEq, Inhabited, Repr
  open CachePASpace

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
  deriving BEq, Inhabited, Repr

inductive MemType where | MemType_Normal | MemType_Device
  deriving BEq, Inhabited, Repr
  open MemType

inductive DeviceType where | DeviceType_GRE | DeviceType_nGRE | DeviceType_nGnRE | DeviceType_nGnRnE
  deriving BEq, Inhabited, Repr
  open DeviceType

structure MemAttrHints where
  attrs : (BitVec 2)
  hints : (BitVec 2)
  transient : Bool
  deriving BEq, Inhabited, Repr

inductive Shareability where | Shareability_NSH | Shareability_ISH | Shareability_OSH
  deriving BEq, Inhabited, Repr
  open Shareability

inductive MemTagType where | MemTag_Untagged | MemTag_AllocationTagged | MemTag_CanonicallyTagged
  deriving BEq, Inhabited, Repr
  open MemTagType

structure MemoryAttributes where
  memtype : MemType
  device : DeviceType
  inner : MemAttrHints
  outer : MemAttrHints
  shareability : Shareability
  tags : MemTagType
  notagaccess : Bool
  xs : (BitVec 1)
  deriving BEq, Inhabited, Repr

inductive PASpace where | PAS_NonSecure | PAS_Secure | PAS_Root | PAS_Realm
  deriving BEq, Inhabited, Repr
  open PASpace

structure FullAddress where
  paspace : PASpace
  address : (BitVec 56)
  deriving BEq, Inhabited, Repr

inductive GPCF where | GPCF_None | GPCF_AddressSize | GPCF_Walk | GPCF_EABT | GPCF_Fail
  deriving BEq, Inhabited, Repr
  open GPCF

structure GPCFRecord where
  gpf : GPCF
  level : Int
  deriving BEq, Inhabited, Repr

inductive Fault where | Fault_None | Fault_AccessFlag | Fault_Alignment | Fault_Background | Fault_Domain | Fault_Permission | Fault_Translation | Fault_AddressSize | Fault_SyncExternal | Fault_SyncExternalOnWalk | Fault_SyncParity | Fault_SyncParityOnWalk | Fault_GPCFOnWalk | Fault_GPCFOnOutput | Fault_AsyncParity | Fault_AsyncExternal | Fault_TagCheck | Fault_Debug | Fault_TLBConflict | Fault_BranchTarget | Fault_HWUpdateAccessFlag | Fault_Lockdown | Fault_Exclusive | Fault_ICacheMaint
  deriving BEq, Inhabited, Repr
  open Fault

inductive ErrorState where | ErrorState_UC | ErrorState_UEU | ErrorState_UEO | ErrorState_UER | ErrorState_CE | ErrorState_Uncategorized | ErrorState_IMPDEF
  deriving BEq, Inhabited, Repr
  open ErrorState

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
  deriving BEq, Inhabited, Repr

inductive MBReqDomain where | MBReqDomain_Nonshareable | MBReqDomain_InnerShareable | MBReqDomain_OuterShareable | MBReqDomain_FullSystem
  deriving BEq, Inhabited, Repr
  open MBReqDomain

inductive MBReqTypes where | MBReqTypes_Reads | MBReqTypes_Writes | MBReqTypes_All
  deriving BEq, Inhabited, Repr
  open MBReqTypes

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
  deriving BEq, Inhabited, Repr

inductive Regime where | Regime_EL3 | Regime_EL30 | Regime_EL2 | Regime_EL20 | Regime_EL10
  deriving BEq, Inhabited, Repr
  open Regime

inductive TGx where | TGx_4KB | TGx_16KB | TGx_64KB
  deriving BEq, Inhabited, Repr
  open TGx

structure TLBContext where
  ss : SecurityState
  regime : Regime
  vmid : (BitVec 16)
  asid : (BitVec 16)
  nG : (BitVec 1)
  ipaspace : PASpace
  includes_s1_name : Bool
  includes_s2_name : Bool
  includes_gpt_name : Bool
  ia : (BitVec 64)
  tg : TGx
  cnp : (BitVec 1)
  level : Int
  isd128 : Bool
  xs : (BitVec 1)
  deriving BEq, Inhabited, Repr

structure AddressDescriptor where
  fault : FaultRecord
  memattrs : MemoryAttributes
  paddress : FullAddress
  tlbcontext : TLBContext
  s1assured : Bool
  s2fs1mro : Bool
  mecid : (BitVec 16)
  vaddress : (BitVec 64)
  deriving BEq, Inhabited, Repr

structure TranslationStartInfo where
  ss : SecurityState
  regime : Regime
  vmid : (BitVec 16)
  asid : (BitVec 16)
  va : (BitVec 64)
  cnp : (BitVec 1)
  accdesc : AccessDescriptor
  size : Int
  deriving BEq, Inhabited, Repr

inductive TLBILevel where | TLBILevel_Any | TLBILevel_Last
  deriving BEq, Inhabited, Repr
  open TLBILevel

inductive TLBIOp where | TLBIOp_DALL | TLBIOp_DASID | TLBIOp_DVA | TLBIOp_IALL | TLBIOp_IASID | TLBIOp_IVA | TLBIOp_ALL | TLBIOp_ASID | TLBIOp_IPAS2 | TLBIPOp_IPAS2 | TLBIOp_VAA | TLBIOp_VA | TLBIPOp_VAA | TLBIPOp_VA | TLBIOp_VMALL | TLBIOp_VMALLS12 | TLBIOp_RIPAS2 | TLBIPOp_RIPAS2 | TLBIOp_RVAA | TLBIOp_RVA | TLBIPOp_RVAA | TLBIPOp_RVA | TLBIOp_RPA | TLBIOp_PAALL
  deriving BEq, Inhabited, Repr
  open TLBIOp

inductive TLBIMemAttr where | TLBI_AllAttr | TLBI_ExcludeXS
  deriving BEq, Inhabited, Repr
  open TLBIMemAttr

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
  deriving BEq, Inhabited, Repr

structure TLBIInfo where
  rec' : TLBIRecord
  shareability : Shareability
  deriving BEq, Inhabited, Repr

structure DxB where
  domain : MBReqDomain
  types : MBReqTypes
  nXS : Bool
  deriving BEq, Inhabited, Repr

inductive Barrier where
  | Barrier_DSB (_ : DxB)
  | Barrier_DMB (_ : DxB)
  | Barrier_ISB (_ : Unit)
  | Barrier_SSBB (_ : Unit)
  | Barrier_PSSBB (_ : Unit)
  | Barrier_SB (_ : Unit)
  deriving Inhabited, BEq, Repr
  open Barrier

abbrev reg_index := Nat

abbrev addr_size : Int := 64

abbrev addr_space := Unit

abbrev abort := Unit

inductive ast where
  | LoadRegister (_ : (reg_index × reg_index × reg_index))
  | StoreRegister (_ : (reg_index × reg_index × reg_index))
  | ExclusiveOr (_ : (reg_index × reg_index × reg_index))
  | DataMemoryBarrier (_ : MBReqTypes)
  | CompareAndBranch (_ : (reg_index × (BitVec 64)))
  deriving Inhabited, BEq, Repr
  open ast

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
  deriving DecidableEq, Hashable, Repr
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
abbrev SailME := PreSailME RegisterType trivialChoiceSource exception

def mem_acc_is_explicit (acc : AccessDescriptor) : Bool :=
  (BEq.beq acc.acctype AccessType_GPR)

def mem_acc_is_ifetch (acc : AccessDescriptor) : Bool :=
  (BEq.beq acc.acctype AccessType_IFETCH)

def mem_acc_is_ttw (acc : AccessDescriptor) : Bool :=
  (BEq.beq acc.acctype AccessType_TTW)

def mem_acc_is_relaxed (acc : AccessDescriptor) : Bool :=
  ((BEq.beq acc.acctype AccessType_GPR) && ((! acc.acqpc) && ((! acc.acqsc) && (! acc.relsc))))

def mem_acc_is_rel_acq_rcpc (acc : AccessDescriptor) : Bool :=
  ((BEq.beq acc.acctype AccessType_GPR) && acc.acqpc)

def mem_acc_is_rel_acq_rcsc (acc : AccessDescriptor) : Bool :=
  ((BEq.beq acc.acctype AccessType_GPR) && (acc.acqsc || acc.relsc))

def mem_acc_is_standalone (acc : AccessDescriptor) : Bool :=
  ((BEq.beq acc.acctype AccessType_GPR) && ((! acc.exclusive) && (! acc.atomicop)))

def mem_acc_is_exclusive (acc : AccessDescriptor) : Bool :=
  ((BEq.beq acc.acctype AccessType_GPR) && acc.exclusive)

def mem_acc_is_atomic_rmw (acc : AccessDescriptor) : Bool :=
  ((BEq.beq acc.acctype AccessType_GPR) && acc.atomicop)

@[reducible]
instance : Arch where
  addr_size := addr_size
  addr_space := addr_space
  CHERI := false
  cap_size_log := 0
  mem_acc := AccessDescriptor
  mem_acc_is_explicit := mem_acc_is_explicit
  mem_acc_is_ifetch := mem_acc_is_ifetch
  mem_acc_is_ttw := mem_acc_is_ttw
  mem_acc_is_relaxed := mem_acc_is_relaxed
  mem_acc_is_rel_acq_rcpc := mem_acc_is_rel_acq_rcpc
  mem_acc_is_rel_acq_rcsc := mem_acc_is_rel_acq_rcsc
  mem_acc_is_standalone := mem_acc_is_standalone
  mem_acc_is_exclusive := mem_acc_is_exclusive
  mem_acc_is_atomic_rmw := mem_acc_is_atomic_rmw
  trans_start := Unit
  trans_end := Unit
  abort := abort
  barrier := Barrier
  cache_op := Unit
  tlbi := Unit
  exn := Unit
  sys_reg_id := Unit
XXXXXXXXX

import Out.Sail.Sail
import Out.Sail.BitVec
import Out.Sail.IntRange
import Out.Defs
import Out.Specialization
import Out.FakeReal

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV2

namespace Out.Functions

open option
open ast
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

/-- Type quantifiers: k_ex10021_ : Bool, k_ex10020_ : Bool -/
def neq_bool (x : Bool) (y : Bool) : Bool :=
  (! (x == y))

/-- Type quantifiers: k_n : Nat, y : Nat, k_n ≥ 0 ∧ y ≥ 0 -/
def eq_bits_int (x : (BitVec k_n)) (y : Nat) : Bool :=
  ((BitVec.toNatInt x) == y)

/-- Type quantifiers: x : Int -/
def __id (x : Int) : Int :=
  x

/-- Type quantifiers: n : Int, m : Int -/
def _shl_int_general (m : Int) (n : Int) : Int :=
  if ((n ≥b 0) : Bool)
  then (Int.shiftl m n)
  else (Int.shiftr m (Neg.neg n))

/-- Type quantifiers: n : Int, m : Int -/
def _shr_int_general (m : Int) (n : Int) : Int :=
  if ((n ≥b 0) : Bool)
  then (Int.shiftr m n)
  else (Int.shiftl m (Neg.neg n))

/-- Type quantifiers: m : Int, n : Int -/
def fdiv_int (n : Int) (m : Int) : Int :=
  if (((n <b 0) && (m >b 0)) : Bool)
  then ((Int.tdiv (n +i 1) m) -i 1)
  else
    (if (((n >b 0) && (m <b 0)) : Bool)
    then ((Int.tdiv (n -i 1) m) -i 1)
    else (Int.tdiv n m))

/-- Type quantifiers: m : Int, n : Int -/
def fmod_int (n : Int) (m : Int) : Int :=
  (n -i (m *i (fdiv_int n m)))

/-- Type quantifiers: len : Nat, k_v : Nat, len ≥ 0 ∧ k_v ≥ 0 -/
def sail_mask (len : Nat) (v : (BitVec k_v)) : (BitVec len) :=
  if ((len ≤b (Sail.BitVec.length v)) : Bool)
  then (Sail.BitVec.truncate v len)
  else (Sail.BitVec.zeroExtend v len)

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def sail_ones (n : Nat) : (BitVec n) :=
  (Complement.complement (BitVec.zero n))

/-- Type quantifiers: l : Int, i : Int, n : Nat, n ≥ 0 -/
def slice_mask {n : _} (i : Int) (l : Int) : (BitVec n) :=
  if ((l ≥b n) : Bool)
  then ((sail_ones n) <<< i)
  else
    (let one : (BitVec n) := (sail_mask n (1#1 : (BitVec 1)))
    (((one <<< l) - one) <<< i))

/-- Type quantifiers: n : Nat, n > 0 -/
def to_bytes_le {n : _} (b : (BitVec (8 * n))) : (Vector (BitVec 8) n) := Id.run do
  let res := (vectorInit (BitVec.zero 8))
  let loop_i_lower := 0
  let loop_i_upper := (n -i 1)
  let mut loop_vars := res
  for i in [loop_i_lower:loop_i_upper:1]i do
    let res := loop_vars
    loop_vars := (vectorUpdate res i (Sail.BitVec.extractLsb b ((8 *i i) +i 7) (8 *i i)))
  (pure loop_vars)

/-- Type quantifiers: n : Nat, n > 0 -/
def from_bytes_le {n : _} (v : (Vector (BitVec 8) n)) : (BitVec (8 * n)) := Id.run do
  let res := (BitVec.zero (8 *i n))
  let loop_i_lower := 0
  let loop_i_upper := (n -i 1)
  let mut loop_vars := res
  for i in [loop_i_lower:loop_i_upper:1]i do
    let res := loop_vars
    loop_vars := (Sail.BitVec.updateSubrange res ((8 *i i) +i 7) (8 *i i) (GetElem?.getElem! v i))
  (pure loop_vars)

/-- Type quantifiers: k_a : Type -/
def is_none (opt : (Option k_a)) : Bool :=
  match opt with
  | .some _ => false
  | none => true

/-- Type quantifiers: k_a : Type -/
def is_some (opt : (Option k_a)) : Bool :=
  match opt with
  | .some _ => true
  | none => false

/-- Type quantifiers: k_n : Int -/
def concat_str_bits (str : String) (x : (BitVec k_n)) : String :=
  (HAppend.hAppend str (BitVec.toFormatted x))

/-- Type quantifiers: x : Int -/
def concat_str_dec (str : String) (x : Int) : String :=
  (HAppend.hAppend str (Int.repr x))

def undefined_SecurityState (_ : Unit) : SailM SecurityState := do
  (internal_pick [SS_NonSecure, SS_Root, SS_Realm, SS_Secure])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def SecurityState_of_num (arg_ : Nat) : SecurityState :=
  match arg_ with
  | 0 => SS_NonSecure
  | 1 => SS_Root
  | 2 => SS_Realm
  | _ => SS_Secure

def num_of_SecurityState (arg_ : SecurityState) : Int :=
  match arg_ with
  | SS_NonSecure => 0
  | SS_Root => 1
  | SS_Realm => 2
  | SS_Secure => 3

def undefined_PARTIDspaceType (_ : Unit) : SailM PARTIDspaceType := do
  (internal_pick [PIdSpace_Secure, PIdSpace_Root, PIdSpace_Realm, PIdSpace_NonSecure])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def PARTIDspaceType_of_num (arg_ : Nat) : PARTIDspaceType :=
  match arg_ with
  | 0 => PIdSpace_Secure
  | 1 => PIdSpace_Root
  | 2 => PIdSpace_Realm
  | _ => PIdSpace_NonSecure

def num_of_PARTIDspaceType (arg_ : PARTIDspaceType) : Int :=
  match arg_ with
  | PIdSpace_Secure => 0
  | PIdSpace_Root => 1
  | PIdSpace_Realm => 2
  | PIdSpace_NonSecure => 3

def undefined_MPAMinfo (_ : Unit) : SailM MPAMinfo := do
  (pure { mpam_sp := ← (undefined_PARTIDspaceType ())
          partid := ← (undefined_bitvector 16)
          pmg := ← (undefined_bitvector 8) })

def undefined_AccessType (_ : Unit) : SailM AccessType := do
  (internal_pick
    [AccessType_IFETCH, AccessType_GPR, AccessType_ASIMD, AccessType_SVE, AccessType_SME, AccessType_IC, AccessType_DC, AccessType_DCZero, AccessType_AT, AccessType_NV2, AccessType_SPE, AccessType_GCS, AccessType_GPTW, AccessType_TTW])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 13 -/
def AccessType_of_num (arg_ : Nat) : AccessType :=
  match arg_ with
  | 0 => AccessType_IFETCH
  | 1 => AccessType_GPR
  | 2 => AccessType_ASIMD
  | 3 => AccessType_SVE
  | 4 => AccessType_SME
  | 5 => AccessType_IC
  | 6 => AccessType_DC
  | 7 => AccessType_DCZero
  | 8 => AccessType_AT
  | 9 => AccessType_NV2
  | 10 => AccessType_SPE
  | 11 => AccessType_GCS
  | 12 => AccessType_GPTW
  | _ => AccessType_TTW

def num_of_AccessType (arg_ : AccessType) : Int :=
  match arg_ with
  | AccessType_IFETCH => 0
  | AccessType_GPR => 1
  | AccessType_ASIMD => 2
  | AccessType_SVE => 3
  | AccessType_SME => 4
  | AccessType_IC => 5
  | AccessType_DC => 6
  | AccessType_DCZero => 7
  | AccessType_AT => 8
  | AccessType_NV2 => 9
  | AccessType_SPE => 10
  | AccessType_GCS => 11
  | AccessType_GPTW => 12
  | AccessType_TTW => 13

def undefined_VARange (_ : Unit) : SailM VARange := do
  (internal_pick [VARange_LOWER, VARange_UPPER])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def VARange_of_num (arg_ : Nat) : VARange :=
  match arg_ with
  | 0 => VARange_LOWER
  | _ => VARange_UPPER

def num_of_VARange (arg_ : VARange) : Int :=
  match arg_ with
  | VARange_LOWER => 0
  | VARange_UPPER => 1

def undefined_MemAtomicOp (_ : Unit) : SailM MemAtomicOp := do
  (internal_pick
    [MemAtomicOp_GCSSS1, MemAtomicOp_ADD, MemAtomicOp_BIC, MemAtomicOp_EOR, MemAtomicOp_ORR, MemAtomicOp_SMAX, MemAtomicOp_SMIN, MemAtomicOp_UMAX, MemAtomicOp_UMIN, MemAtomicOp_SWP, MemAtomicOp_CAS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 10 -/
def MemAtomicOp_of_num (arg_ : Nat) : MemAtomicOp :=
  match arg_ with
  | 0 => MemAtomicOp_GCSSS1
  | 1 => MemAtomicOp_ADD
  | 2 => MemAtomicOp_BIC
  | 3 => MemAtomicOp_EOR
  | 4 => MemAtomicOp_ORR
  | 5 => MemAtomicOp_SMAX
  | 6 => MemAtomicOp_SMIN
  | 7 => MemAtomicOp_UMAX
  | 8 => MemAtomicOp_UMIN
  | 9 => MemAtomicOp_SWP
  | _ => MemAtomicOp_CAS

def num_of_MemAtomicOp (arg_ : MemAtomicOp) : Int :=
  match arg_ with
  | MemAtomicOp_GCSSS1 => 0
  | MemAtomicOp_ADD => 1
  | MemAtomicOp_BIC => 2
  | MemAtomicOp_EOR => 3
  | MemAtomicOp_ORR => 4
  | MemAtomicOp_SMAX => 5
  | MemAtomicOp_SMIN => 6
  | MemAtomicOp_UMAX => 7
  | MemAtomicOp_UMIN => 8
  | MemAtomicOp_SWP => 9
  | MemAtomicOp_CAS => 10

def undefined_CacheOp (_ : Unit) : SailM CacheOp := do
  (internal_pick [CacheOp_Clean, CacheOp_Invalidate, CacheOp_CleanInvalidate])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def CacheOp_of_num (arg_ : Nat) : CacheOp :=
  match arg_ with
  | 0 => CacheOp_Clean
  | 1 => CacheOp_Invalidate
  | _ => CacheOp_CleanInvalidate

def num_of_CacheOp (arg_ : CacheOp) : Int :=
  match arg_ with
  | CacheOp_Clean => 0
  | CacheOp_Invalidate => 1
  | CacheOp_CleanInvalidate => 2

def undefined_CacheOpScope (_ : Unit) : SailM CacheOpScope := do
  (internal_pick
    [CacheOpScope_SetWay, CacheOpScope_PoU, CacheOpScope_PoC, CacheOpScope_PoE, CacheOpScope_PoP, CacheOpScope_PoDP, CacheOpScope_PoPA, CacheOpScope_ALLU, CacheOpScope_ALLUIS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 8 -/
def CacheOpScope_of_num (arg_ : Nat) : CacheOpScope :=
  match arg_ with
  | 0 => CacheOpScope_SetWay
  | 1 => CacheOpScope_PoU
  | 2 => CacheOpScope_PoC
  | 3 => CacheOpScope_PoE
  | 4 => CacheOpScope_PoP
  | 5 => CacheOpScope_PoDP
  | 6 => CacheOpScope_PoPA
  | 7 => CacheOpScope_ALLU
  | _ => CacheOpScope_ALLUIS

def num_of_CacheOpScope (arg_ : CacheOpScope) : Int :=
  match arg_ with
  | CacheOpScope_SetWay => 0
  | CacheOpScope_PoU => 1
  | CacheOpScope_PoC => 2
  | CacheOpScope_PoE => 3
  | CacheOpScope_PoP => 4
  | CacheOpScope_PoDP => 5
  | CacheOpScope_PoPA => 6
  | CacheOpScope_ALLU => 7
  | CacheOpScope_ALLUIS => 8

def undefined_CacheType (_ : Unit) : SailM CacheType := do
  (internal_pick [CacheType_Data, CacheType_Tag, CacheType_Data_Tag, CacheType_Instruction])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def CacheType_of_num (arg_ : Nat) : CacheType :=
  match arg_ with
  | 0 => CacheType_Data
  | 1 => CacheType_Tag
  | 2 => CacheType_Data_Tag
  | _ => CacheType_Instruction

def num_of_CacheType (arg_ : CacheType) : Int :=
  match arg_ with
  | CacheType_Data => 0
  | CacheType_Tag => 1
  | CacheType_Data_Tag => 2
  | CacheType_Instruction => 3

def undefined_CachePASpace (_ : Unit) : SailM CachePASpace := do
  (internal_pick
    [CPAS_NonSecure, CPAS_Any, CPAS_RealmNonSecure, CPAS_Realm, CPAS_Root, CPAS_SecureNonSecure, CPAS_Secure])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 6 -/
def CachePASpace_of_num (arg_ : Nat) : CachePASpace :=
  match arg_ with
  | 0 => CPAS_NonSecure
  | 1 => CPAS_Any
  | 2 => CPAS_RealmNonSecure
  | 3 => CPAS_Realm
  | 4 => CPAS_Root
  | 5 => CPAS_SecureNonSecure
  | _ => CPAS_Secure

def num_of_CachePASpace (arg_ : CachePASpace) : Int :=
  match arg_ with
  | CPAS_NonSecure => 0
  | CPAS_Any => 1
  | CPAS_RealmNonSecure => 2
  | CPAS_Realm => 3
  | CPAS_Root => 4
  | CPAS_SecureNonSecure => 5
  | CPAS_Secure => 6

def undefined_AccessDescriptor (_ : Unit) : SailM AccessDescriptor := do
  (pure { acctype := ← (undefined_AccessType ())
          el := ← (undefined_bitvector 2)
          ss := ← (undefined_SecurityState ())
          acqsc := ← (undefined_bool ())
          acqpc := ← (undefined_bool ())
          relsc := ← (undefined_bool ())
          limitedordered := ← (undefined_bool ())
          exclusive := ← (undefined_bool ())
          atomicop := ← (undefined_bool ())
          modop := ← (undefined_MemAtomicOp ())
          nontemporal := ← (undefined_bool ())
          read := ← (undefined_bool ())
          write := ← (undefined_bool ())
          cacheop := ← (undefined_CacheOp ())
          opscope := ← (undefined_CacheOpScope ())
          cachetype := ← (undefined_CacheType ())
          pan := ← (undefined_bool ())
          transactional := ← (undefined_bool ())
          nonfault := ← (undefined_bool ())
          firstfault := ← (undefined_bool ())
          first := ← (undefined_bool ())
          contiguous := ← (undefined_bool ())
          streamingsve := ← (undefined_bool ())
          ls64 := ← (undefined_bool ())
          mops := ← (undefined_bool ())
          rcw := ← (undefined_bool ())
          rcws := ← (undefined_bool ())
          toplevel := ← (undefined_bool ())
          varange := ← (undefined_VARange ())
          a32lsmd := ← (undefined_bool ())
          tagchecked := ← (undefined_bool ())
          tagaccess := ← (undefined_bool ())
          mpam := ← (undefined_MPAMinfo ()) })

def undefined_MemType (_ : Unit) : SailM MemType := do
  (internal_pick [MemType_Normal, MemType_Device])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def MemType_of_num (arg_ : Nat) : MemType :=
  match arg_ with
  | 0 => MemType_Normal
  | _ => MemType_Device

def num_of_MemType (arg_ : MemType) : Int :=
  match arg_ with
  | MemType_Normal => 0
  | MemType_Device => 1

def undefined_DeviceType (_ : Unit) : SailM DeviceType := do
  (internal_pick [DeviceType_GRE, DeviceType_nGRE, DeviceType_nGnRE, DeviceType_nGnRnE])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def DeviceType_of_num (arg_ : Nat) : DeviceType :=
  match arg_ with
  | 0 => DeviceType_GRE
  | 1 => DeviceType_nGRE
  | 2 => DeviceType_nGnRE
  | _ => DeviceType_nGnRnE

def num_of_DeviceType (arg_ : DeviceType) : Int :=
  match arg_ with
  | DeviceType_GRE => 0
  | DeviceType_nGRE => 1
  | DeviceType_nGnRE => 2
  | DeviceType_nGnRnE => 3

def undefined_MemAttrHints (_ : Unit) : SailM MemAttrHints := do
  (pure { attrs := ← (undefined_bitvector 2)
          hints := ← (undefined_bitvector 2)
          transient := ← (undefined_bool ()) })

def undefined_Shareability (_ : Unit) : SailM Shareability := do
  (internal_pick [Shareability_NSH, Shareability_ISH, Shareability_OSH])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Shareability_of_num (arg_ : Nat) : Shareability :=
  match arg_ with
  | 0 => Shareability_NSH
  | 1 => Shareability_ISH
  | _ => Shareability_OSH

def num_of_Shareability (arg_ : Shareability) : Int :=
  match arg_ with
  | Shareability_NSH => 0
  | Shareability_ISH => 1
  | Shareability_OSH => 2

def undefined_MemTagType (_ : Unit) : SailM MemTagType := do
  (internal_pick [MemTag_Untagged, MemTag_AllocationTagged, MemTag_CanonicallyTagged])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def MemTagType_of_num (arg_ : Nat) : MemTagType :=
  match arg_ with
  | 0 => MemTag_Untagged
  | 1 => MemTag_AllocationTagged
  | _ => MemTag_CanonicallyTagged

def num_of_MemTagType (arg_ : MemTagType) : Int :=
  match arg_ with
  | MemTag_Untagged => 0
  | MemTag_AllocationTagged => 1
  | MemTag_CanonicallyTagged => 2

def undefined_MemoryAttributes (_ : Unit) : SailM MemoryAttributes := do
  (pure { memtype := ← (undefined_MemType ())
          device := ← (undefined_DeviceType ())
          inner := ← (undefined_MemAttrHints ())
          outer := ← (undefined_MemAttrHints ())
          shareability := ← (undefined_Shareability ())
          tags := ← (undefined_MemTagType ())
          notagaccess := ← (undefined_bool ())
          xs := ← (undefined_bitvector 1) })

def undefined_PASpace (_ : Unit) : SailM PASpace := do
  (internal_pick [PAS_NonSecure, PAS_Secure, PAS_Root, PAS_Realm])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def PASpace_of_num (arg_ : Nat) : PASpace :=
  match arg_ with
  | 0 => PAS_NonSecure
  | 1 => PAS_Secure
  | 2 => PAS_Root
  | _ => PAS_Realm

def num_of_PASpace (arg_ : PASpace) : Int :=
  match arg_ with
  | PAS_NonSecure => 0
  | PAS_Secure => 1
  | PAS_Root => 2
  | PAS_Realm => 3

def undefined_FullAddress (_ : Unit) : SailM FullAddress := do
  (pure { paspace := ← (undefined_PASpace ())
          address := ← (undefined_bitvector 56) })

def undefined_GPCF (_ : Unit) : SailM GPCF := do
  (internal_pick [GPCF_None, GPCF_AddressSize, GPCF_Walk, GPCF_EABT, GPCF_Fail])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def GPCF_of_num (arg_ : Nat) : GPCF :=
  match arg_ with
  | 0 => GPCF_None
  | 1 => GPCF_AddressSize
  | 2 => GPCF_Walk
  | 3 => GPCF_EABT
  | _ => GPCF_Fail

def num_of_GPCF (arg_ : GPCF) : Int :=
  match arg_ with
  | GPCF_None => 0
  | GPCF_AddressSize => 1
  | GPCF_Walk => 2
  | GPCF_EABT => 3
  | GPCF_Fail => 4

def undefined_GPCFRecord (_ : Unit) : SailM GPCFRecord := do
  (pure { gpf := ← (undefined_GPCF ())
          level := ← (undefined_int ()) })

def undefined_Fault (_ : Unit) : SailM Fault := do
  (internal_pick
    [Fault_None, Fault_AccessFlag, Fault_Alignment, Fault_Background, Fault_Domain, Fault_Permission, Fault_Translation, Fault_AddressSize, Fault_SyncExternal, Fault_SyncExternalOnWalk, Fault_SyncParity, Fault_SyncParityOnWalk, Fault_GPCFOnWalk, Fault_GPCFOnOutput, Fault_AsyncParity, Fault_AsyncExternal, Fault_TagCheck, Fault_Debug, Fault_TLBConflict, Fault_BranchTarget, Fault_HWUpdateAccessFlag, Fault_Lockdown, Fault_Exclusive, Fault_ICacheMaint])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 23 -/
def Fault_of_num (arg_ : Nat) : Fault :=
  match arg_ with
  | 0 => Fault_None
  | 1 => Fault_AccessFlag
  | 2 => Fault_Alignment
  | 3 => Fault_Background
  | 4 => Fault_Domain
  | 5 => Fault_Permission
  | 6 => Fault_Translation
  | 7 => Fault_AddressSize
  | 8 => Fault_SyncExternal
  | 9 => Fault_SyncExternalOnWalk
  | 10 => Fault_SyncParity
  | 11 => Fault_SyncParityOnWalk
  | 12 => Fault_GPCFOnWalk
  | 13 => Fault_GPCFOnOutput
  | 14 => Fault_AsyncParity
  | 15 => Fault_AsyncExternal
  | 16 => Fault_TagCheck
  | 17 => Fault_Debug
  | 18 => Fault_TLBConflict
  | 19 => Fault_BranchTarget
  | 20 => Fault_HWUpdateAccessFlag
  | 21 => Fault_Lockdown
  | 22 => Fault_Exclusive
  | _ => Fault_ICacheMaint

def num_of_Fault (arg_ : Fault) : Int :=
  match arg_ with
  | Fault_None => 0
  | Fault_AccessFlag => 1
  | Fault_Alignment => 2
  | Fault_Background => 3
  | Fault_Domain => 4
  | Fault_Permission => 5
  | Fault_Translation => 6
  | Fault_AddressSize => 7
  | Fault_SyncExternal => 8
  | Fault_SyncExternalOnWalk => 9
  | Fault_SyncParity => 10
  | Fault_SyncParityOnWalk => 11
  | Fault_GPCFOnWalk => 12
  | Fault_GPCFOnOutput => 13
  | Fault_AsyncParity => 14
  | Fault_AsyncExternal => 15
  | Fault_TagCheck => 16
  | Fault_Debug => 17
  | Fault_TLBConflict => 18
  | Fault_BranchTarget => 19
  | Fault_HWUpdateAccessFlag => 20
  | Fault_Lockdown => 21
  | Fault_Exclusive => 22
  | Fault_ICacheMaint => 23

def undefined_ErrorState (_ : Unit) : SailM ErrorState := do
  (internal_pick
    [ErrorState_UC, ErrorState_UEU, ErrorState_UEO, ErrorState_UER, ErrorState_CE, ErrorState_Uncategorized, ErrorState_IMPDEF])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 6 -/
def ErrorState_of_num (arg_ : Nat) : ErrorState :=
  match arg_ with
  | 0 => ErrorState_UC
  | 1 => ErrorState_UEU
  | 2 => ErrorState_UEO
  | 3 => ErrorState_UER
  | 4 => ErrorState_CE
  | 5 => ErrorState_Uncategorized
  | _ => ErrorState_IMPDEF

def num_of_ErrorState (arg_ : ErrorState) : Int :=
  match arg_ with
  | ErrorState_UC => 0
  | ErrorState_UEU => 1
  | ErrorState_UEO => 2
  | ErrorState_UER => 3
  | ErrorState_CE => 4
  | ErrorState_Uncategorized => 5
  | ErrorState_IMPDEF => 6

def undefined_FaultRecord (_ : Unit) : SailM FaultRecord := do
  (pure { statuscode := ← (undefined_Fault ())
          access := ← (undefined_AccessDescriptor ())
          ipaddress := ← (undefined_FullAddress ())
          gpcf := ← (undefined_GPCFRecord ())
          paddress := ← (undefined_FullAddress ())
          gpcfs2walk := ← (undefined_bool ())
          s2fs1walk := ← (undefined_bool ())
          write := ← (undefined_bool ())
          s1tagnotdata := ← (undefined_bool ())
          tagaccess := ← (undefined_bool ())
          level := ← (undefined_int ())
          extflag := ← (undefined_bitvector 1)
          secondstage := ← (undefined_bool ())
          assuredonly := ← (undefined_bool ())
          toplevel := ← (undefined_bool ())
          overlay := ← (undefined_bool ())
          dirtybit := ← (undefined_bool ())
          domain := ← (undefined_bitvector 4)
          merrorstate := ← (undefined_ErrorState ())
          debugmoe := ← (undefined_bitvector 4) })

def undefined_MBReqDomain (_ : Unit) : SailM MBReqDomain := do
  (internal_pick
    [MBReqDomain_Nonshareable, MBReqDomain_InnerShareable, MBReqDomain_OuterShareable, MBReqDomain_FullSystem])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def MBReqDomain_of_num (arg_ : Nat) : MBReqDomain :=
  match arg_ with
  | 0 => MBReqDomain_Nonshareable
  | 1 => MBReqDomain_InnerShareable
  | 2 => MBReqDomain_OuterShareable
  | _ => MBReqDomain_FullSystem

def num_of_MBReqDomain (arg_ : MBReqDomain) : Int :=
  match arg_ with
  | MBReqDomain_Nonshareable => 0
  | MBReqDomain_InnerShareable => 1
  | MBReqDomain_OuterShareable => 2
  | MBReqDomain_FullSystem => 3

def undefined_MBReqTypes (_ : Unit) : SailM MBReqTypes := do
  (internal_pick [MBReqTypes_Reads, MBReqTypes_Writes, MBReqTypes_All])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def MBReqTypes_of_num (arg_ : Nat) : MBReqTypes :=
  match arg_ with
  | 0 => MBReqTypes_Reads
  | 1 => MBReqTypes_Writes
  | _ => MBReqTypes_All

def num_of_MBReqTypes (arg_ : MBReqTypes) : Int :=
  match arg_ with
  | MBReqTypes_Reads => 0
  | MBReqTypes_Writes => 1
  | MBReqTypes_All => 2

def undefined_CacheRecord (_ : Unit) : SailM CacheRecord := do
  (pure { acctype := ← (undefined_AccessType ())
          cacheop := ← (undefined_CacheOp ())
          opscope := ← (undefined_CacheOpScope ())
          cachetype := ← (undefined_CacheType ())
          regval := ← (undefined_bitvector 64)
          paddress := ← (undefined_FullAddress ())
          vaddress := ← (undefined_bitvector 64)
          setnum := ← (undefined_int ())
          waynum := ← (undefined_int ())
          level := ← (undefined_int ())
          shareability := ← (undefined_Shareability ())
          translated := ← (undefined_bool ())
          is_vmid_valid := ← (undefined_bool ())
          vmid := ← (undefined_bitvector 16)
          is_asid_valid := ← (undefined_bool ())
          asid := ← (undefined_bitvector 16)
          security := ← (undefined_SecurityState ())
          cpas := ← (undefined_CachePASpace ()) })

def undefined_Regime (_ : Unit) : SailM Regime := do
  (internal_pick [Regime_EL3, Regime_EL30, Regime_EL2, Regime_EL20, Regime_EL10])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def Regime_of_num (arg_ : Nat) : Regime :=
  match arg_ with
  | 0 => Regime_EL3
  | 1 => Regime_EL30
  | 2 => Regime_EL2
  | 3 => Regime_EL20
  | _ => Regime_EL10

def num_of_Regime (arg_ : Regime) : Int :=
  match arg_ with
  | Regime_EL3 => 0
  | Regime_EL30 => 1
  | Regime_EL2 => 2
  | Regime_EL20 => 3
  | Regime_EL10 => 4

def undefined_TGx (_ : Unit) : SailM TGx := do
  (internal_pick [TGx_4KB, TGx_16KB, TGx_64KB])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def TGx_of_num (arg_ : Nat) : TGx :=
  match arg_ with
  | 0 => TGx_4KB
  | 1 => TGx_16KB
  | _ => TGx_64KB

def num_of_TGx (arg_ : TGx) : Int :=
  match arg_ with
  | TGx_4KB => 0
  | TGx_16KB => 1
  | TGx_64KB => 2

def undefined_TLBContext (_ : Unit) : SailM TLBContext := do
  (pure { ss := ← (undefined_SecurityState ())
          regime := ← (undefined_Regime ())
          vmid := ← (undefined_bitvector 16)
          asid := ← (undefined_bitvector 16)
          nG := ← (undefined_bitvector 1)
          ipaspace := ← (undefined_PASpace ())
          includes_s1_name := ← (undefined_bool ())
          includes_s2_name := ← (undefined_bool ())
          includes_gpt_name := ← (undefined_bool ())
          ia := ← (undefined_bitvector 64)
          tg := ← (undefined_TGx ())
          cnp := ← (undefined_bitvector 1)
          level := ← (undefined_int ())
          isd128 := ← (undefined_bool ())
          xs := ← (undefined_bitvector 1) })

def undefined_AddressDescriptor (_ : Unit) : SailM AddressDescriptor := do
  (pure { fault := ← (undefined_FaultRecord ())
          memattrs := ← (undefined_MemoryAttributes ())
          paddress := ← (undefined_FullAddress ())
          tlbcontext := ← (undefined_TLBContext ())
          s1assured := ← (undefined_bool ())
          s2fs1mro := ← (undefined_bool ())
          mecid := ← (undefined_bitvector 16)
          vaddress := ← (undefined_bitvector 64) })

def undefined_TranslationStartInfo (_ : Unit) : SailM TranslationStartInfo := do
  (pure { ss := ← (undefined_SecurityState ())
          regime := ← (undefined_Regime ())
          vmid := ← (undefined_bitvector 16)
          asid := ← (undefined_bitvector 16)
          va := ← (undefined_bitvector 64)
          cnp := ← (undefined_bitvector 1)
          accdesc := ← (undefined_AccessDescriptor ())
          size := ← (undefined_int ()) })

def undefined_TLBILevel (_ : Unit) : SailM TLBILevel := do
  (internal_pick [TLBILevel_Any, TLBILevel_Last])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def TLBILevel_of_num (arg_ : Nat) : TLBILevel :=
  match arg_ with
  | 0 => TLBILevel_Any
  | _ => TLBILevel_Last

def num_of_TLBILevel (arg_ : TLBILevel) : Int :=
  match arg_ with
  | TLBILevel_Any => 0
  | TLBILevel_Last => 1

def undefined_TLBIOp (_ : Unit) : SailM TLBIOp := do
  (internal_pick
    [TLBIOp_DALL, TLBIOp_DASID, TLBIOp_DVA, TLBIOp_IALL, TLBIOp_IASID, TLBIOp_IVA, TLBIOp_ALL, TLBIOp_ASID, TLBIOp_IPAS2, TLBIPOp_IPAS2, TLBIOp_VAA, TLBIOp_VA, TLBIPOp_VAA, TLBIPOp_VA, TLBIOp_VMALL, TLBIOp_VMALLS12, TLBIOp_RIPAS2, TLBIPOp_RIPAS2, TLBIOp_RVAA, TLBIOp_RVA, TLBIPOp_RVAA, TLBIPOp_RVA, TLBIOp_RPA, TLBIOp_PAALL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 23 -/
def TLBIOp_of_num (arg_ : Nat) : TLBIOp :=
  match arg_ with
  | 0 => TLBIOp_DALL
  | 1 => TLBIOp_DASID
  | 2 => TLBIOp_DVA
  | 3 => TLBIOp_IALL
  | 4 => TLBIOp_IASID
  | 5 => TLBIOp_IVA
  | 6 => TLBIOp_ALL
  | 7 => TLBIOp_ASID
  | 8 => TLBIOp_IPAS2
  | 9 => TLBIPOp_IPAS2
  | 10 => TLBIOp_VAA
  | 11 => TLBIOp_VA
  | 12 => TLBIPOp_VAA
  | 13 => TLBIPOp_VA
  | 14 => TLBIOp_VMALL
  | 15 => TLBIOp_VMALLS12
  | 16 => TLBIOp_RIPAS2
  | 17 => TLBIPOp_RIPAS2
  | 18 => TLBIOp_RVAA
  | 19 => TLBIOp_RVA
  | 20 => TLBIPOp_RVAA
  | 21 => TLBIPOp_RVA
  | 22 => TLBIOp_RPA
  | _ => TLBIOp_PAALL

def num_of_TLBIOp (arg_ : TLBIOp) : Int :=
  match arg_ with
  | TLBIOp_DALL => 0
  | TLBIOp_DASID => 1
  | TLBIOp_DVA => 2
  | TLBIOp_IALL => 3
  | TLBIOp_IASID => 4
  | TLBIOp_IVA => 5
  | TLBIOp_ALL => 6
  | TLBIOp_ASID => 7
  | TLBIOp_IPAS2 => 8
  | TLBIPOp_IPAS2 => 9
  | TLBIOp_VAA => 10
  | TLBIOp_VA => 11
  | TLBIPOp_VAA => 12
  | TLBIPOp_VA => 13
  | TLBIOp_VMALL => 14
  | TLBIOp_VMALLS12 => 15
  | TLBIOp_RIPAS2 => 16
  | TLBIPOp_RIPAS2 => 17
  | TLBIOp_RVAA => 18
  | TLBIOp_RVA => 19
  | TLBIPOp_RVAA => 20
  | TLBIPOp_RVA => 21
  | TLBIOp_RPA => 22
  | TLBIOp_PAALL => 23

def undefined_TLBIMemAttr (_ : Unit) : SailM TLBIMemAttr := do
  (internal_pick [TLBI_AllAttr, TLBI_ExcludeXS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def TLBIMemAttr_of_num (arg_ : Nat) : TLBIMemAttr :=
  match arg_ with
  | 0 => TLBI_AllAttr
  | _ => TLBI_ExcludeXS

def num_of_TLBIMemAttr (arg_ : TLBIMemAttr) : Int :=
  match arg_ with
  | TLBI_AllAttr => 0
  | TLBI_ExcludeXS => 1

def undefined_TLBIRecord (_ : Unit) : SailM TLBIRecord := do
  (pure { op := ← (undefined_TLBIOp ())
          from_aarch64 := ← (undefined_bool ())
          security := ← (undefined_SecurityState ())
          regime := ← (undefined_Regime ())
          vmid := ← (undefined_bitvector 16)
          asid := ← (undefined_bitvector 16)
          level := ← (undefined_TLBILevel ())
          attr := ← (undefined_TLBIMemAttr ())
          ipaspace := ← (undefined_PASpace ())
          address := ← (undefined_bitvector 64)
          end_address_name := ← (undefined_bitvector 64)
          d64 := ← (undefined_bool ())
          d128 := ← (undefined_bool ())
          ttl := ← (undefined_bitvector 4)
          tg := ← (undefined_bitvector 2) })

def undefined_TLBIInfo (_ : Unit) : SailM TLBIInfo := do
  (pure { rec' := ← (undefined_TLBIRecord ())
          shareability := ← (undefined_Shareability ()) })

def undefined_DxB (_ : Unit) : SailM DxB := do
  (pure { domain := ← (undefined_MBReqDomain ())
          types := ← (undefined_MBReqTypes ())
          nXS := ← (undefined_bool ()) })

def GPRs : (Vector (RegisterRef (BitVec 64)) 31) :=
  #v[(.Reg R0), (.Reg R1), (.Reg R2), (.Reg R3), (.Reg R4), (.Reg R5), (.Reg R6), (.Reg R7), (.Reg R8), (.Reg R9), (.Reg R10), (.Reg R11), (.Reg R12), (.Reg R13), (.Reg R14), (.Reg R15), (.Reg R16), (.Reg R17), (.Reg R18), (.Reg R19), (.Reg R20), (.Reg R21), (.Reg R22), (.Reg R23), (.Reg R24), (.Reg R25), (.Reg R26), (.Reg R27), (.Reg R28), (.Reg R29), (.Reg R30)]

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 31 -/
def wX (n : Nat) (value : (BitVec 64)) : SailM Unit := do
  if ((n != 31) : Bool)
  then writeRegRef (GetElem?.getElem! GPRs n) value
  else (pure ())

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 31 -/
def rX (n : Nat) : SailM (BitVec 64) := do
  if ((n != 31) : Bool)
  then (reg_deref (GetElem?.getElem! GPRs n))
  else (pure 0x0000000000000000#64)

def rPC (_ : Unit) : SailM (BitVec 64) := do
  readReg _PC

def wPC (pc : (BitVec 64)) : SailM Unit := do
  writeReg _PC pc

/-- Type quantifiers: k_a : Type, k_b : Type -/
def is_ok (r : (Result k_a k_b)) : Bool :=
  match r with
  | .Ok _ => true
  | .Err _ => false

/-- Type quantifiers: k_a : Type, k_b : Type -/
def is_err (r : (Result k_a k_b)) : Bool :=
  match r with
  | .Ok _ => false
  | .Err _ => true

/-- Type quantifiers: k_a : Type, k_b : Type -/
def ok_option (r : (Result k_a k_b)) : (Option k_a) :=
  match r with
  | .Ok x => (some x)
  | .Err _ => none

/-- Type quantifiers: k_a : Type, k_b : Type -/
def err_option (r : (Result k_a k_b)) : (Option k_b) :=
  match r with
  | .Ok _ => none
  | .Err err => (some err)

/-- Type quantifiers: k_a : Type, k_b : Type -/
def unwrap_or (r : (Result k_a k_b)) (y : k_a) : k_a :=
  match r with
  | .Ok x => x
  | .Err _ => y

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def sail_instr_announce (x_0 : (BitVec k_n)) : Unit :=
  ()

/-- Type quantifiers: x_0 : Nat, x_0 ∈ {32, 64} -/
def sail_branch_announce (x_0 : Nat) (x_1 : (BitVec x_0)) : Unit :=
  ()

def sail_reset_registers (_ : Unit) : Unit :=
  ()

def sail_synchronize_registers (_ : Unit) : Unit :=
  ()

/-- Type quantifiers: k_a : Type -/
def sail_mark_register (x_0 : (RegisterRef k_a)) (x_1 : String) : Unit :=
  ()

/-- Type quantifiers: k_a : Type, k_b : Type -/
def sail_mark_register_pair (x_0 : (RegisterRef k_a)) (x_1 : (RegisterRef k_b)) (x_2 : String) : Unit :=
  ()

/-- Type quantifiers: k_a : Type -/
def sail_ignore_write_to (reg : (RegisterRef k_a)) : Unit :=
  (sail_mark_register reg "ignore_write")

/-- Type quantifiers: k_a : Type -/
def sail_pick_dependency (reg : (RegisterRef k_a)) : Unit :=
  (sail_mark_register reg "pick")

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def __monomorphize (bv : (BitVec k_n)) : (BitVec k_n) :=
  bv

/-- Type quantifiers: n : Int -/
def __monomorphize_int (n : Int) : Int :=
  n

/-- Type quantifiers: k_b : Bool -/
def __monomorphize_bool (b : Bool) : Bool :=
  b

def __monomorphize_reads : Bool := false

def __monomorphize_writes : Bool := false

/-- Type quantifiers: x_0 : Nat, x_0 ∈ {32, 64} -/
def sail_address_announce (x_0 : Nat) (x_1 : (BitVec x_0)) : Unit :=
  ()

def addr_size' : Nat := 64

def base_AccessDescriptor (acctype : AccessType) : AccessDescriptor :=
  { acctype := acctype
    el := (BitVec.zero 2)
    ss := SS_NonSecure
    acqsc := false
    acqpc := false
    relsc := false
    limitedordered := false
    exclusive := false
    atomicop := false
    modop := MemAtomicOp_ADD
    nontemporal := false
    read := false
    write := false
    cacheop := CacheOp_Clean
    opscope := CacheOpScope_ALLU
    cachetype := CacheType_Data
    pan := false
    transactional := false
    nonfault := false
    firstfault := false
    first := false
    contiguous := false
    streamingsve := false
    ls64 := false
    mops := false
    rcw := false
    rcws := false
    toplevel := false
    varange := VARange_LOWER
    a32lsmd := false
    tagchecked := false
    tagaccess := false
    mpam := { mpam_sp := PIdSpace_NonSecure
              partid := 0x0000#16
              pmg := 0x00#8 } }

def create_writeAccessDescriptor (_ : Unit) : AccessDescriptor :=
  let accdesc := (base_AccessDescriptor AccessType_GPR)
  let accdesc : AccessDescriptor := { accdesc with write := true }
  let accdesc : AccessDescriptor := { accdesc with read := false }
  { accdesc with el := 0b00#2 }

def create_readAccessDescriptor (_ : Unit) : AccessDescriptor :=
  let accdesc := (base_AccessDescriptor AccessType_GPR)
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with write := false }
  { accdesc with el := 0b00#2 }

def create_iFetchAccessDescriptor (_ : Unit) : AccessDescriptor :=
  let accdesc := (base_AccessDescriptor AccessType_IFETCH)
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with write := false }
  { accdesc with el := 0b00#2 }

def addr_space_def := ()

/-- Type quantifiers: N : Nat, N > 0 -/
def read_memory (N : Nat) (addr : (BitVec 64)) (accdesc : AccessDescriptor) : SailM (BitVec (N * 8)) := do
  let req : (Mem_request N 0 addr_size addr_space AccessDescriptor) :=
    { access_kind := accdesc
      address := (Sail.BitVec.truncate addr addr_size')
      address_space := addr_space_def
      size := N
      num_tag := 0 }
  match (← (sail_mem_read req)) with
  | .Ok (bytes, _) => (pure (from_bytes_le (n := N) bytes))
  | .Err _e => throw Error.Exit

def iFetch (addr : (BitVec 64)) (accdesc : AccessDescriptor) : SailM (BitVec 32) := do
  (read_memory 4 addr accdesc)

def rMem (addr : (BitVec 64)) (accdesc : AccessDescriptor) : SailM (BitVec 64) := do
  (read_memory 8 addr accdesc)

def wMem_Addr (addr : (BitVec 64)) : Unit :=
  (sail_address_announce 64 (Sail.BitVec.zeroExtend addr 64))

def wMem (addr : (BitVec 64)) (value : (BitVec 64)) (accdesc : AccessDescriptor) : SailM Unit := do
  let req : (Mem_request 8 0 addr_size addr_space AccessDescriptor) :=
    { access_kind := accdesc
      address := (Sail.BitVec.truncate addr addr_size')
      address_space := addr_space_def
      size := 8
      num_tag := 0 }
  match (← (sail_mem_write req (to_bytes_le (n := 8) value) #v[])) with
  | .Ok _ => (pure ())
  | .Err _ => throw Error.Exit

def dataMemoryBarrier (types : MBReqTypes) : SailM Unit := do
  (sail_barrier
    (Barrier_DMB
      { domain := MBReqDomain_FullSystem
        types := types
        nXS := false }))

def translate_address (va : (BitVec 64)) (accdesc : AccessDescriptor) : (Option (BitVec 64)) :=
  (some va)

def decodeLoadStoreRegister (opc : (BitVec 2)) (Rm : (BitVec 5)) (option_v : (BitVec 3)) (S : (BitVec 1)) (Rn : (BitVec 5)) (Rt : (BitVec 5)) : (Option ast) :=
  let t : reg_index := (BitVec.toNatInt Rt)
  let n : reg_index := (BitVec.toNatInt Rn)
  let m : reg_index := (BitVec.toNatInt Rm)
  if (((option_v != 0b011#3) || (S == 1#1)) : Bool)
  then none
  else
    (if ((opc == 0b01#2) : Bool)
    then (some (LoadRegister (t, n, m)))
    else
      (if ((opc == 0b00#2) : Bool)
      then (some (StoreRegister (t, n, m)))
      else none))

def decodeExclusiveOr (sf : (BitVec 1)) (shift : (BitVec 2)) (N : (BitVec 1)) (Rm : (BitVec 5)) (imm6 : (BitVec 6)) (Rn : (BitVec 5)) (Rd : (BitVec 5)) : (Option ast) :=
  let d : reg_index := (BitVec.toNatInt Rd)
  let n : reg_index := (BitVec.toNatInt Rn)
  let m : reg_index := (BitVec.toNatInt Rm)
  if (((sf == 0#1) && ((BitVec.access imm6 5) == 1#1)) : Bool)
  then none
  else
    (if ((imm6 != 0b000000#6) : Bool)
    then none
    else (some (ExclusiveOr (d, n, m))))

def decodeDataMemoryBarrier (merge_var : (BitVec 4)) : (Option ast) :=
  match merge_var with
  | 0b1111 => (some (DataMemoryBarrier MBReqTypes_All))
  | 0b1110 => (some (DataMemoryBarrier MBReqTypes_Writes))
  | 0b1101 => (some (DataMemoryBarrier MBReqTypes_Reads))
  | _ => none

def decodeCompareAndBranch (imm19 : (BitVec 19)) (Rt : (BitVec 5)) : (Option ast) :=
  let t : reg_index := (BitVec.toNatInt Rt)
  let offset : (BitVec 64) := (Sail.BitVec.signExtend (imm19 ++ 0b00#2) 64)
  (some (CompareAndBranch (t, offset)))

/-- Type quantifiers: m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31, 0 ≤ n ∧ n ≤ 31, 0 ≤ m
  ∧ m ≤ 31 -/
def execute_StoreRegister (t : Nat) (n : Nat) (m : Nat) : SailM Unit := SailME.run do
  let base_addr ← do (rX n)
  let offset ← do (rX m)
  let addr := (base_addr + offset)
  let accdesc := (create_writeAccessDescriptor ())
  let addr ← (( do
    match (translate_address addr accdesc) with
    | .some addr => (pure addr)
    | none => SailME.throw (() : Unit) ) : SailME Unit (BitVec addr_size) )
  let _ : Unit := (wMem_Addr addr)
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  let data ← do (rX t)
  (wMem addr data accdesc)

/-- Type quantifiers: m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31, 0 ≤ n ∧ n ≤ 31, 0 ≤ m
  ∧ m ≤ 31 -/
def execute_LoadRegister (t : Nat) (n : Nat) (m : Nat) : SailM Unit := SailME.run do
  let base_addr ← do (rX n)
  let offset ← do (rX m)
  let addr := (base_addr + offset)
  let accdesc := (create_readAccessDescriptor ())
  let addr ← (( do
    match (translate_address addr accdesc) with
    | .some addr => (pure addr)
    | none => SailME.throw (() : Unit) ) : SailME Unit (BitVec addr_size) )
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  let data ← do (rMem addr accdesc)
  (wX t data)

/-- Type quantifiers: m : Nat, n : Nat, d : Nat, 0 ≤ d ∧ d ≤ 31, 0 ≤ n ∧ n ≤ 31, 0 ≤ m
  ∧ m ≤ 31 -/
def execute_ExclusiveOr (d : Nat) (n : Nat) (m : Nat) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  let operand1 ← do (rX n)
  let operand2 ← do (rX m)
  (wX d (operand1 ^^^ operand2))

def execute_DataMemoryBarrier (types : MBReqTypes) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  (dataMemoryBarrier types)

/-- Type quantifiers: t : Nat, 0 ≤ t ∧ t ≤ 31 -/
def execute_CompareAndBranch (t : Nat) (offset : (BitVec 64)) : SailM Unit := do
  let operand ← do (rX t)
  if ((operand == 0x0000000000000000#64) : Bool)
  then
    (do
      let base ← do (rPC ())
      let addr := (base + offset)
      (wPC addr))
  else writeReg _PC (BitVec.addInt (← readReg _PC) 4)

def execute (merge_var : ast) : SailM Unit := do
  match merge_var with
  | .LoadRegister (t, n, m) => (execute_LoadRegister t n m)
  | .StoreRegister (t, n, m) => (execute_StoreRegister t n m)
  | .ExclusiveOr (d, n, m) => (execute_ExclusiveOr d n m)
  | .DataMemoryBarrier types => (execute_DataMemoryBarrier types)
  | .CompareAndBranch (t, offset) => (execute_CompareAndBranch t offset)

def decode (merge_var : (BitVec 32)) : (Option ast) :=
  match_bv merge_var with
  | [11,111,0,00,opc:2,1,Rm:5,option_v:3,S:1,10,Rn:5,Rt:5] =>
    (decodeLoadStoreRegister opc Rm option_v S Rn Rt)
  | [sf:1,10,01010,shift:2,N:1,Rm:5,imm6:6,Rn:5,Rd:5] =>
    (decodeExclusiveOr sf shift N Rm imm6 Rn Rd)
  | [1101010100,0,00,011,0011,CRm:4,1,01,11111] => (decodeDataMemoryBarrier CRm)
  | [1,011010,0,imm19:19,Rt:5] => (decodeCompareAndBranch imm19 Rt)
  | _ => none

def fetch_and_execute (_ : Unit) : SailM Unit := SailME.run do
  let accdesc := (create_iFetchAccessDescriptor ())
  let addr ← (( do
    match (translate_address (← readReg _PC) accdesc) with
    | .some addr => (pure addr)
    | none => SailME.throw (() : Unit) ) : SailME Unit (BitVec addr_size) )
  let machineCode ← do (iFetch addr accdesc)
  let instr := (decode machineCode)
  match instr with
  | .some instr => (execute instr)
  | none => assert false "Unsupported Encoding"

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
