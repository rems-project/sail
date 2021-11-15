default Order dec
$include <prelude.sail>

enum Access_variety = {
  AV_plain,
  AV_exclusive,
  AV_atomic_rmw
}

enum Access_strength = {
  AS_normal,
  AS_rel_or_acq,
  AS_acq_rc_pc
}

struct Explicit_access_kind = {
  variety : Access_variety,
  strength : Access_strength
}

union Access_kind = {
  AK_Explicit : Explicit_access_kind,
  AK_Ifetch : unit,
  AK_TTW : unit
}

struct Mem_read_request('vasize : Int, 'pa : Type) = {
  MR_access_kind : Access_kind,
  MR_VA : option(bits('vasize)),
  MR_PA : 'pa,
}

struct Mem_write_request('vasize : Int, 'pa : Type) = {
  MW_access_kind : Access_kind,
  MW_VA : option(bits('vasize)),
  MW_PA : 'pa,          
  MW_tag : option(bool),
}

union Mem_result('a: Type, 'abort: Type) = {
  Mem_value : 'a,
  Mem_abort : 'abort
}

event __mem_read_request : forall 'n 'vasize, 'vasize > 0 & 'n > 0.
  (int('n), Mem_read_request('vasize, 'pa)) -> Mem_result(bits(8 * 'n), 'abort)
with
  'pa: Type,
  'abort: Type
= {
    val pa_bits : 'pa -> {'pasize, 'pasize in {32, 64}. bits('pasize)}
}

event __mem_write_request : forall 'n 'vasize, 'vasize > 0 & 'n > 0.
  (int('n), bits(8 * 'n), Mem_write_request('vasize, 'pa)) -> Mem_result(option(bool), 'abort) effect {wmem}
with
  'pa: Type,
  'abort: Type
= {
  val pa_bits : 'pa -> {'pasize, 'pasize in {32, 64}. bits('pasize)}
}

event __mem_write_exclusive_success_request : forall 'vasize, 'vasize > 0. Mem_write_request('vasize, 'pa) -> Mem_result(option(bool), 'abort) effect {wmem}
with
  'pa: Type,
  'abort: Type

event __mem_write_announce_address : forall 'n, 'n > 0. (int('n), 'pa) -> unit effect {wmem}
with
  'pa: Type

event __branch_announce_address : 'branch_announce -> unit
with
  'branch_announce: Type

event __barrier_request : 'barrier -> unit effect {barr}
with
  'barrier: Type

event __cache_op_request : 'cache_op -> unit effect {wmem}
with
  'cache_op: Type

event __TLB_op_request : 'tlb_op -> unit effect {wmem}
with
  'tlb_op: Type

event __fault : 'fault -> unit effect {wmem}
with
  'fault: Type
