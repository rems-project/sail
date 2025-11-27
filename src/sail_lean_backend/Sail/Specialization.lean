import THE_MODULE_NAME.Sail.Sail
import THE_MODULE_NAME.Defs

namespace Sail

@[simp_sail]
def sailTryCatch (e : SailM α) (h : exception → SailM α) : SailM α := PreSail.sailTryCatch e h

@[simp_sail]
def sailThrow (e : exception) : SailM α := PreSail.sailThrow e

abbrev undefined_unit (_ : Unit) : SailM Unit := PreSail.undefined_unit ()

abbrev undefined_bit (_ : Unit) : SailM (BitVec 1) := PreSail.undefined_bit ()

abbrev undefined_bool (_ : Unit) : SailM Bool := PreSail.undefined_bool ()

abbrev undefined_int (_ : Unit) : SailM Int := PreSail.undefined_int ()

abbrev undefined_range (low high : Int) : SailM Int := PreSail.undefined_range low high

abbrev undefined_nat (_ : Unit) : SailM Nat := PreSail.undefined_nat ()

abbrev undefined_string (_ : Unit) : SailM String := PreSail.undefined_string ()

abbrev undefined_bitvector (n : Nat) : SailM (BitVec n) := PreSail.undefined_bitvector n

abbrev undefined_vector (n : Nat) (a : α) : SailM (Vector α n) := PreSail.undefined_vector n a

abbrev internal_pick {α : Type} : List α → SailM α := PreSail.internal_pick

abbrev writeReg (reg : Register) (v : RegisterType reg) : SailM PUnit := PreSail.writeReg reg v

abbrev readReg (reg : Register) : SailM (RegisterType reg) := PreSail.readReg reg

abbrev RegisterRef := @PreSail.RegisterRef Register RegisterType

abbrev readRegRef (reg_ref : RegisterRef α) : SailM α := PreSail.readRegRef reg_ref

abbrev writeRegRef (reg_ref : RegisterRef α) (a : α) : SailM Unit := PreSail.writeRegRef reg_ref a

abbrev reg_deref (reg_ref : RegisterRef α) : SailM α := PreSail.reg_deref reg_ref

abbrev assert (p : Bool) (s : String) : SailM Unit := PreSail.assert p s

namespace ConcurrencyInterfaceV1

open PreSail.ConcurrencyInterfaceV1

abbrev sail_mem_write [Arch] (req : Mem_write_request n vasize (BitVec pa_size) ts arch) : SailM (Result (Option Bool) Arch.abort) :=
  PreSail.ConcurrencyInterfaceV1.sail_mem_write req

abbrev write_ram (addr_size data_size : Nat) (_hex_ram addr : BitVec addr_size) (value : BitVec (8 * data_size)) :
    SailM Unit := PreSail.write_ram addr_size data_size _hex_ram addr value

abbrev sail_mem_read [Arch] (req : Mem_read_request n vasize (BitVec pa_size) ts arch) : SailM (Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort) := PreSail.ConcurrencyInterfaceV1.sail_mem_read req

abbrev read_ram (addr_size data_size : Nat) (_hex_ram addr : BitVec addr_size) : SailM (BitVec (8 * data_size)) := PreSail.read_ram addr_size data_size _hex_ram addr

abbrev sail_barrier (a : α) : SailM Unit := PreSail.ConcurrencyInterfaceV1.sail_barrier a

abbrev sail_cache_op [Arch] (op : Arch.cache_op) : SailM Unit := PreSail.ConcurrencyInterfaceV1.sail_cache_op op
abbrev sail_tlbi [Arch] (op : Arch.tlb_op) : SailM Unit := PreSail.ConcurrencyInterfaceV1.sail_tlbi op
abbrev sail_translation_start [Arch] (ts : Arch.trans_start) : SailM Unit := PreSail.ConcurrencyInterfaceV1.sail_translation_start ts
abbrev sail_translation_end [Arch] (te : Arch.trans_end) : SailM Unit := PreSail.ConcurrencyInterfaceV1.sail_translation_end te
abbrev sail_take_exception [Arch] (f : Arch.fault) : SailM Unit := PreSail.ConcurrencyInterfaceV1.sail_take_exception f
abbrev sail_return_exception [Arch] (a : Arch.pa) : SailM Unit := PreSail.ConcurrencyInterfaceV1.sail_return_exception a

end ConcurrencyInterfaceV1

namespace ConcurrencyInterfaceV2

open PreSail.ConcurrencyInterfaceV2

abbrev sail_mem_read [Arch] (req : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) :
    SailM (Result ((Vector (BitVec 8) n) × (Vector Bool nt)) Arch.abort) :=
  PreSail.ConcurrencyInterfaceV2.sail_mem_read req

def sail_mem_write [Arch] (req : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) (valueBytes : Vector (BitVec 8) n) (tags : Vector Bool nt) :
    SailM (Result (Option Bool) Arch.abort) := do
  PreSail.ConcurrencyInterfaceV2.sail_mem_write req valueBytes tags

abbrev sail_sys_reg_read [Arch] (id : Arch.sys_reg_id) (r : RegisterRef α) : SailM α :=
  PreSail.ConcurrencyInterfaceV2.sail_sys_reg_read id r

abbrev sail_sys_reg_write [Arch] (id : Arch.sys_reg_id) (r : RegisterRef α) (v : α) : SailM Unit :=
  PreSail.ConcurrencyInterfaceV2.sail_sys_reg_write id r v

abbrev sail_mem_address_announce [Arch] (ann : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) : SailM Unit :=
  PreSail.ConcurrencyInterfaceV2.sail_mem_address_announce ann

abbrev sail_barrier [Arch] (b : Arch.barrier) : SailM Unit := PreSail.ConcurrencyInterfaceV2.sail_barrier b
abbrev sail_cache_op [Arch] (op : Arch.cache_op) : SailM Unit := PreSail.ConcurrencyInterfaceV2.sail_cache_op op
abbrev sail_tlbi [Arch] (op : Arch.tlbi) : SailM Unit := PreSail.ConcurrencyInterfaceV2.sail_tlbi op
abbrev sail_translation_start [Arch] (ts : Arch.trans_start) : SailM Unit := PreSail.ConcurrencyInterfaceV2.sail_translation_start ts
abbrev sail_translation_end [Arch] (te : Arch.trans_end) : SailM Unit := PreSail.ConcurrencyInterfaceV2.sail_translation_end te
abbrev sail_take_exception [Arch] (f : Arch.exn) : SailM Unit := PreSail.ConcurrencyInterfaceV2.sail_take_exception f
abbrev sail_return_exception (a : Unit) : SailM Unit := PreSail.ConcurrencyInterfaceV2.sail_return_exception a


end ConcurrencyInterfaceV2

abbrev cycle_count (a : Unit) : SailM Unit := PreSail.cycle_count a

abbrev get_cycle_count (a : Unit) : SailM Nat := PreSail.get_cycle_count a


abbrev print_effect (str : String) : SailM Unit := PreSail.print_effect str

abbrev print_int_effect (str : String) (n : Int) : SailM Unit := PreSail.print_int_effect str n

abbrev print_bits_effect {w : Nat} (str : String) (x : BitVec w) : SailM Unit := PreSail.print_bits_effect str x

abbrev print_endline_effect (str : String) : SailM Unit := PreSail.print_endline_effect str

def SailME.run (m : SailME α α) : SailM α := PreSail.PreSailME.run m

def SailME.throw (e : α) : SailME α β := PreSail.PreSailME.throw e

abbrev sailTryCatchE (e : SailME β α) (h : exception → SailME β α) : SailME β α := PreSail.sailTryCatchE e h

def unwrapValue [Inhabited α] (x : SailM α) : α :=
  match x.run default with
  | .ok x _ => x
  | _ => default

end Sail
