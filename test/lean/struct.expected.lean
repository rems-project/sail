import Out.Sail.Sail

open Sail


structure My_struct where
  field1 : Int
  field2 : (BitVec 1)

/-- Type quantifiers: k_n : Int, k_vasize : Int, k_pa : Type, k_ts : Type, k_arch_ak : Type, k_n > 0
  ∧ k_vasize ≥ 0 -/

structure Mem_write_request
  (k_n : Nat) (k_vasize : Nat) (k_pa : Type) (k_ts : Type) (k_arch_ak : Type) where
  va : (Option (BitVec k_vasize))
  pa : k_pa
  translation : k_ts
  size : Int
  value : (Option (BitVec (8 * k_n)))
  tag : (Option Bool)

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

def undefined_My_struct (_ : Unit) : SailM My_struct := do
  (pure { field1 := (← (undefined_int ()))
          field2 := (← (undefined_bit ())) })

def struct_field2 (s : My_struct) : (BitVec 1) :=
  s.field2

def struct_update_field2 (s : My_struct) (b : (BitVec 1)) : My_struct :=
  { s with field2 := b }

/-- Type quantifiers: i : Int -/
def struct_update_both_fields (s : My_struct) (i : Int) (b : (BitVec 1)) : My_struct :=
  { s with field1 := i, field2 := b }

/-- Type quantifiers: i : Int -/
def mk_struct (i : Int) (b : (BitVec 1)) : My_struct :=
  { field1 := i
    field2 := b }

def undef_struct (x : (BitVec 1)) : SailM My_struct := do
  ((undefined_My_struct ()) : SailM My_struct)

def initialize_registers (_ : Unit) : Unit :=
  ()

