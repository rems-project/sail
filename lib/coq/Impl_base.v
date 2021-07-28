(*==========================================================================*)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(*==========================================================================*)

Require Import Sail.Instr_kinds.

(*
class ( EnumerationType 'a ) 
  val toNat : 'a -> nat
end


val enumeration_typeCompare : forall 'a. EnumerationType 'a => 'a -> 'a -> ordering
let ~{ocaml} enumeration_typeCompare e1 e2 =
  compare (toNat e1) (toNat e2)
let inline {ocaml} enumeration_typeCompare = defaultCompare

 
default_instance forall 'a. EnumerationType 'a => (Ord 'a)
  let compare = enumeration_typeCompare
  let (<)  r1 r2 = (enumeration_typeCompare r1 r2) = LT
  let (<=) r1 r2 = (enumeration_typeCompare r1 r2) <> GT
  let (>)  r1 r2 = (enumeration_typeCompare r1 r2) = GT
  let (>=) r1 r2 = (enumeration_typeCompare r1 r2) <> LT
end



(* maybe isn't a member of type Ord - this should be in the Lem standard library*)
instance forall 'a. Ord 'a => (Ord (maybe 'a))
  let compare = maybeCompare compare
  let (<)  r1 r2 = (maybeCompare compare r1 r2) = LT
  let (<=) r1 r2 = (maybeCompare compare r1 r2) <> GT
  let (>)  r1 r2 = (maybeCompare compare r1 r2) = GT
  let (>=) r1 r2 = (maybeCompare compare r1 r2) <> LT
end

type word8 = nat (* bounded at a byte, for when lem supports it*)

type end_flag =
  | E_big_endian
  | E_little_endian

type bit =
  | Bitc_zero
  | Bitc_one

type bit_lifted = 
  | Bitl_zero
  | Bitl_one
  | Bitl_undef    (* used for modelling h/w arch unspecified bits *)
  | Bitl_unknown  (* used for interpreter analysis exhaustive execution *)

type direction = 
  | D_increasing
  | D_decreasing

let dir_of_bool is_inc = if is_inc then D_increasing else D_decreasing
let bool_of_dir = function
  | D_increasing -> true
  | D_decreasing -> false
  end

(* at some point this should probably not mention bit_lifted anymore *)
type register_value = <| 
    rv_bits: list bit_lifted (* MSB first, smallest index number *); 
    rv_dir: direction; 
    rv_start: nat ;
    rv_start_internal: nat; 
    (*when dir is increasing, rv_start = rv_start_internal. 
      Otherwise, tells interpreter how to reconstruct a proper decreasing value*)
    |>

type byte_lifted = Byte_lifted of list bit_lifted (* of length 8 *) (*MSB first everywhere*)

type instruction_field_value = list bit

type byte = Byte of list bit (* of length 8 *)  (*MSB first everywhere*) 

type address_lifted = Address_lifted of list byte_lifted (* of length 8 for 64bit machines*) * maybe integer
(* for both values of end_flag, MSBy first *)

type memory_byte = byte_lifted (* of length 8 *) (*MSB first everywhere*)

type memory_value = list memory_byte
(* the list is of length >=1 *)
(* the head of the list is the byte stored at the lowest address;
when calling a Sail function with a wmv effect, the least significant 8
bits of the bit vector passed to the function will be interpreted as
the lowest address byte; similarly, when calling a Sail function with
rmem effect, the lowest address byte will be placed in the least
significant 8 bits of the bit vector returned by the function; this
behaviour is consistent with little-endian. *)


(* not sure which of these is more handy yet *)
type address = Address of list byte (* of length 8 *) * integer
(* type address = Address of integer *)

type opcode = Opcode of list byte (* of length 4 *)

(** typeclass instantiations *)

instance (EnumerationType bit)
  let toNat = function
    | Bitc_zero -> 0
    | Bitc_one -> 1
  end
end

instance (EnumerationType bit_lifted)
  let toNat = function
    | Bitl_zero -> 0
    | Bitl_one -> 1
    | Bitl_undef -> 2
    | Bitl_unknown -> 3
  end
end

let ~{ocaml} byte_liftedCompare (Byte_lifted b1) (Byte_lifted b2) = compare b1 b2
let inline {ocaml} byte_liftedCompare = defaultCompare

let ~{ocaml} byte_liftedLess b1 b2      = byte_liftedCompare b1 b2 =  LT
let ~{ocaml} byte_liftedLessEq b1 b2    = byte_liftedCompare b1 b2 <> GT
let ~{ocaml} byte_liftedGreater b1 b2   = byte_liftedCompare b1 b2 =  GT
let ~{ocaml} byte_liftedGreaterEq b1 b2 = byte_liftedCompare b1 b2 <> LT

let inline {ocaml} byte_liftedLess      = defaultLess
let inline {ocaml} byte_liftedLessEq    = defaultLessEq
let inline {ocaml} byte_liftedGreater   = defaultGreater
let inline {ocaml} byte_liftedGreaterEq = defaultGreaterEq

instance (Ord byte_lifted)
  let compare = byte_liftedCompare
  let (<)  = byte_liftedLess
  let (<=) = byte_liftedLessEq
  let (>)  = byte_liftedGreater
  let (>=) = byte_liftedGreaterEq
end

let ~{ocaml} byteCompare (Byte b1) (Byte b2) = compare b1 b2
let inline {ocaml} byteCompare = defaultCompare

let ~{ocaml} byteLess b1 b2      = byteCompare b1 b2 =  LT
let ~{ocaml} byteLessEq b1 b2    = byteCompare b1 b2 <> GT
let ~{ocaml} byteGreater b1 b2   = byteCompare b1 b2 =  GT
let ~{ocaml} byteGreaterEq b1 b2 = byteCompare b1 b2 <> LT

let inline {ocaml} byteLess      = defaultLess
let inline {ocaml} byteLessEq    = defaultLessEq
let inline {ocaml} byteGreater   = defaultGreater
let inline {ocaml} byteGreaterEq = defaultGreaterEq

instance (Ord byte)
  let compare = byteCompare
  let (<)  = byteLess
  let (<=) = byteLessEq
  let (>)  = byteGreater
  let (>=) = byteGreaterEq
end





let ~{ocaml} opcodeCompare (Opcode o1) (Opcode o2) =
  compare o1 o2
let {ocaml} opcodeCompare = defaultCompare

let ~{ocaml} opcodeLess b1 b2      = opcodeCompare b1 b2 =  LT
let ~{ocaml} opcodeLessEq b1 b2    = opcodeCompare b1 b2 <> GT
let ~{ocaml} opcodeGreater b1 b2   = opcodeCompare b1 b2 =  GT
let ~{ocaml} opcodeGreaterEq b1 b2 = opcodeCompare b1 b2 <> LT

let inline {ocaml} opcodeLess      = defaultLess
let inline {ocaml} opcodeLessEq    = defaultLessEq
let inline {ocaml} opcodeGreater   = defaultGreater
let inline {ocaml} opcodeGreaterEq = defaultGreaterEq

instance (Ord opcode)
  let compare = opcodeCompare
  let (<)  = opcodeLess
  let (<=) = opcodeLessEq
  let (>)  = opcodeGreater
  let (>=) = opcodeGreaterEq
end

let addressCompare (Address b1 i1) (Address b2 i2) = compare i1 i2
(* this cannot be defaultCompare for OCaml because addresses contain big ints *)

let addressLess b1 b2      = addressCompare b1 b2 =  LT
let addressLessEq b1 b2    = addressCompare b1 b2 <> GT
let addressGreater b1 b2   = addressCompare b1 b2 =  GT
let addressGreaterEq b1 b2 = addressCompare b1 b2 <> LT

instance (SetType address)
  let setElemCompare = addressCompare
end

instance (Ord address)
  let compare = addressCompare
  let (<)  = addressLess
  let (<=) = addressLessEq
  let (>)  = addressGreater
  let (>=) = addressGreaterEq
end

let {coq; ocaml} addressEqual a1 a2 = (addressCompare a1 a2) = EQ
let inline {hol; isabelle} addressEqual = unsafe_structural_equality

let {coq; ocaml} addressInequal a1 a2 = not (addressEqual a1 a2)
let inline {hol; isabelle} addressInequal = unsafe_structural_inequality

instance  (Eq address)
  let (=)  = addressEqual
  let (<>) = addressInequal
end

let ~{ocaml} directionCompare d1 d2 =
  match (d1, d2) with
  | (D_decreasing, D_increasing) -> GT
  | (D_increasing, D_decreasing) -> LT
  | _ -> EQ
  end
let inline {ocaml} directionCompare = defaultCompare

let ~{ocaml} directionLess b1 b2      = directionCompare b1 b2 =  LT
let ~{ocaml} directionLessEq b1 b2    = directionCompare b1 b2 <> GT
let ~{ocaml} directionGreater b1 b2   = directionCompare b1 b2 =  GT
let ~{ocaml} directionGreaterEq b1 b2 = directionCompare b1 b2 <> LT

let inline {ocaml} directionLess      = defaultLess
let inline {ocaml} directionLessEq    = defaultLessEq
let inline {ocaml} directionGreater   = defaultGreater
let inline {ocaml} directionGreaterEq = defaultGreaterEq

instance (Ord direction)
  let compare = directionCompare
  let (<)  = directionLess
  let (<=) = directionLessEq
  let (>)  = directionGreater
  let (>=) = directionGreaterEq
end

instance (Show direction)
  let show = function D_increasing -> "D_increasing" | D_decreasing  -> "D_decreasing" end
end

let ~{ocaml} register_valueCompare rv1 rv2 =
  compare (rv1.rv_bits, rv1.rv_dir, rv1.rv_start, rv1.rv_start_internal)
          (rv2.rv_bits, rv2.rv_dir, rv2.rv_start, rv2.rv_start_internal)
let inline {ocaml} register_valueCompare = defaultCompare

let ~{ocaml} register_valueLess b1 b2      = register_valueCompare b1 b2 =  LT
let ~{ocaml} register_valueLessEq b1 b2    = register_valueCompare b1 b2 <> GT
let ~{ocaml} register_valueGreater b1 b2   = register_valueCompare b1 b2 =  GT
let ~{ocaml} register_valueGreaterEq b1 b2 = register_valueCompare b1 b2 <> LT

let inline {ocaml} register_valueLess      = defaultLess
let inline {ocaml} register_valueLessEq    = defaultLessEq
let inline {ocaml} register_valueGreater   = defaultGreater
let inline {ocaml} register_valueGreaterEq = defaultGreaterEq

instance (Ord register_value)
  let compare = register_valueCompare
  let (<)  = register_valueLess
  let (<=) = register_valueLessEq
  let (>)  = register_valueGreater
  let (>=) = register_valueGreaterEq
end

let address_liftedCompare (Address_lifted b1 i1) (Address_lifted b2 i2) =
  compare (i1,b1) (i2,b2)
(* this cannot be defaultCompare for OCaml because address_lifteds contain big
   ints *)

let address_liftedLess b1 b2      = address_liftedCompare b1 b2 =  LT
let address_liftedLessEq b1 b2    = address_liftedCompare b1 b2 <> GT
let address_liftedGreater b1 b2   = address_liftedCompare b1 b2 =  GT
let address_liftedGreaterEq b1 b2 = address_liftedCompare b1 b2 <> LT

instance (Ord address_lifted)
  let compare = address_liftedCompare
  let (<)  = address_liftedLess
  let (<=) = address_liftedLessEq
  let (>)  = address_liftedGreater
  let (>=) = address_liftedGreaterEq
end

(* Registers *)
type slice = (nat * nat)

type reg_name = 
  (* do we really need this here if ppcmem already has this information by itself? *)
| Reg of string * nat * nat * direction
(*Name of the register, accessing the entire register, the start and size of this register, and its direction *)

| Reg_slice of string * nat * direction * slice 
(* Name of the register, accessing from the bit indexed by the first
to the bit indexed by the second integer of the slice, inclusive. For
machineDef* the first is a smaller number or equal to the second, adjusted
to reflect the correct span direction in the interpreter side.  *)

| Reg_field of string * nat * direction * string * slice 
(*Name of the register, start and direction, and name of the field of the register
accessed. The slice specifies where this field is in the register*)

| Reg_f_slice of string * nat * direction * string * slice * slice 
(* The first four components are as in Reg_field; the final slice
specifies a part of the field, indexed w.r.t. the register as a whole *)

let register_base_name : reg_name -> string = function
  | Reg s _ _ _             -> s
  | Reg_slice s _ _ _       -> s
  | Reg_field s _ _ _ _     -> s
  | Reg_f_slice s _ _ _ _ _ -> s
  end

let slice_of_reg_name : reg_name -> slice = function
  | Reg _ start width D_increasing -> (start, start + width -1)
  | Reg _ start width D_decreasing -> (start - width - 1, start)
  | Reg_slice _ _ _ sl             -> sl
  | Reg_field _ _ _ _ sl           -> sl
  | Reg_f_slice _ _ _ _ _ sl       -> sl
  end

let width_of_reg_name (r: reg_name) : nat =
  let width_of_slice (i, j) = (* j - i + 1 in *)

    (integerFromNat j) - (integerFromNat i) + 1
    $> abs $> natFromInteger
  in
  match r with
  | Reg _ _ width _          -> width
  | Reg_slice _ _ _ sl       -> width_of_slice sl
  | Reg_field _ _ _ _ sl     -> width_of_slice sl
  | Reg_f_slice _ _ _ _ _ sl -> width_of_slice sl
  end

let reg_name_non_empty_intersection (r: reg_name) (r': reg_name) : bool = 
  register_base_name r = register_base_name r' &&
  let (i1,  i2)  = slice_of_reg_name r in
  let (i1', i2') = slice_of_reg_name r' in
  i1' <= i2 && i2' >= i1

let reg_nameCompare r1 r2 = 
  compare (register_base_name r1,slice_of_reg_name r1)
          (register_base_name r2,slice_of_reg_name r2)

let reg_nameLess b1 b2      = reg_nameCompare b1 b2 =  LT
let reg_nameLessEq b1 b2    = reg_nameCompare b1 b2 <> GT
let reg_nameGreater b1 b2   = reg_nameCompare b1 b2 =  GT
let reg_nameGreaterEq b1 b2 = reg_nameCompare b1 b2 <> LT

instance (Ord reg_name)
  let compare = reg_nameCompare
  let (<)  = reg_nameLess
  let (<=) = reg_nameLessEq
  let (>)  = reg_nameGreater
  let (>=) = reg_nameGreaterEq
end

let {coq;ocaml} reg_nameEqual a1 a2 = (reg_nameCompare a1 a2) = EQ
let {hol;isabelle} reg_nameEqual = unsafe_structural_equality
let {coq;ocaml} reg_nameInequal a1 a2 = not (reg_nameEqual a1 a2)
let {hol;isabelle} reg_nameInequal = unsafe_structural_inequality

instance (Eq reg_name)
  let (=)  = reg_nameEqual
  let (<>) = reg_nameInequal
end

instance (SetType reg_name)
  let setElemCompare = reg_nameCompare
end

let direction_of_reg_name r = match r with
  | Reg _ _ _ d -> d
  | Reg_slice _ _ d _ -> d
  | Reg_field _ _ d _ _ -> d
  | Reg_f_slice _ _ d _ _ _ -> d
 end

let start_of_reg_name r = match r with
  | Reg _ start _ _ -> start
  | Reg_slice _ start _ _ -> start
  | Reg_field _ start _ _ _ -> start
  | Reg_f_slice _ start _ _ _ _ -> start
end

(* Data structures for building up instructions *)

(* read_kind, write_kind, barrier_kind, trans_kind and instruction_kind have
   been moved to sail_instr_kinds.lem.  This removes the dependency of the
   shallow embedding on the rest of sail_impl_base.lem, and helps avoid name
   clashes between the different monad types. *)

type event = 
  | E_read_mem of read_kind * address_lifted * nat * maybe (list reg_name)
  | E_read_memt of read_kind * address_lifted * nat * maybe (list reg_name)
  | E_write_mem of write_kind * address_lifted * nat * maybe (list reg_name) * memory_value * maybe (list reg_name)
  | E_write_ea of write_kind * address_lifted * nat * maybe (list reg_name)
  | E_excl_res
  | E_write_memv of maybe address_lifted * memory_value * maybe (list reg_name)
  | E_write_memvt of maybe address_lifted * (bit_lifted * memory_value) * maybe (list reg_name)
  | E_barrier of barrier_kind
  | E_footprint 
  | E_read_reg of reg_name
  | E_write_reg of reg_name * register_value
  | E_escape
  | E_error of string 


let eventCompare e1 e2 = 
  match (e1,e2) with
  | (E_read_mem rk1 v1 i1 tr1, E_read_mem rk2 v2 i2 tr2) ->
     compare (rk1, (v1,i1,tr1)) (rk2,(v2, i2, tr2)) 
  | (E_read_memt rk1 v1 i1 tr1, E_read_memt rk2 v2 i2 tr2) ->
     compare (rk1, (v1,i1,tr1)) (rk2,(v2, i2, tr2)) 
  | (E_write_mem wk1 v1 i1 tr1 v1' tr1', E_write_mem wk2 v2 i2 tr2 v2' tr2') -> 
    compare ((wk1,v1,i1),(tr1,v1',tr1'))  ((wk2,v2,i2),(tr2,v2',tr2')) 
  | (E_write_ea wk1 a1 i1 tr1, E_write_ea wk2 a2 i2 tr2) ->
    compare (wk1, (a1, i1, tr1)) (wk2, (a2, i2, tr2))
  | (E_excl_res, E_excl_res) -> EQ
  | (E_write_memv _ mv1 tr1, E_write_memv _ mv2 tr2) -> compare (mv1,tr1) (mv2,tr2)
  | (E_write_memvt _ mv1 tr1, E_write_memvt _ mv2 tr2) -> compare (mv1,tr1) (mv2,tr2)
  | (E_barrier bk1, E_barrier bk2) -> compare bk1 bk2
  | (E_read_reg r1, E_read_reg r2) -> compare r1 r2
  | (E_write_reg r1 v1, E_write_reg r2 v2) -> compare (r1,v1) (r2,v2)
  | (E_error s1, E_error s2) -> compare s1 s2
  | (E_escape,E_escape) -> EQ
  | (E_read_mem _ _ _ _, _) -> LT
  | (E_write_mem _ _ _ _ _ _, _) -> LT
  | (E_write_ea _ _ _ _, _) -> LT
  | (E_excl_res, _) -> LT
  | (E_write_memv _ _ _, _) -> LT
  | (E_barrier _, _) -> LT
  | (E_read_reg _, _) -> LT
  | (E_write_reg _ _, _) -> LT
  | _ -> GT
  end

let eventLess b1 b2      = eventCompare b1 b2 =  LT
let eventLessEq b1 b2    = eventCompare b1 b2 <> GT
let eventGreater b1 b2   = eventCompare b1 b2 =  GT
let eventGreaterEq b1 b2 = eventCompare b1 b2 <> LT

instance (Ord event)
  let compare = eventCompare
  let (<)  = eventLess
  let (<=) = eventLessEq
  let (>)  = eventGreater
  let (>=) = eventGreaterEq
end

instance (SetType event)
  let setElemCompare = compare
end


(* the address_lifted types should go away here and be replaced by address *)
type with_aux 'o = 'o * maybe ((unit -> (string * string)) * ((list (reg_name * register_value)) -> list event))
type outcome 'a 'e =
  (* Request to read memory, value is location to read, integer is size to read,
     followed by registers that were used in computing that size *)
  | Read_mem of (read_kind * address_lifted * nat) * (memory_value -> with_aux (outcome 'a 'e))
  (* Tell the system a write is imminent, at address lifted, of size nat *)
  | Write_ea of (write_kind * address_lifted * nat) * (with_aux (outcome 'a 'e))
  (* Request the result of store-exclusive *)
  | Excl_res of (bool -> with_aux (outcome 'a 'e))
  (* Request to write memory at last signalled address. Memory value should be 8
     times the size given in ea signal *)
  | Write_memv of memory_value * (bool -> with_aux (outcome 'a 'e))
  (* Request a memory barrier *)
  | Barrier of barrier_kind * with_aux (outcome 'a 'e)
  (* Tell the system to dynamically recalculate dependency footprint *)
  | Footprint of with_aux (outcome 'a 'e)
  (* Request to read register, will track dependency when mode.track_values *)
  | Read_reg of reg_name * (register_value -> with_aux (outcome 'a 'e))
  (* Request to write register *)
  | Write_reg of (reg_name * register_value) * with_aux (outcome 'a 'e)
  | Escape of maybe string
  (*Result of a failed assert with possible error message to report*)
  | Fail of maybe string
  (* Exception of type 'e *)
  | Exception of 'e
  | Internal of (maybe string * maybe (unit -> string)) * with_aux (outcome 'a 'e)
  | Done of 'a
  | Error of string

type outcome_s 'a 'e = with_aux (outcome 'a 'e)
(* first string : output of instruction_stack_to_string
   second string: output of local_variables_to_string *)

(** operations and coercions on basic values *)

val word8_to_bitls : word8 -> list bit_lifted
val bitls_to_word8 : list bit_lifted -> word8

val integer_of_word8_list : list word8 -> integer
val word8_list_of_integer : integer -> integer -> list word8 

val concretizable_bitl : bit_lifted -> bool
val concretizable_bytl : byte_lifted -> bool
val concretizable_bytls : list byte_lifted -> bool

let concretizable_bitl = function
  | Bitl_zero -> true
  | Bitl_one -> true
  | Bitl_undef -> false
  | Bitl_unknown -> false
end 

let concretizable_bytl (Byte_lifted bs) = List.all concretizable_bitl bs
let concretizable_bytls = List.all concretizable_bytl

(* constructing values *)

val build_register_value : list bit_lifted -> direction -> nat -> nat -> register_value
let build_register_value bs dir width start_index =
  <| rv_bits = bs;
     rv_dir = dir; (* D_increasing for Power, D_decreasing for ARM *)
     rv_start_internal = start_index; 
     rv_start = if dir = D_increasing
       then start_index
       else (start_index+1) - width; (* Smaller index, as in Power, for external interaction *)
  |>

val register_value : bit_lifted -> direction -> nat -> nat -> register_value
let register_value b dir width start_index = 
  build_register_value (List.replicate width b) dir width start_index

val register_value_zeros : direction -> nat -> nat -> register_value
let register_value_zeros dir width start_index = 
  register_value Bitl_zero dir width start_index

val register_value_ones : direction -> nat -> nat -> register_value
let register_value_ones dir width start_index = 
  register_value Bitl_one dir width start_index

val register_value_for_reg : reg_name -> list bit_lifted -> register_value
let register_value_for_reg r bs : register_value =
  let () = ensure (width_of_reg_name r = List.length bs)
      ("register_value_for_reg (\"" ^ show (register_base_name r) ^ "\") length mismatch: "
          ^ show (width_of_reg_name r) ^ " vs " ^ show (List.length bs))
  in
  let (j1, j2) = slice_of_reg_name r in
  let d = direction_of_reg_name r in
  <|  rv_bits = bs;
      rv_dir = d;
      rv_start_internal = if d = D_increasing then j1 else (start_of_reg_name r) - j1;
      rv_start = j1;
  |>

val byte_lifted_undef : byte_lifted
let byte_lifted_undef = Byte_lifted (List.replicate 8 Bitl_undef)

val byte_lifted_unknown : byte_lifted
let byte_lifted_unknown = Byte_lifted (List.replicate 8 Bitl_unknown)
  
val memory_value_unknown : nat (*the number of bytes*) -> memory_value
let memory_value_unknown (width:nat) : memory_value = 
  List.replicate width byte_lifted_unknown 

val memory_value_undef : nat (*the number of bytes*) -> memory_value
let memory_value_undef (width:nat) : memory_value = 
  List.replicate width byte_lifted_undef 

val match_endianness : forall 'a. end_flag -> list 'a -> list 'a
let match_endianness endian l =
  match endian with
  | E_little_endian -> List.reverse l
  | E_big_endian    -> l
  end

(* lengths *)  

val memory_value_length : memory_value -> nat
let memory_value_length (mv:memory_value) = List.length mv


(* aux fns *)

val maybe_all : forall 'a.  list (maybe 'a) -> maybe (list 'a)
let rec maybe_all' xs acc = 
  match xs with
  | [] -> Just (List.reverse acc)
  | Nothing :: _ -> Nothing
  | (Just y)::xs' -> maybe_all' xs' (y::acc)
  end
let maybe_all xs = maybe_all' xs [] 

(** coercions *)

(* bits and bytes *)

let bit_to_bool = function (* TODO: rename bool_of_bit *)
  | Bitc_zero -> false
  | Bitc_one -> true
end


val bit_lifted_of_bit : bit -> bit_lifted
let bit_lifted_of_bit b = 
  match b with
  | Bitc_zero -> Bitl_zero
  | Bitc_one -> Bitl_one
  end

val bit_of_bit_lifted : bit_lifted -> maybe bit
let bit_of_bit_lifted bl =
  match bl with
  | Bitl_zero -> Just Bitc_zero
  | Bitl_one -> Just Bitc_one
  | Bitl_undef -> Nothing
  | Bitl_unknown -> Nothing
  end


val byte_lifted_of_byte : byte -> byte_lifted
let byte_lifted_of_byte (Byte bs) : byte_lifted = Byte_lifted (List.map bit_lifted_of_bit bs)

val byte_of_byte_lifted : byte_lifted -> maybe byte
let byte_of_byte_lifted bl = 
  match bl with
  | Byte_lifted bls -> 
      match maybe_all (List.map bit_of_bit_lifted bls) with
      | Nothing -> Nothing
      | Just bs -> Just (Byte bs)
      end
  end


val bytes_of_bits : list bit -> list byte (*assumes (length bits) mod 8 = 0*)
let rec bytes_of_bits bits = match bits with
  | [] -> []
  | b0::b1::b2::b3::b4::b5::b6::b7::bits -> 
    (Byte [b0;b1;b2;b3;b4;b5;b6;b7])::(bytes_of_bits bits)
  | _ -> failwith "bytes_of_bits not given bits divisible by 8"
end

val byte_lifteds_of_bit_lifteds : list bit_lifted -> list byte_lifted (*assumes (length bits) mod 8 = 0*)
let rec byte_lifteds_of_bit_lifteds bits = match bits with
  | [] -> []
  | b0::b1::b2::b3::b4::b5::b6::b7::bits -> 
    (Byte_lifted [b0;b1;b2;b3;b4;b5;b6;b7])::(byte_lifteds_of_bit_lifteds bits)
  | _ -> failwith "byte_lifteds of bit_lifteds not given bits divisible by 8"
end


val byte_of_memory_byte : memory_byte -> maybe byte
let byte_of_memory_byte = byte_of_byte_lifted

val memory_byte_of_byte : byte -> memory_byte
let memory_byte_of_byte = byte_lifted_of_byte


(* to and from nat *)

(* this natFromBoolList could move to the Lem word.lem library *)
val natFromBoolList : list bool -> nat
let rec natFromBoolListAux (acc : nat) (bl : list bool) = 
  match bl with 
    | [] -> acc
    | (true :: bl') -> natFromBoolListAux ((acc * 2) + 1) bl'
    | (false :: bl') -> natFromBoolListAux (acc * 2) bl'
  end
let natFromBoolList bl = 
  natFromBoolListAux 0 (List.reverse bl)


val nat_of_bit_list : list bit -> nat 
let nat_of_bit_list b =
  natFromBoolList (List.reverse (List.map bit_to_bool b))
  (* natFromBoolList takes a list with LSB first, for consistency with rest of Lem word library, so we reverse it. twice. *)


(* to and from integer *)

val integer_of_bit_list : list bit -> integer 
let integer_of_bit_list b =
  integerFromBoolList (false,(List.reverse (List.map bit_to_bool b)))
  (* integerFromBoolList takes a list with LSB first, so we reverse it *)

val bit_list_of_integer : nat -> integer -> list bit 
let bit_list_of_integer len b = 
  List.map (fun b -> if b then Bitc_one else Bitc_zero) 
    (reverse (boolListFrombitSeq len (bitSeqFromInteger Nothing b)))

val integer_of_byte_list : list byte -> integer 
let integer_of_byte_list bytes = integer_of_bit_list (List.concatMap (fun (Byte bs) -> bs) bytes)

val byte_list_of_integer : nat -> integer -> list byte 
let byte_list_of_integer (len:nat) (a:integer):list byte = 
  let bits = bit_list_of_integer (len * 8) a in bytes_of_bits bits


val integer_of_address : address -> integer 
let integer_of_address (a:address):integer = 
  match a with
  | Address bs i -> i 
  end

val address_of_integer : integer -> address 
let address_of_integer (i:integer):address =
  Address (byte_list_of_integer 8 i) i

(* to and from signed-integer *)

val signed_integer_of_bit_list : list bit -> integer
let signed_integer_of_bit_list b =
  match b with
  | [] -> failwith "empty bit list"
  | Bitc_zero :: b' ->
      integerFromBoolList (false,(List.reverse (List.map bit_to_bool b)))
  | Bitc_one :: b' ->
      let b'_val = integerFromBoolList (false,(List.reverse (List.map bit_to_bool b'))) in
      (* integerFromBoolList takes a list with LSB first, so we reverse it *)
      let msb_val = integerPow 2 ((List.length b) - 1) in
      b'_val - msb_val
  end


(* regarding a list of int as a list of bytes in memory, MSB lowest-address first, convert to an integer *)
val integer_address_of_int_list : list int -> integer
let rec integerFromIntListAux (acc: integer) (is: list int) = 
  match is with 
  | [] -> acc
  | (i :: is') -> integerFromIntListAux ((acc * 256) + integerFromInt i) is'
  end
let integer_address_of_int_list (is: list int) =
  integerFromIntListAux 0 is

val address_of_byte_list : list byte -> address 
let address_of_byte_list bs = 
  if List.length bs <> 8 then failwith "address_of_byte_list given list not of length 8" else 
  Address bs (integer_of_byte_list bs)

let address_of_byte_lifted_list bls =
  match maybe_all (List.map byte_of_byte_lifted bls) with
  | Nothing -> Nothing
  | Just bs -> Just (address_of_byte_list bs)
  end

(* operations on addresses *)

val add_address_nat : address -> nat -> address 
let add_address_nat (a:address) (i:nat) : address = 
  address_of_integer ((integer_of_address a) + (integerFromNat i))

val clear_low_order_bits_of_address : address -> address 
let clear_low_order_bits_of_address a = 
  match a with 
  | Address [b0;b1;b2;b3;b4;b5;b6;b7] i -> 
      match b7 with
      | Byte [bt0;bt1;bt2;bt3;bt4;bt5;bt6;bt7] -> 
          let b7' = Byte [bt0;bt1;bt2;bt3;bt4;bt5;Bitc_zero;Bitc_zero] in
	  let bytes = [b0;b1;b2;b3;b4;b5;b6;b7'] in
          Address bytes (integer_of_byte_list bytes)
      | _ -> failwith "Byte does not contain 8 bits"
      end
  | _ -> failwith "Address does not contain 8 bytes"
  end



val byte_list_of_memory_value : end_flag -> memory_value -> maybe (list byte)
let byte_list_of_memory_value endian mv =
  match_endianness endian mv
  $> List.map byte_of_memory_byte
  $> maybe_all


val integer_of_memory_value : end_flag -> memory_value -> maybe integer
let integer_of_memory_value endian (mv:memory_value):maybe integer =
  match byte_list_of_memory_value endian mv with
  | Just bs -> Just (integer_of_byte_list bs)
  | Nothing -> Nothing 
  end

val memory_value_of_integer : end_flag  -> nat -> integer -> memory_value
let memory_value_of_integer endian (len:nat) (i:integer):memory_value =
  List.map byte_lifted_of_byte (byte_list_of_integer len i)
  $> match_endianness endian


val integer_of_register_value : register_value -> maybe integer 
let integer_of_register_value (rv:register_value):maybe integer = 
  match maybe_all (List.map bit_of_bit_lifted rv.rv_bits) with
  | Nothing -> Nothing
  | Just bs -> Just (integer_of_bit_list bs)
  end

(* NOTE: register_value_for_reg_of_integer might be easier to use *)
val register_value_of_integer : nat -> nat -> direction -> integer -> register_value 
let register_value_of_integer (len:nat) (start:nat) (dir:direction) (i:integer):register_value =
  let bs = bit_list_of_integer len i in
  build_register_value (List.map bit_lifted_of_bit bs) dir len start

val register_value_for_reg_of_integer : reg_name -> integer -> register_value
let register_value_for_reg_of_integer (r: reg_name) (i:integer) : register_value =
  register_value_of_integer (width_of_reg_name r) (start_of_reg_name r) (direction_of_reg_name r) i

(* *)

val opcode_of_bytes : byte -> byte -> byte -> byte -> opcode
let opcode_of_bytes b0 b1 b2 b3 : opcode = Opcode [b0;b1;b2;b3]

val register_value_of_address : address -> direction -> register_value   
let register_value_of_address (Address bytes _) dir : register_value = 
  let bits = List.concatMap (fun (Byte bs) -> List.map bit_lifted_of_bit bs) bytes in
   <| rv_bits = bits;
      rv_dir = dir;
      rv_start = 0; 
      rv_start_internal = if dir = D_increasing then 0 else (List.length bits) - 1
   |>

val register_value_of_memory_value : memory_value -> direction -> register_value
let register_value_of_memory_value bytes dir : register_value =
  let bitls = List.concatMap (fun (Byte_lifted bs) -> bs) bytes in
  <| rv_bits = bitls;
     rv_dir = dir;
     rv_start = 0;
     rv_start_internal = if dir = D_increasing then 0 else (List.length bitls) - 1
   |>                                                     

val memory_value_of_register_value: register_value -> memory_value
let memory_value_of_register_value r =
  (byte_lifteds_of_bit_lifteds r.rv_bits)
   
val address_lifted_of_register_value : register_value -> maybe address_lifted
(* returning Nothing iff the register value is not 64 bits wide, but
allowing Bitl_undef and Bitl_unknown *)
let address_lifted_of_register_value (rv:register_value) : maybe address_lifted = 
  if List.length rv.rv_bits <> 64 then Nothing
  else 
    Just (Address_lifted (byte_lifteds_of_bit_lifteds rv.rv_bits)
                         (if List.all concretizable_bitl rv.rv_bits 
			  then match (maybe_all (List.map bit_of_bit_lifted rv.rv_bits)) with
                              | (Just(bits)) -> Just (integer_of_bit_list bits)
                              | Nothing -> Nothing end
			  else Nothing))

val address_of_address_lifted : address_lifted -> maybe address
(* returning Nothing iff the address contains any Bitl_undef or Bitl_unknown *)
let address_of_address_lifted (al:address_lifted): maybe address =
  match al with
  | Address_lifted bls (Just i)-> 
      match maybe_all ((List.map byte_of_byte_lifted) bls) with
      | Nothing -> Nothing
      | Just bs -> Just (Address bs i)
      end
  | _ -> Nothing
end

val address_of_register_value : register_value -> maybe address
(* returning Nothing iff the register value is not 64 bits wide, or contains Bitl_undef or Bitl_unknown *)
let address_of_register_value (rv:register_value) : maybe address = 
  match address_lifted_of_register_value rv with
  | Nothing -> Nothing
  | Just al -> 
      match address_of_address_lifted al with
      | Nothing -> Nothing
      | Just a -> Just a
      end
  end

let address_of_memory_value (endian: end_flag) (mv:memory_value) : maybe address =
  match byte_list_of_memory_value endian mv with
  | Nothing -> Nothing
  | Just bs -> 
      if List.length bs <> 8 then Nothing else
      Just (address_of_byte_list bs)
  end 

val byte_of_int : int -> byte
let byte_of_int (i:int) : byte = 
  Byte (bit_list_of_integer 8 (integerFromInt i))

val memory_byte_of_int : int -> memory_byte
let memory_byte_of_int (i:int) : memory_byte = 
  memory_byte_of_byte (byte_of_int i)

(*
val int_of_memory_byte : int -> maybe memory_byte
let int_of_memory_byte (mb:memory_byte) : int = 
  failwith "TODO"
*)



val memory_value_of_address_lifted : end_flag -> address_lifted -> memory_value
let memory_value_of_address_lifted endian (Address_lifted bs _ :address_lifted) =
  match_endianness endian bs

val byte_list_of_address : address -> list byte
let byte_list_of_address (Address bs _) : list byte = bs

val memory_value_of_address : end_flag -> address -> memory_value
let memory_value_of_address endian (Address bs _) =
  match_endianness endian bs
  $> List.map byte_lifted_of_byte

val byte_list_of_opcode : opcode -> list byte
let byte_list_of_opcode (Opcode bs) : list byte = bs

(** ****************************************** *)
(** show type class instantiations             *)
(** ****************************************** *)

(* matching printing_functions.ml *)
val stringFromReg_name : reg_name -> string
let stringFromReg_name r =
  let norm_sl start dir (first,second) = (first,second)
    (* match dir with
      | D_increasing -> (first,second)
      | D_decreasing -> (start - first, start - second)
    end *)
  in
  match r with
  | Reg s start size dir -> s
  | Reg_slice s start dir sl ->
      let (first,second) = norm_sl start dir sl in
      s ^ "[" ^ show first ^ (if (first = second) then "" else ".." ^ (show second)) ^ "]"
  | Reg_field s start dir f sl ->
      let (first,second) = norm_sl start dir sl in
      s ^ "." ^ f ^ " (" ^ (show start) ^ ", " ^ (show dir) ^ ", " ^ (show first) ^ ", " ^ (show second) ^ ")"
  | Reg_f_slice s start dir f (first1,second1) (first,second) ->
      let (first,second) =
        match dir with
        | D_increasing -> (first,second)
        | D_decreasing -> (start - first, start - second)
        end in
      s ^ "." ^ f ^ "]" ^ show first ^ (if (first = second) then "" else ".." ^ (show second)) ^ "]"
  end

instance (Show reg_name)
  let show = stringFromReg_name
end


(* hex pp of integers, adapting the Lem string_extra.lem code *)
val stringFromNaturalHexHelper : natural -> list char -> list char
let rec stringFromNaturalHexHelper n acc =
  if n = 0 then
    acc
  else
    stringFromNaturalHexHelper (n / 16) (String_extra.chr (natFromNatural (let nd = n mod 16 in if nd <=9 then nd + 48 else nd - 10 + 97)) :: acc)

val stringFromNaturalHex : natural -> string
let (*~{ocaml;hol}*) stringFromNaturalHex n = 
  if n = 0 then "0" else toString (stringFromNaturalHexHelper n [])

val stringFromIntegerHex : integer -> string
let (*~{ocaml}*) stringFromIntegerHex i = 
  if i < 0 then 
    "-" ^ stringFromNaturalHex (naturalFromInteger i)
  else
    stringFromNaturalHex (naturalFromInteger i)


let stringFromAddress (Address bs i) = 
  let i' = integer_of_byte_list bs in
  if i=i' then
(*TODO: ideally this should be made to match the src/pp.ml pp_address; the following very roughly matches what's used in the ppcmem UI, enough to make exceptions readable *)
    if i < 65535 then 
      show i 
    else
      stringFromIntegerHex i
  else
    "stringFromAddress bytes and integer mismatch"

instance (Show address)
  let show = stringFromAddress
end

let stringFromByte_lifted bl =
  match byte_of_byte_lifted bl with
  | Nothing -> "u?"  
  | Just (Byte bits) -> 
      let i = integer_of_bit_list bits in
      show i
  end

instance (Show byte_lifted)
  let show = stringFromByte_lifted
end

(* possible next instruction address options *)
type nia = 
  | NIA_successor
  | NIA_concrete_address of address
  | NIA_indirect_address

let niaCompare n1 n2 = match (n1,n2) with
  | (NIA_successor, NIA_successor) -> EQ
  | (NIA_successor, _) -> LT
  | (_, NIA_successor) -> GT
  | (NIA_concrete_address a1, NIA_concrete_address a2) -> compare a1 a2
  | (NIA_concrete_address _, _) -> LT
  | (_, NIA_concrete_address _) -> GT
  | (NIA_indirect_address, NIA_indirect_address) -> EQ
  (* | (NIA_indirect_address, _) -> LT
  | (_, NIA_indirect_address) -> GT *)
  end

instance (Ord nia)
  let compare = niaCompare
  let (<)  n1 n2 = (niaCompare n1 n2) = LT
  let (<=) n1 n2 = (niaCompare n1 n2) <> GT
  let (>)  n1 n2 = (niaCompare n1 n2) = GT
  let (>=) n1 n2 = (niaCompare n1 n2) <> LT
end

let stringFromNia = function
  | NIA_successor          -> "NIA_successor"
  | NIA_concrete_address a -> "NIA_concrete_address " ^ show a
  | NIA_indirect_address   -> "NIA_indirect_address"
end

instance (Show nia)
  let show = stringFromNia
end

type dia =
  | DIA_none
  | DIA_concrete_address of address
  | DIA_register of reg_name

let diaCompare d1 d2 = match (d1, d2) with
  | (DIA_none, DIA_none) -> EQ
  | (DIA_none, _) -> LT
  | (DIA_concrete_address a1, DIA_none) -> GT
  | (DIA_concrete_address a1, DIA_concrete_address a2) -> compare a1 a2
  | (DIA_concrete_address a1, _) -> LT
  | (DIA_register r1, DIA_register r2) -> compare r1 r2
  | (DIA_register _, _) -> GT
end

instance (Ord dia)
  let compare = diaCompare
  let (<)  n1 n2 = (diaCompare n1 n2) = LT
  let (<=) n1 n2 = (diaCompare n1 n2) <> GT
  let (>)  n1 n2 = (diaCompare n1 n2) = GT
  let (>=) n1 n2 = (diaCompare n1 n2) <> LT
end

let stringFromDia = function
  | DIA_none               ->  "DIA_none"
  | DIA_concrete_address a ->  "DIA_concrete_address " ^ show a
  | DIA_register r ->  "DIA_delayed_register " ^ show r
end

instance (Show dia)
  let show = stringFromDia
end
*)
