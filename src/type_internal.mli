open Big_int

module Envmap : Finite_map.Fmap with type k = string
module Nameset : sig
  include Set.S with type elt = string
  val pp : Format.formatter -> t -> unit
end

val zero : big_int
val one  : big_int
val two  : big_int

type kind = { mutable k : k_aux }
and k_aux =
  | K_Typ
  | K_Nat
  | K_Ord
  | K_Efct
  | K_Val
  | K_Lam of kind list * kind
  | K_infer

type t_uvar
type n_uvar
type e_uvar
type o_uvar
type t = { mutable t : t_aux }
(*No recursive t will ever be Tfn *)
and t_aux =
  | Tvar of string (* concrete *)
  | Tid of string  (* concrete *)
  | Tfn of t * t * implicit_parm * effect  (* concrete *)
  | Ttup of t list (* concrete *)
  | Tapp of string * t_arg list (* concrete *)
  | Tabbrev of t * t (* first t is the type from the source; second is the actual ground type, never abbrev *)
  | Toptions of t * t option (* used in overloads or cast; first is always concrete. Removed in type checking *)
  | Tuvar of t_uvar (* Unification variable *)
(*Implicit nexp parameters for library and special function calls*)
and implicit_parm =
  | IP_none (*Standard function*)
  | IP_length (*Library function to take length of a vector as first parameter*)
  | IP_start (*Library functions to take start of a vector as first parameter*)
  | IP_var of nexp (*Special user functions, must be declared with val, will pass stated parameter to functions as above*)
and nexp = { mutable nexp : nexp_aux }
and nexp_aux =
  | Nvar of string
  | Nconst of big_int
  | Npos_inf (* Used to define nat and int types, does not arise from source otherwise *)
  | Nneg_inf (* Used to define int type, does not arise from source otherwise *)
  | Nadd of nexp * nexp
  | Nmult of nexp * nexp
  | N2n of nexp * big_int option (* Optionally contains the 2^n result for const n, for different constraint equations *)
  | Npow of nexp * int (* Does not appear in source *)
  | Nneg of nexp (* Does not appear in source *)
  | Ninexact (*Does not appear in source*)
  | Nuvar of n_uvar (* Unification variable *)
and effect = { mutable effect : effect_aux }
and effect_aux =
  | Evar of string
  | Eset of Ast.base_effect list
  | Euvar of e_uvar (* Unificiation variable *)
and order = { mutable order : order_aux }
and order_aux =
  | Ovar of string
  | Oinc
  | Odec
  | Ouvar of o_uvar (* Unification variable *)
and t_arg =
  | TA_typ of t
  | TA_nexp of nexp
  | TA_eft of effect
  | TA_ord of order 

type tag =
  | Emp_local (* Standard value, variable, expression *)
  | Emp_global (* Variable from global instead of local scope *)
  | External of string option (* External function or register name *)
  | Default (* Variable has default type, has not been bound *)
  | Constructor (* Variable is a data constructor *)
  | Enum (* Variable came from an enumeration *)
  | Alias (* Variable came from a register alias *)
  | Spec (* Variable came from a val specification *)

type constraint_origin =
  | Patt of Parse_ast.l
  | Expr of Parse_ast.l
  | Fun of Parse_ast.l
  | Specc of Parse_ast.l

(* Constraints for nexps, plus the location which added the constraint *)
type nexp_range =
  | LtEq of constraint_origin * nexp * nexp
  | Eq of constraint_origin * nexp * nexp
  | GtEq of constraint_origin * nexp * nexp
  | In of constraint_origin * string * int list
  | InS of constraint_origin * nexp * int list (* This holds the given value for string after a substitution *)
  | CondCons of constraint_origin * nexp_range list * nexp_range list (* Constraints from one path from a conditional (pattern or if) and the constraints from that conditional *)
  | BranchCons of constraint_origin * nexp_range list (* CondCons constraints from all branches of a conditional; list should be all CondCons *)

val get_c_loc : constraint_origin -> Parse_ast.l

val n_zero : nexp
val n_one : nexp
val n_two : nexp

type variable_range =
  | VR_eq of string * nexp
  | VR_range of string * nexp_range list
  | VR_vec_eq of string * nexp
  | VR_vec_r of string * nexp_range list
  | VR_recheck of string * t (*For cases where inference hasn't yet determined the type of v*)

type bounds_env = 
  | No_bounds
  | Bounds of variable_range list

type t_params = (string * kind) list
type tannot = 
  | NoTyp
  | Base of (t_params * t) * tag * nexp_range list * effect * bounds_env
  (* First tannot is the most polymorphic version; the list includes all variants. All t to be Tfn *)
  | Overload of tannot * bool * tannot list 

type 'a emap = 'a Envmap.t

type rec_kind = Record | Register
type rec_env = (string * rec_kind * ((string * tannot) list))
type alias_kind = OneReg of string * tannot | TwoReg of string * string * tannot | MultiReg of (string list) * tannot
type def_envs = { 
  k_env: kind emap; 
  abbrevs: tannot emap; 
  namesch : tannot emap; 
  enum_env : (string list) emap; 
  rec_env : rec_env list;
  alias_env : alias_kind emap;
  default_o : order;
 }

type exp = tannot Ast.exp

val lookup_record_typ : string -> rec_env list -> rec_env option
val lookup_record_fields : string list -> rec_env list -> rec_env option
val lookup_possible_records : string list -> rec_env list -> rec_env list
val lookup_field_type : string -> rec_env -> tannot

val add_effect : Ast.base_effect -> effect -> effect
val union_effects : effect -> effect -> effect

val initial_kind_env : kind Envmap.t
val initial_abbrev_env : tannot Envmap.t
val initial_typ_env : tannot Envmap.t
val nat_t : t
val unit_t : t
val bool_t : t
val bit_t : t
val pure_e : effect
val nob : bounds_env

val simple_annot : t -> tannot
val global_annot : t -> tannot
val tag_annot : t -> tag -> tannot
val constrained_annot : t -> nexp_range list -> tannot
val cons_tag_annot : t -> tag -> nexp_range list -> tannot
val cons_ef_annot : t -> nexp_range list -> effect -> tannot
val cons_bs_annot : t -> nexp_range list -> bounds_env -> tannot

val t_to_string : t -> string
val n_to_string : nexp -> string
val tannot_to_string : tannot -> string
val t_to_typ : t -> Ast.typ

val int_to_nexp : int -> nexp

val reset_fresh : unit -> unit
val new_t : unit -> t
val new_n : unit -> nexp
val new_o : unit -> order
val new_e : unit -> effect
val equate_t : t -> t -> unit

val subst : (string * kind) list -> t -> nexp_range list -> effect -> t * nexp_range list * effect
val get_abbrev : def_envs -> t -> (t * nexp_range list)

val extract_bounds : def_envs -> string -> t -> bounds_env
val merge_bounds : bounds_env -> bounds_env -> bounds_env

val normalize_nexp : nexp -> nexp
val get_index : nexp -> int (*TEMPORARILY expose nindex through this for debugging purposes*)

val select_overload_variant : def_envs -> bool -> bool -> tannot list -> t -> tannot list

(*May raise an exception if a contradiction is found*)
val resolve_constraints : nexp_range list -> nexp_range list
(* whether to actually perform constraint resolution or not *)
val do_resolve_constraints : bool ref

(*May raise an exception if effects do not match tannot effects, will lift unification variables to fresh type variables *)
val check_tannot : Parse_ast.l -> tannot -> nexp option -> nexp_range list -> effect -> tannot

val nexp_eq : nexp -> nexp -> bool

val conforms_to_t : def_envs -> bool -> bool -> t -> t -> bool

(* type_consistent is similar to a standard type equality, except in the case of [[consistent t1 t2]] where
   t1 and t2 are both range types and t1 is contained within the range of t2: i.e.
   range<2, 5> is consistent with range<0, 10>, but not vice versa.
   Similar for atom.
   When widen, two atoms are used to generate a range that contains them (or is defined by them for constants; and an atom and a range may widen the range.
   type_consistent mutates uvars to perform unification and will raise an error if the [[t1]] and [[t2]] are inconsistent
*)
val type_consistent : constraint_origin -> def_envs -> bool -> t -> t -> t * nexp_range list

(* type_coerce mutates to unify variables, and will raise an exception if the first type cannot
   be coerced into the second and is additionally inconsistent with the second; 
   bool specifices whether this has arisen from an implicit or explicit type coercion request *)
val type_coerce : constraint_origin -> def_envs -> bool -> bool -> t -> exp -> t -> t * nexp_range list * effect * exp

(* Merge tannots when intersection or unioning two environments. In case of default types, defer to tannot on right 
   When merging atoms, use bool to control widening. 
*)
val tannot_merge : constraint_origin -> def_envs -> bool -> tannot -> tannot -> tannot 
