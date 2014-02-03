module Envmap : Finite_map.Fmap with type k = string
module Nameset : sig
  include Set.S with type elt = string
  val pp : Format.formatter -> t -> unit
end

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
and t_aux =
  | Tvar of string
  | Tid of string
  | Tfn of t * t * effect
  | Ttup of t list
  | Tapp of string * t_arg list
  | Tuvar of t_uvar
and nexp = { mutable nexp : nexp_aux }
and nexp_aux =
  | Nvar of string
  | Nconst of int
  | Nadd of nexp * nexp
  | Nmult of nexp * nexp
  | N2n of nexp
  | Nneg of nexp (* Unary minus for representing new sizes after slicing *)
  | Nuvar of n_uvar
and effect = { mutable effect : effect_aux }
and effect_aux =
  | Evar of string
  | Eset of Ast.base_effect list
  | Euvar of e_uvar
and order = { mutable order : order_aux }
and order_aux =
  | Ovar of string
  | Oinc
  | Odec
  | Ouvar of o_uvar
and t_arg =
  | TA_typ of t
  | TA_nexp of nexp
  | TA_eft of effect
  | TA_ord of order 

type tag =
  | Emp
  | External
  | Default
  | Constructor
  | Enum
  | Spec

(* Constraints for nexps, plus the location which added the constraint, each nexp is either <= 0 = 0 or >= 0 *)
type nexp_range =
  | LtEq of Parse_ast.l * nexp * nexp
  | Eq of Parse_ast.l * nexp * nexp
  | GtEq of Parse_ast.l * nexp * nexp
  | In of Parse_ast.l * string * int list
  | InS of Parse_ast.l * nexp * int list (* This holds the given value for string after a substitution *)

type t_params = (string * kind) list
type tannot = ((t_params * t) * tag * nexp_range list) option
type 'a emap = 'a Envmap.t

type rec_kind = Record | Register
type def_envs = { 
  k_env: kind emap; 
  abbrevs: tannot emap; 
  namesch : tannot emap; 
  enum_env : (string list) emap; 
  rec_env : (string * rec_kind * ((string * tannot) list)) list;
 }

type exp = tannot Ast.exp

val initial_kind_env : kind Envmap.t
val initial_abbrev_env : tannot Envmap.t
val initial_typ_env : tannot Envmap.t
val nat_t : t
val unit_t : t
val bool_t : t
val bit_t : t

val reset_fresh : unit -> unit
val new_t : unit -> t
val new_n : unit -> nexp
val new_o : unit -> order
val new_e : unit -> effect

val subst : (string * kind) list -> t -> nexp_range list -> t * nexp_range list


(* type_consistent is similar to a standard type equality, except in the case of [[consistent t1 t2]] where
   t1 and t2 are both enum types and t1 is contained within the range of t2: i.e.
   enum 2 5 inc is consistent with enum 0 10 inc, but not vice versa.
   type_consistent mutates uvars to perform unification and will raise an error if the [[t1]] and [[t2]] are inconsitent
*)
val type_consistent : Parse_ast.l -> def_envs -> t -> t -> t * nexp_range list

(* type_eq mutates to unify variables, and will raise an exception if the first type cannot be coerced into the second *)
val type_coerce : Parse_ast.l -> def_envs -> t -> exp -> t -> t * nexp_range list * exp
