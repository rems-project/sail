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
  | Nneg of nexp (* Unary minus for representing new vector sizes after vector slicing *)
  | Nuvar of n_uvar
and effect = { mutable effect : effect_aux }
and effect_aux =
  | Evar of string
  | Eset of Ast.efct_aux list
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

(* Constraints for nexps, plus the location which added the constraint, each nexp is either <= 0 = 0 or >= 0 *)
type nexp_range =
  | LtEq of Parse_ast.l * nexp
  | Eq of Parse_ast.l * nexp
  | GtEq of Parse_ast.l * nexp
  | In of Parse_ast.l * nexp * nexp list

type tannot = (t * nexp_range list) option

val initial_kind_env : kind Envmap.t
