open Ast
open IdUtil
open PatternMatch
open TypeAnnot
open ValueType

module Value =
 functor (Tannot:S) ->
 struct
  type t = value

  (** val join : t -> t -> t **)

  let join x y =
    if value_eqb x y then x else V_unit

  (** val v_unit : value **)

  let v_unit =
    V_unit

  (** val v_list : value list -> value **)

  let v_list x =
    V_list x

  (** val v_tuple : value list -> value **)

  let v_tuple x =
    V_tuple x

  (** val v_vector : value list -> value **)

  let v_vector x =
    V_vector x

  (** val v_ref : id -> value **)

  let v_ref x =
    V_ref x

  (** val of_lit : lit -> value **)

  let of_lit =
    value_of_lit

  (** val is_unit : t -> bool **)

  let is_unit = function
  | V_unit -> true
  | _ -> false

  (** val is_true : t -> bool **)

  let is_true = function
  | V_bool b -> b
  | _ -> false

  (** val is_false : t -> bool **)

  let is_false = function
  | V_bool b -> if b then false else true
  | _ -> false

  (** val lookup_field' : (id * t) list -> id -> t **)

  let rec lookup_field' fields name =
    match fields with
    | [] -> V_unit
    | p :: fields0 ->
      let (name', v) = p in
      if id_eqb name name' then v else lookup_field' fields0 name

  (** val lookup_field : t -> id -> t **)

  let lookup_field rec0 name =
    match rec0 with
    | V_record fields -> lookup_field' fields name
    | _ -> V_unit

  module PM = Make(Tannot)

  (** val pattern_match : Tannot.t pat -> t -> t match_result **)

  let pattern_match =
    PM.pattern_match

  (** val complete : t binding -> t **)

  let complete = function
  | Complete v -> v
  | Partial vs -> complete_value vs
 end
