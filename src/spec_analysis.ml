open Ast
open Util
open Big_int
open Type_internal

type typ = Type_internal.t

(*Query a spec for its default order if one is provided. Assumes Inc if not *)
let get_default_order_sp (DT_aux(spec,_)) =
  match spec with
  | DT_order (Ord_aux(o,_)) ->
    (match o with
     | Ord_inc -> Some {order = Oinc}
     | Ord_dec -> Some { order = Odec}
     | _ -> Some {order = Oinc})
  | _ -> None

let get_default_order_def = function
  | DEF_default def_spec -> get_default_order_sp def_spec
  | _ -> None

let rec default_order (Defs defs) =
  match defs with
  | [] -> { order = Oinc } (*When no order is specified, we assume that it's inc*)
  | def::defs ->
    match get_default_order_def def with
    | None -> default_order (Defs defs)
    | Some o -> o
