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

(*Is within range*)

let check_in_range (candidate : big_int) (range : typ) : bool =
  match range.t with
  | Tapp("range", [TA_nexp min; TA_nexp max]) | Tabbrev(_,{t=Tapp("range", [TA_nexp min; TA_nexp max])}) ->
    let min,max = 
      match min.nexp,max.nexp with
      | (Nconst min, Nconst max)
      | (Nconst min, N2n(_, Some max))
      | (N2n(_, Some min), Nconst max)
      | (N2n(_, Some min), N2n(_, Some max))
        -> min, max
      | (Nneg n, Nconst max) | (Nneg n, N2n(_, Some max))->
        (match n.nexp with
         | Nconst abs_min | N2n(_,Some abs_min) ->
           (minus_big_int abs_min), max
         | _ -> assert false (*Put a better error message here*))
      | (Nconst min,Nneg n) | (N2n(_, Some min), Nneg n) ->
        (match n.nexp with
         | Nconst abs_max | N2n(_,Some abs_max) ->
           min, (minus_big_int abs_max)
         | _ -> assert false (*Put a better error message here*))
    | (Nneg nmin, Nneg nmax) ->
      ((match nmin.nexp with
          | Nconst abs_min | N2n(_,Some abs_min) -> (minus_big_int abs_min)
          | _ -> assert false (*Put a better error message here*)),
       (match nmax.nexp with
        | Nconst abs_max | N2n(_,Some abs_max) -> (minus_big_int abs_max)
        | _ -> assert false (*Put a better error message here*)))
    | _ -> assert false        
    in le_big_int min candidate && le_big_int candidate max
  | _ -> assert false

       
let is_within_range candidate range constraints =
  match candidate.t with
  | Tapp("atom", [TA_nexp n]) ->
    (match n.nexp with
     | Nconst i -> if check_in_range i range then Yes else No
     | _ -> Maybe)
