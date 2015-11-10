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

(*Rmove me when switch to zarith*)
let rec power_big_int b n =
  if eq_big_int n zero_big_int
  then unit_big_int
  else mult_big_int b (power_big_int b (sub_big_int n unit_big_int))

let is_within_range candidate range constraints =
  match candidate.t with
  | Tapp("atom", [TA_nexp n]) ->
    (match n.nexp with
     | Nconst i | N2n(_,Some i) -> if check_in_range i range then Yes else No
     | _ -> Maybe)
  | Tapp("range", [TA_nexp bot; TA_nexp top]) ->
    (match bot.nexp,top.nexp with
     | Nconst b, Nconst t | Nconst b, N2n(_,Some t) | N2n(_, Some b), Nconst t | N2n(_,Some b), N2n(_, Some t) ->
       let at_least_in = check_in_range b range in
       let at_most_in = check_in_range t range in
       if at_least_in && at_most_in
       then Yes
       else if at_least_in || at_most_in
       then Maybe
       else No
     | _ -> Maybe)
  | Tapp("vector", [_; TA_nexp size ; _; _]) ->
    (match size.nexp with
     | Nconst i | N2n(_, Some i) ->
       if check_in_range (power_big_int (big_int_of_int 2) i) range
       then Yes
       else No
     | _ -> Maybe)
  | _ -> Maybe
