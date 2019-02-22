(************************************************************)
(* Support for toFromInterp                                 *)
(************************************************************)

open Sail_lib;;
open Value;;

type vector_order =
 | Order_inc
 | Order_dec


let zunitFromInterpValue v = match v with
  | V_unit -> ()
  | _ -> failwith "invalid interpreter value for unit"

let zunitToInterpValue () = V_unit


let zatomFromInterpValue typq_'n v = match v with
  | V_int i ->
     assert (typq_'n = i);
     i
  | _ -> failwith "invalid interpreter value for atom"

let zatomToInterpValue typq_'n v =
  assert (typq_'n = v);
  V_int v


let zvectorFromInterpValue typq_'n typq_'ord typq_'a v = match v with
  | V_vector vs ->
     assert (Big_int.of_int (List.length vs) = typq_'n);
     List.map typq_'a vs
  | _ -> failwith "invalid interpreter value for vector"

let zvectorToInterpValue typq_'n typq_'ord typq_'a v =
  assert (Big_int.of_int (List.length v) = typq_'n);
  V_vector (List.map typq_'a v)


let zbitFromInterpValue v = match v with
  | V_bit b -> b
  | _ -> failwith "invalid interpreter value for bit"

let zbitToInterpValue v = V_bit v
