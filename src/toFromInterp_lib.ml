(************************************************************)
(* Support for toFromInterp                                 *)
(************************************************************)

open Sail_lib;;
open Value;;

type vector_order =
 | Order_inc
 | Order_dec

(* zencoded variants are for the OCaml backend, non-zencoded are for the Lem backend compiled to OCaml.
   Sometimes they're just aliased. *)

let zunitFromInterpValue v = match v with
  | V_unit -> ()
  | _ -> failwith "invalid interpreter value for unit"

let zunitToInterpValue () = V_unit

let unitFromInterpValue = zunitFromInterpValue
let unitToInterpValue = zunitToInterpValue

let zatomFromInterpValue typq_'n v = match v with
  | V_int i when typq_'n = i -> i
  | _ -> failwith "invalid interpreter value for atom"

let zatomToInterpValue typq_'n v =
  assert (typq_'n = v);
  V_int v

let atomFromInterpValue = zatomFromInterpValue
let atomToInterpValue = zatomToInterpValue 

let zintFromInterpValue v = match v with
  | V_int i -> i
  | _ -> failwith "invalid interpreter value for int"

let zintToInterpValue v = V_int v

let intFromInterpValue = zintFromInterpValue
let intToInterpValue = zintToInterpValue 

let znatFromInterpValue v = match v with
  | V_int i when i >= Big_int.zero -> i
  | _ -> failwith "invalid interpreter value for nat"

let znatToInterpValue v =
  assert (v >= Big_int.zero);
  V_int v

let natFromInterpValue = znatFromInterpValue
let natToInterpValue = znatToInterpValue 


let zboolFromInterpValue v = match v with
  | V_bool b -> b
  | _ -> failwith "invalid interpreter value for bool"

let zboolToInterpValue v = V_bool v

let boolFromInterpValue = zboolFromInterpValue
let boolToInterpValue = zboolToInterpValue 

let zstringFromInterpValue v = match v with
  | V_string s -> s
  | _ -> failwith "invalid interpreter value for string"

let zstringToInterpValue v = V_string v

let stringFromInterpValue = zstringFromInterpValue
let stringToInterpValue = zstringToInterpValue 

let zlistFromInterpValue typq_'a v = match v with
  | V_list vs -> List.map typq_'a vs
  | _ -> failwith "invalid interpreter value for list"

let zlistToInterpValue typq_'a v = V_list (List.map typq_'a v)

let listFromInterpValue = zlistFromInterpValue
let listToInterpValue = zlistToInterpValue 

let zvectorFromInterpValue typq_'n typq_'ord typq_'a v = match v with
  | V_vector vs ->
     assert (Big_int.of_int (List.length vs) = typq_'n);
     List.map typq_'a vs
  | _ -> failwith "invalid interpreter value for vector"

let zvectorToInterpValue typq_'n typq_'ord typq_'a v =
  assert (Big_int.of_int (List.length v) = typq_'n);
  V_vector (List.map typq_'a v)

let vectorFromInterpValue = zvectorFromInterpValue
let vectorToInterpValue = zvectorToInterpValue 

let zbitFromInterpValue v = match v with
  | V_bit b -> b
  | _ -> failwith "invalid interpreter value for bit"

let zbitToInterpValue v = V_bit v

let bitFromInterpValue = zbitFromInterpValue
let bitToInterpValue = zbitToInterpValue

let optionFromInterpValue typq_'a v = match v with
  | V_ctor ("None", [v0]) -> None
  | V_ctor ("Some", [v0]) -> Some (typq_'a v0)
  | _ -> failwith "invalid interpreter value for option"

let optionToInterpValue typq_'a v = match v with
  | None -> V_ctor ("None", [(unitToInterpValue ())])
  | Some (v0) -> V_ctor ("Some", [(typq_'a v0)])


let bitsFromInterpValue typq_'n v = match v with
  | V_vector vs ->
     assert (Big_int.of_int (List.length vs) = typq_'n);
     Lem.wordFromBitlist (List.map (fun b -> bitFromInterpValue b |> Sail_lib.bool_of_bit) vs)
  | _ -> failwith "invalid interpreter value for bits"

let bitsToInterpValue typq_'n v =
  let bs = Lem.bitlistFromWord v in
  assert (Big_int.of_int (List.length bs) = typq_'n);
  V_vector (List.map (fun b -> Sail_lib.bit_of_bool b |> bitToInterpValue) bs)


