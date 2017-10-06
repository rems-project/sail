open Big_int
open Util

(* ===== Integer Constraints ===== *)

type nexp_op = Plus | Minus | Mult

type nexp =
  | NFun of (nexp_op * nexp * nexp)
  | N2n of nexp
  | NConstant of big_int
  | NVar of int

let big_int_op : nexp_op -> big_int -> big_int -> big_int = function
  | Plus -> add_big_int
  | Minus -> sub_big_int
  | Mult -> mult_big_int

let rec arith constr =
  let constr' = match constr with
    | NFun (op, x, y) -> NFun (op, arith x, arith y)
    | N2n c -> N2n (arith c)
    | c -> c
  in
  match constr' with
  | NFun (op, NConstant x, NConstant y) -> NConstant (big_int_op op x y)
  | N2n (NConstant x) -> NConstant (power_int_positive_big_int 2 x)
  | c -> c

(* ===== Boolean Constraints ===== *)

type constraint_bool_op = And | Or

type constraint_compare_op = Gt | Lt | GtEq | LtEq | Eq | NEq

let negate_comparison = function
  | Gt -> LtEq
  | Lt -> GtEq
  | GtEq -> Lt
  | LtEq -> Gt
  | Eq -> NEq
  | NEq -> Eq

type 'a constraint_bool =
  | BFun of (constraint_bool_op * 'a constraint_bool * 'a constraint_bool)
  | Not of 'a constraint_bool
  | CFun of (constraint_compare_op * 'a * 'a)
  | Branch of ('a constraint_bool list)
  | Boolean of bool

let rec pairs (xs : 'a list) (ys : 'a list) : ('a * 'b) list =
  match xs with
  | [] -> []
  | (x :: xs) -> List.map (fun y -> (x, y)) ys @ pairs xs ys

let rec unbranch : 'a constraint_bool -> 'a constraint_bool list = function
  | Branch xs -> List.map unbranch xs |> List.concat
  | Not x -> unbranch x |> List.map (fun y -> Not y)
  | BFun (op, x, y) ->
     let xs, ys = unbranch x, unbranch y in
     List.map (fun (z, w) -> BFun (op, z, w)) (pairs xs ys)
  | c -> [c]

(* Apply De Morgan's laws to push all negations to just before integer
   constraints *)
let rec de_morgan : 'a constraint_bool -> 'a constraint_bool = function
  | Not (Not x) -> de_morgan x
  | Not (BFun (And, x, y)) -> BFun (Or, de_morgan (Not x), de_morgan (Not y))
  | Not (BFun (Or, x, y)) -> BFun (And, de_morgan (Not x), de_morgan (Not y))
  | Not (Boolean b) -> Boolean (not b)
  | BFun (op, x, y) -> BFun (op, de_morgan x, de_morgan y)
  | c -> c

(* Once De Morgan's laws are applied we can push all the Nots into
   comparison constraints *)
let rec remove_nots : 'a constraint_bool -> 'a constraint_bool = function
  | BFun (op, x, y) -> BFun (op, remove_nots x, remove_nots y)
  | Not (CFun (c, x, y)) -> CFun (negate_comparison c, x, y)
  | c -> c

(* Apply distributivity so all Or clauses are within And clauses *)
let rec distrib_step : 'a constraint_bool -> ('a constraint_bool * int) = function
  | BFun (Or, x, BFun (And, y, z)) ->
     let (xy, n) = distrib_step (BFun (Or, x, y)) in
     let (xz, m) = distrib_step (BFun (Or, x, z)) in
     BFun (And, xy, xz), n + m + 1
  | BFun (Or, BFun (And, x, y), z) ->
     let (xz, n) = distrib_step (BFun (Or, x, z)) in
     let (yz, m) = distrib_step (BFun (Or, y, z)) in
     BFun (And, xz, yz), n + m + 1
  | BFun (op, x, y) ->
     let (x', n) = distrib_step x in
     let (y', m) = distrib_step y in
     BFun (op, x', y'), n + m
  | c -> (c, 0)

let rec distrib (c : 'a constraint_bool) : 'a constraint_bool =
  let (c', n) = distrib_step c in
  if n = 0 then c else distrib c'

(* Once these steps have been applied, the constraint language is a
   list of And clauses, each a list of Or clauses, with either
   explicit booleans (LBool) or integer comparisons LFun. The flatten
   function coverts from a constraint_bool to this representation. *)
type 'a constraint_leaf =
  | LFun of (constraint_compare_op * 'a * 'a)
  | LBoolean of bool

let rec flatten_or : 'a constraint_bool -> 'a constraint_leaf list = function
  | BFun (Or, x, y) -> flatten_or x @ flatten_or y
  | CFun comparison -> [LFun comparison]
  | Boolean b -> [LBoolean b]
  | _ -> assert false

let rec flatten : 'a constraint_bool -> 'a constraint_leaf list list = function
  | BFun (And, x, y) -> flatten x @ flatten y
  | Boolean b -> [[LBoolean b]]
  | c -> [flatten_or c]

let normalize (constr : 'a constraint_bool) : 'a constraint_leaf list list =
  constr
  |> de_morgan
  |> remove_nots
  |> distrib
  |> flatten

(* Get a set of variables from a constraint *)
module IntSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = int
  end)

let rec int_expr_vars : nexp -> IntSet.t = function
  | NConstant _ -> IntSet.empty
  | NVar v -> IntSet.singleton v
  | NFun (_, x, y) -> IntSet.union (int_expr_vars x) (int_expr_vars y)
  | N2n x -> int_expr_vars x

let leaf_expr_vars : nexp constraint_leaf -> IntSet .t = function
  | LBoolean _ -> IntSet.empty
  | LFun (_, x, y) -> IntSet.union (int_expr_vars x) (int_expr_vars y)

let constraint_vars constr : IntSet.t =
  constr
  |> List.map (List.map leaf_expr_vars)
  |> List.map (List.fold_left IntSet.union IntSet.empty)
  |> List.fold_left IntSet.union IntSet.empty

(* SMTLIB v2.0 format is based on S-expressions so we have a
   lightweight representation of those here. *)
type sexpr = List of (sexpr list) | Atom of string

let sfun (fn : string) (xs : sexpr list) : sexpr = List (Atom fn :: xs)

let rec pp_sexpr : sexpr -> string = function
  | List xs -> "(" ^ string_of_list " " pp_sexpr xs ^ ")"
  | Atom x -> x

let var_decs constr =
  constraint_vars constr
  |> IntSet.elements
  |> List.map (fun var -> sfun "declare-const" [Atom ("v" ^ string_of_int var); Atom "Int"])
  |> string_of_list "\n" pp_sexpr

let cop_sexpr op x y =
  match op with
  | Gt -> sfun ">" [x; y]
  | Lt -> sfun "<" [x; y]
  | GtEq -> sfun ">=" [x; y]
  | LtEq -> sfun "<=" [x; y]
  | Eq -> sfun "=" [x; y]
  | NEq -> sfun "not" [sfun "=" [x; y]]

let iop_sexpr op x y =
  match op with
  | Plus -> sfun "+" [x; y]
  | Minus -> sfun "-" [x; y]
  | Mult -> sfun "*" [x; y]

let rec sexpr_of_nexp = function
  | NFun (op, x, y) -> iop_sexpr op (sexpr_of_nexp x) (sexpr_of_nexp y)
  | N2n x -> sfun "^" [Atom "2"; sexpr_of_nexp x]
  | NConstant c -> Atom (string_of_big_int c) (* CHECK: do we do negative constants right? *)
  | NVar var -> Atom ("v" ^ string_of_int var)

let rec sexpr_of_cbool = function
  | BFun (And, x, y) -> sfun "and" [sexpr_of_cbool x; sexpr_of_cbool y]
  | BFun (Or, x, y) -> sfun "or" [sexpr_of_cbool x; sexpr_of_cbool y]
  | Not x -> sfun "not" [sexpr_of_cbool x]
  | CFun (op, x, y) -> cop_sexpr op (sexpr_of_nexp (arith x)) (sexpr_of_nexp (arith y))
  | Branch xs -> sfun "BRANCH" (List.map sexpr_of_cbool xs)
  | Boolean true -> Atom "true"
  | Boolean false -> Atom "false"

let sexpr_of_constraint_leaf = function
  | LFun (op, x, y) -> cop_sexpr op (sexpr_of_nexp (arith x)) (sexpr_of_nexp (arith y))
  | LBoolean true -> Atom "true"
  | LBoolean false -> Atom "false"

let sexpr_of_constraint constr : sexpr =
  constr
  |> List.map (List.map sexpr_of_constraint_leaf)
  |> List.map (fun xs -> match xs with [x] -> x | _ -> (sfun "or" xs))
  |> sfun "and"

let smtlib_of_constraint constr : string =
  "(push)\n"
  ^ var_decs constr ^ "\n"
  ^ pp_sexpr (sfun "define-fun" [Atom "constraint"; List []; Atom "Bool"; sexpr_of_constraint constr])
  ^ "\n(assert constraint)\n(check-sat)\n(pop)"

type t = nexp constraint_bool

type smt_result = Unknown | Sat | Unsat

module DigestMap = Map.Make(Digest)

let known_problems = ref (DigestMap.empty)

let load_digests_err () =
  let in_chan = open_in_bin "z3_problems" in
  let rec load () =
    let digest = Digest.input in_chan in
    let result = input_byte in_chan in
    begin
      match result with
      | 0 -> known_problems := DigestMap.add digest Unknown !known_problems
      | 1 -> known_problems := DigestMap.add digest Sat !known_problems
      | 2 -> known_problems := DigestMap.add digest Unsat !known_problems
      | _ -> assert false
    end;
    load ()
  in
  try load () with
  | End_of_file -> close_in in_chan

let load_digests () =
  try load_digests_err () with
  | Sys_error _ -> ()

let save_digests () =
  let out_chan = open_out_bin "z3_problems" in
  let output digest result =
    Digest.output out_chan digest;
    match result with
    | Unknown -> output_byte out_chan 0
    | Sat -> output_byte out_chan 1
    | Unsat -> output_byte out_chan 2
  in
  DigestMap.iter output !known_problems;
  close_out out_chan

let rec call_z3 constraints : smt_result =
  let problems = unbranch constraints in
  let z3_file =
    problems
    |> List.map normalize
    |> List.map smtlib_of_constraint
    |> string_of_list "\n" (fun x -> x)
  in

  (* prerr_endline (Printf.sprintf "SMTLIB2 constraints are: \n%s%!" z3_file); *)

  let rec input_lines chan = function
    | 0 -> []
    | n ->
       begin
         let l = input_line chan in
         let ls = input_lines chan (n - 1) in
         l :: ls
       end
  in

  let digest = Digest.string z3_file in
  try
    let result = DigestMap.find digest !known_problems in
    result
  with
  | Not_found ->
    begin
      let (input_file, tmp_chan) = Filename.open_temp_file "constraint_" ".sat" in
      output_string tmp_chan z3_file;
      close_out tmp_chan;
      let z3_chan = Unix.open_process_in ("z3 -t:1000 -T:10 " ^ input_file) in
      let z3_output = List.combine problems (input_lines z3_chan (List.length problems)) in
      let _ = Unix.close_process_in z3_chan in
      Sys.remove input_file;
      try
        let (problem, _) = List.find (fun (_, result) -> result = "unsat") z3_output in
        known_problems := DigestMap.add digest Unsat !known_problems;
        Unsat
      with
      | Not_found ->
         let unsolved = List.filter (fun (_, result) -> result = "unknown") z3_output in
         if unsolved == []
         then (known_problems := DigestMap.add digest Sat !known_problems; Sat)
         else (known_problems := DigestMap.add digest Unknown !known_problems; Unknown)
    end

let string_of constr =
  constr
  |> unbranch
  |> List.map normalize
  |> List.map (fun c -> smtlib_of_constraint c)
  |> string_of_list "\n" (fun x -> x)

(* ===== Abstract API for building constraints ===== *)

(* These functions are exported from constraint.mli, and ensure that
   the internal representation of constraints remains opaque. *)

let implies (x : t) (y : t) : t =
  BFun (Or, Not x, y)

let conj (x : t) (y : t) : t =
  BFun (And, x, y)

let disj (x : t) (y : t) : t =
  BFun (Or, x, y)

let negate (x : t) : t = Not x

let branch (xs : t list) : t = Branch xs

let literal (b : bool) : t = Boolean b

let lt x y : t = CFun (Lt, x, y)

let lteq x y : t = CFun (LtEq, x, y)

let gt x y : t = CFun (Gt, x, y)

let gteq x y : t = CFun (GtEq, x, y)

let eq x y : t = CFun (Eq, x, y)

let neq x y : t = CFun (NEq, x, y)

let pow2 x : nexp = N2n x

let add x y : nexp = NFun (Plus, x, y)

let sub x y : nexp = NFun (Minus, x, y)

let mult x y : nexp = NFun (Mult, x, y)

let constant (x : big_int) : nexp = NConstant x

let variable (v : int) : nexp = NVar v
