open Ast
open AstInduction
open Bit
open Datatypes
open IdUtil
open List0
open ListDef
open ListUtil
open PatternMatch
open PeanoNat
open Specif
open TypeAnnot
open ValueType
open Wf

(** val is_value : 'a1 exp -> bool **)

let is_value = function
| E_aux (e, _) -> (match e with
                   | E_internal_value _ -> true
                   | _ -> false)

type return_value =
| Return_ok of value
| Return_exception of value

type var_type =
| Var_local
| Var_register

type place =
| PL_id of id * var_type
| PL_register of id
| PL_vector of place * Big_int_Z.big_int
| PL_vector_range of place * Big_int_Z.big_int * Big_int_Z.big_int
| PL_field of place * id

type destructure =
| DL_app of id * value list
| DL_tuple of destructure list
| DL_vector_concat of (Types.vector_concat_split * destructure) list
| DL_place of place

module Monad =
 struct
  type 'a t =
  | Pure of 'a
  | Early_return of value
  | Exception of value
  | Runtime_type_error of Parse_ast.l
  | Match_failure of Parse_ast.l
  | Assertion_failed of string
  | Call of id * value list * (return_value -> 'a t)
  | Read_var of place * (value -> 'a t)
  | Write_var of place * value * (unit -> 'a t)
  | Get_undefined of typ * (value -> 'a t)

  (** val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t **)

  let rec bind m f =
    match m with
    | Pure x -> f x
    | Early_return v -> Early_return v
    | Exception v -> Exception v
    | Runtime_type_error l -> Runtime_type_error l
    | Match_failure l -> Match_failure l
    | Assertion_failed msg -> Assertion_failed msg
    | Call (id0, args, cont) -> Call (id0, args, (fun v -> bind (cont v) f))
    | Read_var (r, cont) -> Read_var (r, (fun v -> bind (cont v) f))
    | Write_var (r, v, cont) -> Write_var (r, v, (fun u -> bind (cont u) f))
    | Get_undefined (t0, cont) ->
      Get_undefined (t0, (fun v -> bind (cont v) f))

  (** val fmap : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec fmap f = function
  | Pure x -> Pure (f x)
  | Early_return v -> Early_return v
  | Exception v -> Exception v
  | Runtime_type_error l -> Runtime_type_error l
  | Match_failure l -> Match_failure l
  | Assertion_failed msg -> Assertion_failed msg
  | Call (id0, args, cont) -> Call (id0, args, (fun v -> fmap f (cont v)))
  | Read_var (r, cont) -> Read_var (r, (fun v -> fmap f (cont v)))
  | Write_var (r, v, cont) -> Write_var (r, v, (fun u -> fmap f (cont u)))
  | Get_undefined (t0, cont) -> Get_undefined (t0, (fun v -> fmap f (cont v)))

  (** val pure : 'a1 -> 'a1 t **)

  let pure x =
    Pure x

  (** val lift_option : Parse_ast.l -> 'a1 option -> 'a1 t **)

  let lift_option l = function
  | Some y -> Pure y
  | None -> Runtime_type_error l

  (** val sequence : 'a1 t list -> 'a1 list t **)

  let rec sequence = function
  | [] -> pure []
  | m :: ms -> bind m (fun x -> bind (sequence ms) (fun xs -> pure (x :: xs)))

  (** val get_undefined : typ -> value t **)

  let get_undefined typ0 =
    Get_undefined (typ0, pure)

  (** val throw : value -> 'a1 t **)

  let throw v =
    Exception v

  type 'a caught =
  | Continue of 'a
  | Caught of value

  (** val catch : 'a1 t -> 'a1 caught t **)

  let catch = function
  | Pure x -> Pure (Continue x)
  | Early_return v -> Early_return v
  | Exception v -> Pure (Caught v)
  | Runtime_type_error l -> Runtime_type_error l
  | Match_failure l -> Match_failure l
  | Assertion_failed msg -> Assertion_failed msg
  | Call (id0, args, cont) ->
    Call (id0, args, (fun v -> fmap (fun x -> Continue x) (cont v)))
  | Read_var (r, cont) ->
    Read_var (r, (fun v -> fmap (fun x -> Continue x) (cont v)))
  | Write_var (r, v, cont) ->
    Write_var (r, v, (fun _ -> fmap (fun x -> Continue x) (cont ())))
  | Get_undefined (t0, cont) ->
    Get_undefined (t0, (fun v -> fmap (fun x -> Continue x) (cont v)))
 end

type 'a evaluated =
| Evaluated of 'a
| Unevaluated

(** val get_bool : 'a1 exp -> bool evaluated Monad.t **)

let get_bool = function
| E_aux (e, annot0) ->
  (match e with
   | E_internal_value v ->
     (match v with
      | V_bool b -> Monad.pure (Evaluated b)
      | _ -> Monad.Runtime_type_error (fst annot0))
   | _ -> Monad.pure Unevaluated)

(** val get_string : 'a1 exp -> string evaluated Monad.t **)

let get_string = function
| E_aux (e, annot0) ->
  (match e with
   | E_internal_value v ->
     (match v with
      | V_string s -> Monad.pure (Evaluated s)
      | _ -> Monad.Runtime_type_error (fst annot0))
   | _ -> Monad.pure Unevaluated)

(** val get_value : 'a1 exp -> value evaluated **)

let get_value = function
| E_aux (e, _) ->
  (match e with
   | E_internal_value v -> Evaluated v
   | _ -> Unevaluated)

(** val all_evaluated : 'a1 exp list -> value list **)

let rec all_evaluated = function
| [] -> []
| e :: xs0 ->
  let E_aux (e0, _) = e in
  (match e0 with
   | E_internal_value v -> v :: (all_evaluated xs0)
   | _ -> all_evaluated xs0)

(** val coerce_place : Parse_ast.l -> destructure -> place Monad.t **)

let coerce_place loc = function
| DL_place p -> Monad.pure p
| _ -> Monad.Runtime_type_error loc

(** val left_to_right : 'a1 exp list -> 'a1 exp list * 'a1 exp list **)

let rec left_to_right = function
| [] -> ([], [])
| x :: xs0 ->
  let E_aux (e, annot0) = x in
  (match e with
   | E_internal_value v ->
     let (vs, xs') = left_to_right xs0 in
     (((E_aux ((E_internal_value v), annot0)) :: vs), xs')
   | _ -> ([], (x :: xs0)))

(** val all_evaluated_fields : 'a1 fexp list -> (id * value) list **)

let rec all_evaluated_fields = function
| [] -> []
| f :: xs0 ->
  let FE_aux (f0, _) = f in
  let FE_fexp (id0, e) = f0 in
  let E_aux (e0, _) = e in
  (match e0 with
   | E_internal_value v -> (id0, v) :: (all_evaluated_fields xs0)
   | _ -> all_evaluated_fields xs0)

(** val left_to_right_fields :
    'a1 fexp list -> 'a1 fexp list * 'a1 fexp list **)

let rec left_to_right_fields = function
| [] -> ([], [])
| x :: xs0 ->
  let FE_aux (f, fe_annot) = x in
  let FE_fexp (id0, e) = f in
  let E_aux (e0, annot0) = e in
  (match e0 with
   | E_internal_value v ->
     let (vs, xs') = left_to_right_fields xs0 in
     (((FE_aux ((FE_fexp (id0, (E_aux ((E_internal_value v), annot0)))),
     fe_annot)) :: vs), xs')
   | _ -> ([], (x :: xs0)))

type 'a ltr2 =
| LTR2_0 of 'a exp * 'a exp
| LTR2_1 of value * 'a exp
| LTR2_2 of value * value

(** val left_to_right2 : 'a1 exp -> 'a1 exp -> 'a1 ltr2 **)

let left_to_right2 x y =
  let E_aux (e1, _) = x in
  (match e1 with
   | E_internal_value v1 ->
     let E_aux (e2, _) = y in
     (match e2 with
      | E_internal_value v2 -> LTR2_2 (v1, v2)
      | _ -> LTR2_1 (v1, y))
   | _ -> LTR2_0 (x, y))

type 'a ltr3 =
| LTR3_0 of 'a exp * 'a exp * 'a exp
| LTR3_1 of value * 'a exp * 'a exp
| LTR3_2 of value * value * 'a exp
| LTR3_3 of value * value * value

(** val left_to_right3 : 'a1 exp -> 'a1 exp -> 'a1 exp -> 'a1 ltr3 **)

let left_to_right3 x y z =
  let p = (x, y) in
  let (e0, e1) = p in
  let E_aux (e2, _) = e0 in
  (match e2 with
   | E_internal_value v1 ->
     let E_aux (e3, _) = e1 in
     (match e3 with
      | E_internal_value v2 ->
        let E_aux (e4, _) = z in
        (match e4 with
         | E_internal_value v3 -> LTR3_3 (v1, v2, v3)
         | _ -> LTR3_2 (v1, v2, z))
      | _ -> LTR3_1 (v1, y, z))
   | _ -> LTR3_0 (x, y, z))

module Make =
 functor (Tannot:S) ->
 struct
  module PM = Make(Tannot)

  (** val substitute : id -> value -> 'a1 exp -> 'a1 exp **)

  let rec substitute n v x = match x with
  | E_aux (aux, annot0) ->
    (match aux with
     | E_block xs -> E_aux ((E_block (map (substitute n v) xs)), annot0)
     | E_id m ->
       if id_eqb n m
       then E_aux ((E_internal_value v), annot0)
       else E_aux ((E_id m), annot0)
     | E_lit _ -> E_aux (aux, annot0)
     | E_typ (typ0, x0) -> E_aux ((E_typ (typ0, (substitute n v x0))), annot0)
     | E_app (f, args) ->
       E_aux ((E_app (f, (map (substitute n v) args))), annot0)
     | E_tuple xs -> E_aux ((E_tuple (map (substitute n v) xs)), annot0)
     | E_if (i, t0, e) ->
       E_aux ((E_if ((substitute n v i), (substitute n v t0),
         (substitute n v e))), annot0)
     | E_loop (loop_kind, measure, cond, body) ->
       E_aux ((E_loop (loop_kind, measure, (substitute n v cond),
         (substitute n v body))), annot0)
     | E_for (loop_var, from, to0, amount, ord, body) ->
       if id_eqb n loop_var
       then E_aux ((E_for (loop_var, (substitute n v from),
              (substitute n v to0), (substitute n v amount), ord, body)),
              annot0)
       else E_aux ((E_for (loop_var, (substitute n v from),
              (substitute n v to0), (substitute n v amount), ord,
              (substitute n v body))), annot0)
     | E_vector xs -> E_aux ((E_vector (map (substitute n v) xs)), annot0)
     | E_vector_append (x0, y) ->
       E_aux ((E_vector_append ((substitute n v x0), (substitute n v y))),
         annot0)
     | E_list xs -> E_aux ((E_list (map (substitute n v) xs)), annot0)
     | E_cons (x0, xs) ->
       E_aux ((E_cons ((substitute n v x0), (substitute n v xs))), annot0)
     | E_struct (struct_name, fields) ->
       E_aux ((E_struct (struct_name,
         (map (fun f ->
           let FE_aux (f0, fe_annot) = f in
           let FE_fexp (name, x0) = f0 in
           FE_aux ((FE_fexp (name, (substitute n v x0))), fe_annot)) fields))),
         annot0)
     | E_struct_update (x0, fields) ->
       E_aux ((E_struct_update ((substitute n v x0),
         (map (fun f ->
           let FE_aux (f0, fe_annot) = f in
           let FE_fexp (name, y) = f0 in
           FE_aux ((FE_fexp (name, (substitute n v y))), fe_annot)) fields))),
         annot0)
     | E_field (x0, f) -> E_aux ((E_field ((substitute n v x0), f)), annot0)
     | E_match (head_exp, arms) ->
       E_aux ((E_match ((substitute n v head_exp),
         (map (substitute_arm n v) arms))), annot0)
     | E_let (pat0, y, body) ->
       if binds_id n pat0
       then E_aux ((E_let (pat0, (substitute n v y), body)), annot0)
       else E_aux ((E_let (pat0, (substitute n v y), (substitute n v body))),
              annot0)
     | E_assign (l, x0) ->
       E_aux ((E_assign ((substitute_lexp n v l), (substitute n v x0))),
         annot0)
     | E_return x0 -> E_aux ((E_return (substitute n v x0)), annot0)
     | E_throw exn -> E_aux ((E_throw (substitute n v exn)), annot0)
     | E_try (head_exp, arms) ->
       E_aux ((E_try ((substitute n v head_exp),
         (map (substitute_arm n v) arms))), annot0)
     | E_assert (x0, msg) ->
       E_aux ((E_assert ((substitute n v x0), (substitute n v msg))), annot0)
     | E_var (l, x0, body) ->
       E_aux ((E_var ((substitute_lexp n v l), (substitute n v x0),
         (substitute n v body))), annot0)
     | _ -> x)

  (** val substitute_arm : id -> value -> 'a1 pexp -> 'a1 pexp **)

  and substitute_arm n v = function
  | Pat_aux (aux, annot0) ->
    (match aux with
     | Pat_exp (pat0, body) ->
       if binds_id n pat0
       then Pat_aux ((Pat_exp (pat0, body)), annot0)
       else Pat_aux ((Pat_exp (pat0, (substitute n v body))), annot0)
     | Pat_when (pat0, guard, body) ->
       if binds_id n pat0
       then Pat_aux ((Pat_when (pat0, guard, body)), annot0)
       else Pat_aux ((Pat_when (pat0, (substitute n v guard),
              (substitute n v body))), annot0))

  (** val substitute_lexp : id -> value -> 'a1 lexp -> 'a1 lexp **)

  and substitute_lexp n v l = match l with
  | LE_aux (aux, annot0) ->
    (match aux with
     | LE_deref x -> LE_aux ((LE_deref (substitute n v x)), annot0)
     | LE_tuple lxs ->
       LE_aux ((LE_tuple (map (substitute_lexp n v) lxs)), annot0)
     | LE_vector_concat lxs ->
       LE_aux ((LE_vector_concat (map (substitute_lexp n v) lxs)), annot0)
     | LE_vector (lx, x) ->
       LE_aux ((LE_vector ((substitute_lexp n v lx), (substitute n v x))),
         annot0)
     | LE_vector_range (lx, x, y) ->
       LE_aux ((LE_vector_range ((substitute_lexp n v lx),
         (substitute n v x), (substitute n v y))), annot0)
     | LE_field (lx, f) ->
       LE_aux ((LE_field ((substitute_lexp n v lx), f)), annot0)
     | _ -> l)

  (** val bv_concat : Parse_ast.l -> value list -> bit list Monad.t **)

  let rec bv_concat l = function
  | [] -> Monad.pure []
  | v :: rest ->
    (match v with
     | V_bitvector bs ->
       Monad.bind (bv_concat l rest) (fun rest' -> Monad.pure (app bs rest'))
     | _ -> Monad.Runtime_type_error l)

  (** val lookup_field :
      Parse_ast.l -> id -> (id * value) list -> value Monad.t **)

  let rec lookup_field l name = function
  | [] -> Monad.Runtime_type_error l
  | p :: fields0 ->
    let (name', v) = p in
    if id_eqb name name' then Monad.pure v else lookup_field l name fields0

  (** val destructuring_assignment :
      Tannot.t annot -> destructure -> value -> unit Monad.t **)

  let rec destructuring_assignment annot0 d v =
    match d with
    | DL_app (_, _) -> Monad.Runtime_type_error (fst annot0)
    | DL_tuple ds ->
      (match v with
       | V_tuple vs ->
         if Nat.eqb (length ds) (length vs)
         then let (assignment, _) =
                fold_left (fun acc d0 ->
                  let (prev, y) = acc in
                  (match y with
                   | [] -> (prev, [])
                   | v0 :: vs0 ->
                     ((Monad.bind prev (fun _ ->
                        destructuring_assignment annot0 d0 v0)),
                       vs0)))
                  ds ((Monad.pure ()), vs)
              in
              assignment
         else Monad.Runtime_type_error (fst annot0)
       | _ -> Monad.Runtime_type_error (fst annot0))
    | DL_vector_concat ds ->
      (match v with
       | V_bitvector bs ->
         let (assignment, _) =
           fold_left (fun acc d0 ->
             let (s, d1) = d0 in
             (match s with
              | Types.No_split ->
                ((Monad.Runtime_type_error (fst annot0)), [])
              | Types.Split s0 ->
                let (prev, bs0) = acc in
                (match bs0 with
                 | [] -> (prev, [])
                 | _ :: _ ->
                   let (bs_take, bs_drop) = take_drop s0 bs0 in
                   ((Monad.bind prev (fun _ ->
                      destructuring_assignment annot0 d1 (V_bitvector bs_take))),
                   bs_drop))))
             ds ((Monad.pure ()), bs)
         in
         assignment
       | V_vector vs ->
         let (assignment, _) =
           fold_left (fun acc d0 ->
             let (s, d1) = d0 in
             (match s with
              | Types.No_split ->
                ((Monad.Runtime_type_error (fst annot0)), [])
              | Types.Split s0 ->
                let (prev, vs0) = acc in
                (match vs0 with
                 | [] -> (prev, [])
                 | _ :: _ ->
                   let (vs_take, vs_drop) = take_drop s0 vs0 in
                   ((Monad.bind prev (fun _ ->
                      destructuring_assignment annot0 d1 (V_vector vs_take))),
                   vs_drop))))
             ds ((Monad.pure ()), vs)
         in
         assignment
       | _ -> Monad.Runtime_type_error (fst annot0))
    | DL_place p -> Monad.Write_var (p, v, (fun _ -> Monad.pure ()))

  (** val lexp_to_destructure : Tannot.t lexp -> destructure Monad.t **)

  let rec lexp_to_destructure = function
  | LE_aux (aux, annot0) ->
    (match aux with
     | LE_id var ->
       (match Tannot.get_id_type (snd annot0) var with
        | Types.Local_variable ->
          Monad.pure (DL_place (PL_id (var, Var_local)))
        | Types.Global_register ->
          Monad.pure (DL_place (PL_id (var, Var_register)))
        | Types.Enum_member -> Monad.Runtime_type_error (fst annot0))
     | LE_deref x ->
       let E_aux (e, _) = x in
       (match e with
        | E_internal_value v ->
          (match v with
           | V_ref r -> Monad.pure (DL_place (PL_register r))
           | _ -> Monad.Runtime_type_error (fst annot0))
        | _ -> Monad.Runtime_type_error (fst annot0))
     | LE_app (name, args) ->
       let evaluated0 = all_evaluated args in
       Monad.pure (DL_app (name, evaluated0))
     | LE_typ (_, var) ->
       (match Tannot.get_id_type (snd annot0) var with
        | Types.Local_variable ->
          Monad.pure (DL_place (PL_id (var, Var_local)))
        | Types.Global_register ->
          Monad.pure (DL_place (PL_id (var, Var_register)))
        | Types.Enum_member -> Monad.Runtime_type_error (fst annot0))
     | LE_tuple ls ->
       Monad.bind (Monad.sequence (map lexp_to_destructure ls)) (fun ds ->
         Monad.pure (DL_tuple ds))
     | LE_vector_concat ls ->
       Monad.bind
         (Monad.sequence
           (map (fun l0 ->
             let LE_aux (_, annot1) = l0 in
             Monad.bind (lexp_to_destructure l0) (fun d ->
               Monad.pure ((Tannot.get_split (snd annot1)), d)))
             ls))
         (fun ds -> Monad.pure (DL_vector_concat ds))
     | LE_vector (l0, n) ->
       Monad.bind
         (Monad.bind (lexp_to_destructure l0) (coerce_place (fst annot0)))
         (fun p ->
         let E_aux (e, _) = n in
         (match e with
          | E_internal_value v ->
            (match v with
             | V_int n0 -> Monad.pure (DL_place (PL_vector (p, n0)))
             | _ -> Monad.Runtime_type_error (fst annot0))
          | _ -> Monad.Runtime_type_error (fst annot0)))
     | LE_vector_range (l0, n, m) ->
       Monad.bind
         (Monad.bind (lexp_to_destructure l0) (coerce_place (fst annot0)))
         (fun p ->
         let E_aux (e1, _) = n in
         (match e1 with
          | E_internal_value v ->
            (match v with
             | V_int n0 ->
               let E_aux (e2, _) = m in
               (match e2 with
                | E_internal_value v0 ->
                  (match v0 with
                   | V_int m0 ->
                     Monad.pure (DL_place (PL_vector_range (p, n0, m0)))
                   | _ -> Monad.Runtime_type_error (fst annot0))
                | _ -> Monad.Runtime_type_error (fst annot0))
             | _ -> Monad.Runtime_type_error (fst annot0))
          | _ -> Monad.Runtime_type_error (fst annot0)))
     | LE_field (l0, f) ->
       Monad.bind
         (Monad.bind (lexp_to_destructure l0) (coerce_place (fst annot0)))
         (fun p -> Monad.pure (DL_place (PL_field (p, f)))))

  (** val update_field :
      id -> value -> (id * value) list -> (id * value) list **)

  let rec update_field name v = function
  | [] -> []
  | p :: rest ->
    let (name', old_v) = p in
    if id_eqb name name'
    then (name, v) :: rest
    else (name', old_v) :: (update_field name v rest)

  (** val step : Tannot.t exp -> Tannot.t exp Monad.t **)

  let step =
    coq_Fix_sub (fun recarg step' ->
      let step0 = fun orig_exp -> step' (Coq_exist orig_exp) in
      let E_aux (aux, annot0) = recarg in
      let wrap = fun e_aux' -> Monad.pure (E_aux (e_aux', annot0)) in
      (match aux with
       | E_block xs ->
         (match xs with
          | [] -> wrap (E_internal_value V_unit)
          | x :: xs0 ->
            let E_aux (e, annot1) = x in
            (match e with
             | E_block ys ->
               (match xs0 with
                | [] -> wrap (E_block ys)
                | e0 :: l ->
                  let x0 = E_aux ((E_block ys), annot1) in
                  let xs1 = e0 :: l in
                  if is_value x0
                  then wrap (E_block xs1)
                  else Monad.bind (step0 x0) (fun x' ->
                         wrap (E_block (x' :: xs1))))
             | E_id i ->
               let x0 = E_aux ((E_id i), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_lit l ->
               let x0 = E_aux ((E_lit l), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_typ (t0, e0) ->
               let x0 = E_aux ((E_typ (t0, e0)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_app (i, l) ->
               let x0 = E_aux ((E_app (i, l)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_tuple l ->
               let x0 = E_aux ((E_tuple l), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_if (e0, e1, e2) ->
               let x0 = E_aux ((E_if (e0, e1, e2)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_loop (l, i, e0, e1) ->
               let x0 = E_aux ((E_loop (l, i, e0, e1)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_for (i, e0, e1, e2, o, e3) ->
               let x0 = E_aux ((E_for (i, e0, e1, e2, o, e3)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_vector l ->
               let x0 = E_aux ((E_vector l), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_vector_append (e0, e1) ->
               let x0 = E_aux ((E_vector_append (e0, e1)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_list l ->
               let x0 = E_aux ((E_list l), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_cons (e0, e1) ->
               let x0 = E_aux ((E_cons (e0, e1)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_struct (s, l) ->
               let x0 = E_aux ((E_struct (s, l)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_struct_update (e0, l) ->
               let x0 = E_aux ((E_struct_update (e0, l)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_field (e0, i) ->
               let x0 = E_aux ((E_field (e0, i)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_match (e0, l) ->
               let x0 = E_aux ((E_match (e0, l)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_let (p, e0, e1) ->
               let x0 = E_aux ((E_let (p, e0, e1)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_assign (l, e0) ->
               let x0 = E_aux ((E_assign (l, e0)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_sizeof n ->
               let x0 = E_aux ((E_sizeof n), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_return e0 ->
               let x0 = E_aux ((E_return e0), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_exit e0 ->
               let x0 = E_aux ((E_exit e0), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_config l ->
               let x0 = E_aux ((E_config l), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_ref i ->
               let x0 = E_aux ((E_ref i), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_throw e0 ->
               let x0 = E_aux ((E_throw e0), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_try (e0, l) ->
               let x0 = E_aux ((E_try (e0, l)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_assert (e0, e1) ->
               let x0 = E_aux ((E_assert (e0, e1)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_var (l, e0, e1) ->
               let x0 = E_aux ((E_var (l, e0, e1)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_undef ->
               let x0 = E_aux (E_undef, annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_internal_plet (p, e0, e1) ->
               let x0 = E_aux ((E_internal_plet (p, e0, e1)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_internal_return e0 ->
               let x0 = E_aux ((E_internal_return e0), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_internal_value v ->
               (match xs0 with
                | [] -> wrap (E_internal_value v)
                | e0 :: l ->
                  let x0 = E_aux ((E_internal_value v), annot1) in
                  let xs1 = e0 :: l in
                  if is_value x0
                  then wrap (E_block xs1)
                  else Monad.bind (step0 x0) (fun x' ->
                         wrap (E_block (x' :: xs1))))
             | E_internal_assume (n, e0) ->
               let x0 = E_aux ((E_internal_assume (n, e0)), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))
             | E_constraint n ->
               let x0 = E_aux ((E_constraint n), annot1) in
               if is_value x0
               then wrap (E_block xs0)
               else Monad.bind (step0 x0) (fun x' ->
                      wrap (E_block (x' :: xs0)))))
       | E_id id0 ->
         let filtered_var = Tannot.get_id_type (snd annot0) id0 in
         (match filtered_var with
          | Types.Local_variable ->
            Monad.Read_var ((PL_id (id0, Var_local)), (fun v ->
              wrap (E_internal_value v)))
          | Types.Global_register ->
            Monad.Read_var ((PL_id (id0, Var_register)), (fun v ->
              wrap (E_internal_value v)))
          | Types.Enum_member -> wrap (E_internal_value (V_member id0)))
       | E_lit lit -> wrap (E_internal_value (value_of_lit lit))
       | E_typ (_, x) -> step0 x
       | E_app (id0, args) ->
         let Id_aux (i, _) = id0 in
         (match i with
          | And_bool ->
            (match args with
             | [] -> Monad.Runtime_type_error (fst annot0)
             | lhs :: l ->
               (match l with
                | [] -> Monad.Runtime_type_error (fst annot0)
                | rhs :: l0 ->
                  (match l0 with
                   | [] ->
                     Monad.bind (get_bool lhs) (fun b ->
                       match b with
                       | Evaluated b0 ->
                         if b0
                         then Monad.pure rhs
                         else wrap (E_internal_value (V_bool false))
                       | Unevaluated ->
                         Monad.bind (step0 lhs) (fun lhs' ->
                           wrap (E_app (id0, (lhs' :: (rhs :: []))))))
                   | _ :: _ -> Monad.Runtime_type_error (fst annot0))))
          | Or_bool ->
            (match args with
             | [] -> Monad.Runtime_type_error (fst annot0)
             | lhs :: l ->
               (match l with
                | [] -> Monad.Runtime_type_error (fst annot0)
                | rhs :: l0 ->
                  (match l0 with
                   | [] ->
                     Monad.bind (get_bool lhs) (fun b ->
                       match b with
                       | Evaluated b0 ->
                         if b0
                         then wrap (E_internal_value (V_bool true))
                         else Monad.pure rhs
                       | Unevaluated ->
                         Monad.bind (step0 lhs) (fun lhs' ->
                           wrap (E_app (id0, (lhs' :: (rhs :: []))))))
                   | _ :: _ -> Monad.Runtime_type_error (fst annot0))))
          | _ ->
            let filtered_var = left_to_right args in
            let (evaluated0, unevaluated) = filtered_var in
            (match unevaluated with
             | [] ->
               Monad.bind (Monad.Call (id0, (all_evaluated evaluated0),
                 Monad.pure)) (fun r ->
                 match r with
                 | Return_ok v -> wrap (E_internal_value v)
                 | Return_exception exn ->
                   wrap (E_throw (E_aux ((E_internal_value exn), annot0))))
             | u :: us ->
               Monad.bind (step0 u) (fun u' ->
                 wrap (E_app (id0, (app evaluated0 (u' :: us)))))))
       | E_tuple xs ->
         let filtered_var = left_to_right xs in
         let (evaluated0, unevaluated) = filtered_var in
         (match unevaluated with
          | [] -> wrap (E_internal_value (V_tuple (all_evaluated evaluated0)))
          | x :: xs0 ->
            Monad.bind (step0 x) (fun x' ->
              wrap (E_tuple (app evaluated0 (x' :: xs0)))))
       | E_if (i, t0, e) ->
         Monad.bind (get_bool i) (fun b ->
           match b with
           | Evaluated b0 -> if b0 then Monad.pure t0 else Monad.pure e
           | Unevaluated ->
             Monad.bind (step0 i) (fun i' -> wrap (E_if (i', t0, e))))
       | E_loop (l, _, cond, body) ->
         (match l with
          | While ->
            wrap (E_if (cond, (E_aux ((E_block (body :: (recarg :: []))),
              annot0)), (E_aux ((E_internal_value V_unit), annot0))))
          | Until ->
            wrap (E_block (body :: ((E_aux ((E_if (cond, (E_aux
              ((E_internal_value V_unit), annot0)), recarg)),
              annot0)) :: []))))
       | E_for (loop_var, from, to0, amount, ord, body) ->
         let filtered_var = left_to_right3 from to0 amount in
         (match filtered_var with
          | LTR3_0 (_, _, _) ->
            Monad.bind (step0 from) (fun from' ->
              wrap (E_for (loop_var, from', to0, amount, ord, body)))
          | LTR3_1 (_, _, _) ->
            Monad.bind (step0 to0) (fun to' ->
              wrap (E_for (loop_var, from, to', amount, ord, body)))
          | LTR3_2 (_, _, _) ->
            Monad.bind (step0 amount) (fun amount' ->
              wrap (E_for (loop_var, from, to0, amount', ord, body)))
          | LTR3_3 (v_from, v_to, v_amount) ->
            let Ord_aux (o, _) = ord in
            (match o with
             | Ord_inc ->
               Monad.bind
                 (Monad.lift_option (fst annot0) (Primops.gt_int v_from v_to))
                 (fun cmp ->
                 match cmp with
                 | V_bool b ->
                   if b
                   then wrap (E_internal_value V_unit)
                   else Monad.bind
                          (Monad.lift_option (fst annot0)
                            (Primops.add_int v_from v_amount))
                          (fun next ->
                          wrap (E_block
                            ((substitute loop_var v_from body) :: ((E_aux
                            ((E_for (loop_var, (E_aux ((E_internal_value
                            next), annot0)), to0, amount, ord, body)),
                            annot0)) :: []))))
                 | _ -> Monad.Runtime_type_error (fst annot0))
             | Ord_dec ->
               Monad.bind
                 (Monad.lift_option (fst annot0) (Primops.lt_int v_from v_to))
                 (fun cmp ->
                 match cmp with
                 | V_bool b ->
                   if b
                   then wrap (E_internal_value V_unit)
                   else Monad.bind
                          (Monad.lift_option (fst annot0)
                            (Primops.sub_int v_from v_amount))
                          (fun next ->
                          wrap (E_block
                            ((substitute loop_var v_from body) :: ((E_aux
                            ((E_for (loop_var, (E_aux ((E_internal_value
                            next), annot0)), to0, amount, ord, body)),
                            annot0)) :: []))))
                 | _ -> Monad.Runtime_type_error (fst annot0))))
       | E_vector xs ->
         let filtered_var = left_to_right xs in
         let (evaluated0, unevaluated) = filtered_var in
         (match unevaluated with
          | [] ->
            if Tannot.is_bitvector (snd annot0)
            then Monad.bind
                   (bv_concat (fst annot0) (all_evaluated evaluated0))
                   (fun bits -> wrap (E_internal_value (V_bitvector bits)))
            else wrap (E_internal_value (V_vector (all_evaluated evaluated0)))
          | u :: us ->
            Monad.bind (step0 u) (fun u' ->
              wrap (E_vector (app evaluated0 (u' :: us)))))
       | E_vector_append (_, _) -> Monad.Runtime_type_error (fst annot0)
       | E_list xs ->
         let filtered_var = left_to_right xs in
         let (evaluated0, unevaluated) = filtered_var in
         (match unevaluated with
          | [] -> wrap (E_internal_value (V_list (all_evaluated evaluated0)))
          | u :: us ->
            Monad.bind (step0 u) (fun u' ->
              wrap (E_list (app evaluated0 (u' :: us)))))
       | E_cons (x, xs) ->
         let filtered_var = left_to_right2 x xs in
         (match filtered_var with
          | LTR2_0 (_, _) ->
            Monad.bind (step0 x) (fun x' -> wrap (E_cons (x', xs)))
          | LTR2_1 (_, _) ->
            Monad.bind (step0 xs) (fun xs' -> wrap (E_cons (x, xs')))
          | LTR2_2 (vx, vxs) ->
            (match vxs with
             | V_list elems -> wrap (E_internal_value (V_list (vx :: elems)))
             | _ -> Monad.Runtime_type_error (fst annot0)))
       | E_struct (struct_id, fs) ->
         let filtered_var = left_to_right_fields fs in
         let (evaluated0, unevaluated) = filtered_var in
         (match unevaluated with
          | [] ->
            wrap (E_internal_value (V_record
              (all_evaluated_fields evaluated0)))
          | f :: xs ->
            let FE_aux (f0, annot1) = f in
            let FE_fexp (name, x) = f0 in
            Monad.bind (step0 x) (fun x' ->
              wrap (E_struct (struct_id,
                (app evaluated0 ((FE_aux ((FE_fexp (name, x')),
                  annot1)) :: xs))))))
       | E_struct_update (x, fs) ->
         let E_aux (e, _) = x in
         (match e with
          | E_internal_value wildcard' ->
            (match wildcard' with
             | V_record fields ->
               let filtered_var = left_to_right_fields fs in
               let (evaluated0, unevaluated) = filtered_var in
               (match unevaluated with
                | [] ->
                  let updates = all_evaluated_fields evaluated0 in
                  let fields0 =
                    fold_left (fun fields0 s ->
                      update_field (fst s) (snd s) fields0) updates fields
                  in
                  wrap (E_internal_value (V_record fields0))
                | f :: ys ->
                  let FE_aux (f0, annot1) = f in
                  let FE_fexp (name, y) = f0 in
                  Monad.bind (step0 y) (fun y' ->
                    wrap (E_struct_update (x,
                      (app evaluated0 ((FE_aux ((FE_fexp (name, y')),
                        annot1)) :: ys))))))
             | _ -> Monad.Runtime_type_error (fst annot0))
          | _ ->
            Monad.bind (step0 x) (fun x' -> wrap (E_struct_update (x', fs))))
       | E_field (x, f) ->
         let filtered_var = get_value x in
         (match filtered_var with
          | Evaluated v ->
            (match v with
             | V_record fields ->
               Monad.bind (lookup_field (fst annot0) f fields)
                 (fun v_field -> wrap (E_internal_value v_field))
             | _ -> Monad.Runtime_type_error (fst annot0))
          | Unevaluated ->
            Monad.bind (step0 x) (fun x' -> wrap (E_field (x', f))))
       | E_match (head_exp, arms) ->
         let E_aux (e, _) = head_exp in
         (match e with
          | E_internal_value v ->
            (match arms with
             | [] -> Monad.Match_failure (fst annot0)
             | p :: next_arms ->
               let Pat_aux (p0, pexp_annot) = p in
               (match p0 with
                | Pat_exp (pat0, body) ->
                  let filtered_var = PM.pattern_match pat0 v in
                  (match filtered_var with
                   | Matched arm_substs ->
                     Monad.pure
                       (IdMap.fold substitute (complete_bindings arm_substs)
                         body)
                   | _ -> wrap (E_match (head_exp, next_arms)))
                | Pat_when (pat0, guard, body) ->
                  let filtered_var = PM.pattern_match pat0 v in
                  (match filtered_var with
                   | Matched arm_substs ->
                     let guard0 =
                       IdMap.fold substitute (complete_bindings arm_substs)
                         guard
                     in
                     let E_aux (e0, _) = guard0 in
                     (match e0 with
                      | E_internal_value v_guard ->
                        (match v_guard with
                         | V_bool b ->
                           if b
                           then let filtered_var0 = PM.pattern_match pat0 v in
                                (match filtered_var0 with
                                 | Matched arm_substs0 ->
                                   Monad.pure
                                     (IdMap.fold substitute
                                       (complete_bindings arm_substs0) body)
                                 | _ -> wrap (E_match (head_exp, next_arms)))
                           else wrap (E_match (head_exp, next_arms))
                         | _ -> Monad.Runtime_type_error (fst pexp_annot))
                      | _ ->
                        Monad.bind (step0 guard0) (fun guard' ->
                          wrap (E_match (head_exp, ((Pat_aux ((Pat_when
                            (pat0, guard', body)),
                            pexp_annot)) :: next_arms)))))
                   | _ -> wrap (E_match (head_exp, next_arms)))))
          | _ ->
            Monad.bind (step0 head_exp) (fun head_exp' ->
              wrap (E_match (head_exp', arms))))
       | E_let (pat0, x, body) ->
         let E_aux (e, _) = x in
         (match e with
          | E_internal_value v ->
            let filtered_var = PM.pattern_match pat0 v in
            (match filtered_var with
             | Matched body_substs ->
               Monad.pure
                 (IdMap.fold substitute (complete_bindings body_substs) body)
             | _ -> Monad.Match_failure (fst annot0))
          | _ ->
            Monad.bind (step0 x) (fun x' -> wrap (E_let (pat0, x', body))))
       | E_assign (lx, x) ->
         let subexps = lexp_subexps lx in
         let filtered_var = left_to_right subexps in
         let (evaluated0, unevaluated) = filtered_var in
         (match unevaluated with
          | [] ->
            let filtered_var0 = get_value x in
            (match filtered_var0 with
             | Evaluated v ->
               Monad.bind (lexp_to_destructure lx) (fun d ->
                 Monad.bind (destructuring_assignment annot0 d v) (fun _ ->
                   wrap (E_internal_value V_unit)))
             | Unevaluated ->
               Monad.bind (step0 x) (fun x' -> wrap (E_assign (lx, x'))))
          | u :: us ->
            Monad.bind (step0 u) (fun u' ->
              let filtered_var0 =
                update_lexp_subexps (app evaluated0 (u' :: us)) lx
              in
              let (l', _) = filtered_var0 in wrap (E_assign (l', x))))
       | E_sizeof _ -> Monad.Runtime_type_error (fst annot0)
       | E_return x ->
         let filtered_var = get_value x in
         (match filtered_var with
          | Evaluated v -> Monad.Early_return v
          | Unevaluated -> Monad.bind (step0 x) (fun x' -> wrap (E_return x')))
       | E_exit _ -> Monad.Runtime_type_error (fst annot0)
       | E_config _ -> Monad.Runtime_type_error (fst annot0)
       | E_ref register_name -> wrap (E_internal_value (V_ref register_name))
       | E_throw x ->
         let filtered_var = get_value x in
         (match filtered_var with
          | Evaluated v -> Monad.throw v
          | Unevaluated -> Monad.bind (step0 x) (fun x' -> wrap (E_throw x')))
       | E_try (x, arms) ->
         let E_aux (e, annot1) = x in
         (match e with
          | E_internal_value v ->
            Monad.pure (E_aux ((E_internal_value v), annot1))
          | _ ->
            Monad.bind (Monad.catch (step0 x)) (fun x' ->
              match x' with
              | Monad.Continue x'' -> wrap (E_try (x'', arms))
              | Monad.Caught exn ->
                wrap (E_match ((E_aux ((E_internal_value exn), annot0)),
                  (app arms (Tannot.fallthrough :: []))))))
       | E_assert (x, msg) ->
         Monad.bind (get_bool x) (fun b ->
           match b with
           | Evaluated b0 ->
             Monad.bind (get_string msg) (fun s ->
               match s with
               | Evaluated s0 ->
                 if b0
                 then wrap (E_internal_value V_unit)
                 else Monad.Assertion_failed s0
               | Unevaluated ->
                 Monad.bind (step0 msg) (fun msg' ->
                   wrap (E_assert (x, msg'))))
           | Unevaluated ->
             Monad.bind (step0 x) (fun x' -> wrap (E_assert (x', msg))))
       | E_var (l, x, body) ->
         wrap (E_block ((E_aux ((E_assign (l, x)), annot0)) :: (body :: [])))
       | E_undef ->
         Monad.bind (Monad.get_undefined (Tannot.get_type (snd annot0)))
           (fun u -> wrap (E_internal_value u))
       | E_internal_plet (_, _, _) -> Monad.Runtime_type_error (fst annot0)
       | E_internal_return _ -> Monad.Runtime_type_error (fst annot0)
       | E_internal_value v -> wrap (E_internal_value v)
       | E_internal_assume (_, _) -> Monad.Runtime_type_error (fst annot0)
       | E_constraint _ -> Monad.Runtime_type_error (fst annot0)))
 end
