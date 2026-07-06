open Assignment
open Ast
open Datatypes
open IdUtil
open Lattice
open List0
open ListDef
open OptionUtil
open PatternMatch
open TypeAnnot
open Base

type single_case =
| Field of id
| Internal_assume of n_constraint
| Internal_return
| Throw
| Typ of typ

type pair_case =
| Assert
| Vector_append
| Cons

type list_case =
| List
| Tuple
| Vector
| Bitvector

type match_case =
| Match
| Letbind
| Try
| Internal_plet

type ('v, 'r, 's, 'a) zexp_aux =
| Z_single of ('v, 'r, 's, 'a) zexp * single_case
| Z_return of ('v, 'r, 's, 'a) zexp
| Z_inline of ('v, 'r, 's, 'a) zexp * 'r option
| Z_exit of ('v, 'r, 's, 'a) zexp
| Z_pair_1 of ('v, 'r, 's, 'a) zexp * pair_case * 'a exp
| Z_pair_2 of ('v, 'r, 's, 'a) zexp * pair_case * 'r
| Z_list of ('v, 'r, 's, 'a) zexp * list_case * 'r list * 'a exp list
| Z_app of ('v, 'r, 's, 'a) zexp * id * 'r list * 'a exp list
| Z_block of ('v, 'r, 's, 'a) zexp * 'r list * 'a exp list
| Z_if_cond of ('v, 'r, 's, 'a) zexp * 'a exp * 'a exp
| Z_if_then of ('v, 'r, 's, 'a) zexp * ('s * 'r) * 'a exp
| Z_if_else of ('v, 'r, 's, 'a) zexp * 'r * ('s * 'r)
| Z_match_head of ('v, 'r, 's, 'a) zexp * match_case
   * ((('s * 'a pat) * 'r option) * 'r) list
   * (('a pat * 'a exp option) * 'a exp) list option
| Z_match_arms_guard of ('v, 'r, 's, 'a) zexp * match_case * 'v * ('s * 'r)
   * ((('s * 'a pat) * 'r option) * 'r) list * 'a pat * bool * 'a exp
   * (('a pat * 'a exp option) * 'a exp) list option
| Z_match_arms_body of ('v, 'r, 's, 'a) zexp * match_case * 'v * ('s * 'r)
   * ((('s * 'a pat) * 'r option) * 'r) list * 'a pat * 'r option
   * (('a pat * 'a exp option) * 'a exp) list option
| Z_assign_left of ('v, 'r, 's, 'a) zexp * 'a zlexp * 'r list * 'a exp list
   * 'a exp
| Z_assign_right of ('v, 'r, 's, 'a) zexp * 'a zlexp * 'r list
| Z_var_left of ('v, 'r, 's, 'a) zexp * 'a zlexp * 'r list * 'a exp list
   * 'a exp * 'a exp
| Z_var_right of ('v, 'r, 's, 'a) zexp * 'a zlexp * 'r list * 'a exp
| Z_var_body of ('v, 'r, 's, 'a) zexp * 'a zlexp * 'r list * 'r
| Z_struct of ('v, 'r, 's, 'a) zexp * struct_name * (id * 'r) list * 
   id * 'a fexp list
| Z_struct_update_base of ('v, 'r, 's, 'a) zexp * struct_name * 'a fexp list
| Z_struct_update of ('v, 'r, 's, 'a) zexp * struct_name * 'r
   * (id * 'r) list * id * 'a fexp list
and ('v, 'r, 's, 'a) zexp =
| Z_aux of ('v, 'r, 's, 'a) zexp_aux * 'a annot
| Z_top

(** val unwrap_arm : 'a1 pexp -> ('a1 pat * 'a1 exp option) * 'a1 exp **)

let unwrap_arm = function
| Pat_aux (p, _) ->
  (match p with
   | Pat_exp (pat0, body) -> ((pat0, None), body)
   | Pat_when (pat0, guard, body) -> ((pat0, (Some guard)), body))

module ExpBuilder =
 functor (Tannot:S) ->
 struct
  type t = Tannot.t exp

  (** val mk_app : Tannot.t annot -> id -> t list -> Tannot.t exp **)

  let mk_app ann f xs =
    E_aux ((E_app (f, xs)), ann)

  (** val mk_config : Tannot.t annot -> string list -> Tannot.t exp **)

  let mk_config ann key =
    E_aux ((E_config key), ann)

  (** val mk_id : Tannot.t annot -> id -> Tannot.t exp **)

  let mk_id ann id0 =
    E_aux ((E_id id0), ann)

  (** val mk_block : Tannot.t annot -> t list -> Tannot.t exp **)

  let mk_block ann exps =
    E_aux ((E_block (rev exps)), ann)

  (** val mk_exit : Tannot.t annot -> t -> Tannot.t exp **)

  let mk_exit ann x =
    E_aux ((E_exit x), ann)

  (** val mk_ite : Tannot.t annot -> t -> t -> t -> Tannot.t exp **)

  let mk_ite ann iexp texp eexp =
    E_aux ((E_if (iexp, texp, eexp)), ann)

  (** val mk_list : Tannot.t annot -> list_case -> t list -> Tannot.t exp **)

  let mk_list ann c xs =
    match c with
    | List -> E_aux ((E_list (rev xs)), ann)
    | Tuple -> E_aux ((E_tuple (rev xs)), ann)
    | _ -> E_aux ((E_vector (rev xs)), ann)

  (** val mk_literal : Tannot.t annot -> lit -> Tannot.t exp **)

  let mk_literal ann l0 =
    E_aux ((E_lit l0), ann)

  (** val mk_pexp :
      Tannot.t annot -> ((Tannot.t pat * t option) * t) -> Tannot.t pexp **)

  let mk_pexp ann = function
  | (p, body) ->
    let (pat0, guard_opt) = p in
    (match guard_opt with
     | Some g -> Pat_aux ((Pat_when (pat0, g, body)), ann)
     | None -> Pat_aux ((Pat_exp (pat0, body)), ann))

  (** val mk_match :
      Tannot.t annot -> match_case -> t -> ((Tannot.t pat * t option) * t)
      list -> Tannot.t exp **)

  let mk_match ann c head_exp arms =
    match c with
    | Try -> E_aux ((E_try (head_exp, (map (mk_pexp ann) arms))), ann)
    | Internal_plet ->
      (match arms with
       | [] -> E_aux ((E_match (head_exp, (map (mk_pexp ann) arms))), ann)
       | p :: l0 ->
         let (p0, body) = p in
         let (pat0, o) = p0 in
         (match o with
          | Some _ ->
            E_aux ((E_match (head_exp, (map (mk_pexp ann) arms))), ann)
          | None ->
            (match l0 with
             | [] -> E_aux ((E_internal_plet (pat0, head_exp, body)), ann)
             | _ :: _ ->
               E_aux ((E_match (head_exp, (map (mk_pexp ann) arms))), ann))))
    | _ ->
      (match arms with
       | [] -> E_aux ((E_match (head_exp, (map (mk_pexp ann) arms))), ann)
       | p :: l0 ->
         let (p0, body) = p in
         let (pat0, o) = p0 in
         (match o with
          | Some _ ->
            E_aux ((E_match (head_exp, (map (mk_pexp ann) arms))), ann)
          | None ->
            (match l0 with
             | [] -> E_aux ((E_let (pat0, head_exp, body)), ann)
             | _ :: _ ->
               E_aux ((E_match (head_exp, (map (mk_pexp ann) arms))), ann))))

  (** val mk_pair : Tannot.t annot -> pair_case -> t -> t -> Tannot.t exp **)

  let mk_pair ann c x y =
    match c with
    | Assert -> E_aux ((E_assert (x, y)), ann)
    | Vector_append -> E_aux ((E_vector_append (x, y)), ann)
    | Cons -> E_aux ((E_cons (x, y)), ann)

  (** val mk_ref : Tannot.t annot -> id -> Tannot.t exp **)

  let mk_ref ann reg =
    E_aux ((E_ref reg), ann)

  (** val mk_return : Tannot.t annot -> t -> Tannot.t exp **)

  let mk_return ann x =
    E_aux ((E_return x), ann)

  (** val mk_inline : Tannot.t annot -> t -> Tannot.t exp **)

  let mk_inline ann x =
    let (loc, tannot) = ann in
    E_aux ((E_block (x :: [])), (loc, (Tannot.annotate loc "inline" tannot)))

  (** val mk_single : Tannot.t annot -> single_case -> t -> Tannot.t exp **)

  let mk_single ann c x =
    match c with
    | Field fld -> E_aux ((E_field (x, fld)), ann)
    | Internal_assume nc -> E_aux ((E_internal_assume (nc, x)), ann)
    | Internal_return -> E_aux ((E_return x), ann)
    | Throw -> E_aux ((E_throw x), ann)
    | Typ typ0 -> E_aux ((E_typ (typ0, x)), ann)

  (** val mk_var :
      Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t -> Tannot.t exp **)

  let mk_var ann l0 args x body =
    let (o, _) = update_zlexp_subexps args l0 in
    (match o with
     | Some l' -> E_aux ((E_var (l', x, body)), ann)
     | None -> E_aux (E_undef, ann))

  (** val mk_assign :
      Tannot.t annot -> Tannot.t zlexp -> t list -> t -> Tannot.t exp **)

  let mk_assign ann l0 args x =
    let (o, _) = update_zlexp_subexps args l0 in
    (match o with
     | Some l' -> E_aux ((E_assign (l', x)), ann)
     | None -> E_aux (E_undef, ann))

  (** val mk_undef : Tannot.t annot -> Tannot.t exp **)

  let mk_undef ann =
    E_aux (E_undef, ann)

  (** val mk_fexp : Tannot.t annot -> (id * t) -> Tannot.t fexp **)

  let mk_fexp ann = function
  | (k, v) -> FE_aux ((FE_fexp (k, v)), ann)

  (** val mk_struct : Tannot.t annot -> struct_name -> (id * t) list -> t **)

  let mk_struct ann sn fs =
    E_aux ((E_struct (sn, (map (mk_fexp ann) (rev fs)))), ann)

  (** val mk_struct_update :
      Tannot.t annot -> struct_name -> t -> (id * t) list -> t **)

  let mk_struct_update ann _ base fs =
    E_aux ((E_struct_update (base, (map (mk_fexp ann) (rev fs)))), ann)
 end

module Residual =
 functor (Tannot:S) ->
 functor (B:sig
  type t

  val mk_app : Tannot.t annot -> id -> t list -> t

  val mk_config : Tannot.t annot -> string list -> t

  val mk_id : Tannot.t annot -> id -> t

  val mk_block : Tannot.t annot -> t list -> t

  val mk_exit : Tannot.t annot -> t -> t

  val mk_ite : Tannot.t annot -> t -> t -> t -> t

  val mk_list : Tannot.t annot -> list_case -> t list -> t

  val mk_literal : Tannot.t annot -> lit -> t

  val mk_match :
    Tannot.t annot -> match_case -> t -> ((Tannot.t pat * t option) * t) list
    -> t

  val mk_pair : Tannot.t annot -> pair_case -> t -> t -> t

  val mk_ref : Tannot.t annot -> id -> t

  val mk_return : Tannot.t annot -> t -> t

  val mk_inline : Tannot.t annot -> t -> t

  val mk_single : Tannot.t annot -> single_case -> t -> t

  val mk_var : Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t -> t

  val mk_assign : Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t

  val mk_undef : Tannot.t annot -> t

  val mk_struct : Tannot.t annot -> struct_name -> (id * t) list -> t

  val mk_struct_update :
    Tannot.t annot -> struct_name -> t -> (id * t) list -> t
 end) ->
 functor (L:SAIL_VALUE) ->
 struct
  module Matching = L.Matching(Tannot)

  module Destructure = Assignment.Typed(Tannot)

  type value = { this : L.t option; exn : L.t option; eff : bool }

  (** val this : value -> L.t option **)

  let this v =
    v.this

  (** val exn : value -> L.t option **)

  let exn v =
    v.exn

  (** val eff : value -> bool **)

  let eff v =
    v.eff

  type state = { local_lets : L.t IdMap.t list;
                 local_vars : L.t IdMap.t list; toplevel_lets : L.t IdMap.t;
                 registers : L.t IdMap.t }

  (** val local_lets : state -> L.t IdMap.t list **)

  let local_lets s =
    s.local_lets

  (** val local_vars : state -> L.t IdMap.t list **)

  let local_vars s =
    s.local_vars

  (** val toplevel_lets : state -> L.t IdMap.t **)

  let toplevel_lets s =
    s.toplevel_lets

  (** val registers : state -> L.t IdMap.t **)

  let registers s =
    s.registers

  type t = value * B.t

  (** val is_unit : value -> bool **)

  let is_unit v =
    (&&) ((&&) (option_is L.is_unit v.this) (is_none v.exn)) (negb v.eff)

  (** val is_true : value -> bool **)

  let is_true v =
    (&&) (option_is L.is_true v.this) (is_none v.exn)

  (** val is_false : value -> bool **)

  let is_false v =
    (&&) (option_is L.is_false v.this) (is_none v.exn)

  (** val bounded_join : L.t option -> L.t option -> L.t option **)

  let bounded_join o_UU2081_ o_UU2082_ =
    option_join L.join o_UU2081_ o_UU2082_

  (** val mk_block : Tannot.t annot -> t list -> value * B.t **)

  let mk_block ann rs = match rs with
  | [] ->
    ({ this = (Some (L.mk_unit ())); exn = None; eff = false },
      (B.mk_block ann []))
  | r :: _ ->
    ({ this = (fst r).this; exn =
      (fold_left bounded_join (map (fun r0 -> (fst r0).exn) rs) None); eff =
      (fold_left (||) (map (fun r0 -> (fst r0).eff) rs) false) },
      (B.mk_block ann (map snd rs)))

  (** val mk_exit : Tannot.t annot -> t -> value * B.t **)

  let mk_exit ann r =
    ({ this = None; exn = (fst r).exn; eff = true }, (B.mk_exit ann (snd r)))

  (** val mk_ite : Tannot.t annot -> t -> t -> t -> value * B.t **)

  let mk_ite ann ir tr er =
    match (fst ir).this with
    | Some _ ->
      ({ this = (bounded_join (fst tr).this (fst er).this); exn =
        (bounded_join (bounded_join (fst ir).exn (fst tr).exn) (fst er).exn);
        eff = ((||) ((||) (fst ir).eff (fst tr).eff) (fst er).eff) },
        (B.mk_ite ann (snd ir) (snd tr) (snd er)))
    | None ->
      ({ this = None; exn = (fst ir).exn; eff = (fst ir).eff }, (snd ir))

  (** val mk_list : Tannot.t annot -> list_case -> t list -> value * B.t **)

  let mk_list ann c rs =
    let ctor =
      match c with
      | List -> L.mk_list
      | Tuple -> L.mk_tuple
      | Vector -> L.mk_vector
      | Bitvector -> L.mk_bitvector
    in
    ({ this =
    (option_map ctor (option_all (rev (map (fun r -> (fst r).this) rs))));
    exn = (fold_left bounded_join (map (fun r -> (fst r).exn) rs) None);
    eff = (fold_left (||) (map (fun r -> (fst r).eff) rs) false) },
    (B.mk_list ann c (map snd rs)))

  (** val mk_literal : Tannot.t annot -> lit -> value * B.t **)

  let mk_literal ann l0 =
    ({ this = (Some (L.of_lit l0)); exn = None; eff = false },
      (B.mk_literal ann l0))

  (** val build_arm :
      (((state * Tannot.t pat) * t option) * t) -> (Tannot.t pat * B.t
      option) * B.t **)

  let build_arm = function
  | (p, body) ->
    let (p0, guard_opt) = p in
    let (_, pat0) = p0 in ((pat0, (option_map snd guard_opt)), (snd body))

  (** val exn_arm :
      (((state * Tannot.t pat) * t option) * t) -> L.t option **)

  let exn_arm = function
  | (p, body) ->
    let (_, guard_opt) = p in
    bounded_join (option_bind guard_opt (fun r -> (fst r).exn)) (fst body).exn

  (** val this_arm :
      (((state * Tannot.t pat) * t option) * t) -> L.t option **)

  let this_arm = function
  | (_, body) -> (fst body).this

  (** val eff_arm : (((state * Tannot.t pat) * t option) * t) -> bool **)

  let eff_arm = function
  | (p, body) ->
    let (_, guard_opt) = p in
    (||) (match guard_opt with
          | Some g -> (fst g).eff
          | None -> false)
      (fst body).eff

  (** val mk_match :
      Tannot.t annot -> match_case -> bool -> t -> (((state * Tannot.t
      pat) * t option) * t) list -> t **)

  let mk_match ann c guaranteed_match head arms =
    let b = B.mk_match ann c (snd head) (map build_arm arms) in
    (match c with
     | Try ->
       let p =
         if is_none (fst head).exn
         then { this = (fst head).this; exn = None; eff = (fst head).eff }
         else { this =
                (fold_left (fun acc arm -> bounded_join acc (this_arm arm))
                  arms (fst head).this);
                exn =
                (if guaranteed_match
                 then fold_left (fun acc arm ->
                        bounded_join acc (exn_arm arm)) arms None
                 else fold_left (fun acc arm ->
                        bounded_join acc (exn_arm arm)) arms (fst head).exn);
                eff =
                (fold_left (fun acc arm -> (||) acc (eff_arm arm)) arms
                  (fst head).eff) }
       in
       (p, b)
     | _ ->
       ({ this =
         (fold_left (fun acc arm -> bounded_join acc (this_arm arm)) arms
           None);
         exn =
         (fold_left (fun acc arm -> bounded_join acc (exn_arm arm)) arms
           (fst head).exn);
         eff =
         (fold_left (fun acc arm -> (||) acc (eff_arm arm)) arms
           (fst head).eff) },
         b))

  (** val mk_pair : Tannot.t annot -> pair_case -> t -> t -> value * B.t **)

  let mk_pair ann c x y =
    let b = B.mk_pair ann c (snd x) (snd y) in
    (match c with
     | Assert ->
       ({ this = (Some (L.mk_unit ())); exn =
         (bounded_join (fst x).exn (fst y).exn); eff = true }, b)
     | Vector_append -> ({ this = None; exn = None; eff = false }, b)
     | Cons ->
       let this' =
         match (fst x).this with
         | Some h ->
           (match (fst y).this with
            | Some t0 -> Some (L.cons h t0)
            | None -> None)
         | None -> None
       in
       ({ this = this'; exn = None; eff = false }, b))

  (** val mk_ref : Tannot.t annot -> id -> value * B.t **)

  let mk_ref ann id0 =
    ({ this = (Some (L.mk_ref (Aux.unwrap id0))); exn = None; eff = false },
      (B.mk_ref ann id0))

  (** val mk_return : Tannot.t annot -> t -> value * B.t **)

  let mk_return ann r =
    ({ this = None; exn = (fst r).exn; eff = true },
      (B.mk_return ann (snd r)))

  (** val join_returns : t option -> t -> t **)

  let join_returns acc ret =
    match acc with
    | Some a ->
      ({ this = (bounded_join (fst a).this (fst ret).this); exn =
        (bounded_join (fst a).exn (fst ret).exn); eff =
        ((||) (fst a).eff (fst ret).eff) }, (snd ret))
    | None -> ret

  (** val mk_inline : Tannot.t annot -> t option -> t -> value * B.t **)

  let mk_inline ann acc r =
    let this' =
      match acc with
      | Some a -> bounded_join (fst a).this (fst r).this
      | None -> (fst r).this
    in
    ({ this = this'; exn = (fst r).exn; eff = false },
    (B.mk_inline ann (snd r)))

  (** val mk_single : Tannot.t annot -> single_case -> t -> value * B.t **)

  let mk_single ann c r =
    let b = B.mk_single ann c (snd r) in
    (match c with
     | Field fld ->
       (match (fst r).this with
        | Some rec0 ->
          ({ this = (Some (L.lookup_field rec0 (Aux.unwrap fld))); exn =
            (fst r).exn; eff = (fst r).eff }, b)
        | None -> ({ this = None; exn = (fst r).exn; eff = (fst r).eff }, b))
     | Throw ->
       ({ this = None; exn = (bounded_join (fst r).this (fst r).exn); eff =
         false }, b)
     | _ -> ((fst r), b))

  (** val mk_var :
      Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t -> value * B.t **)

  let mk_var ann zl rs exp0 body =
    ((fst body), (B.mk_var ann zl (map snd rs) (snd exp0) (snd body)))

  (** val mk_assign :
      Tannot.t annot -> Tannot.t zlexp -> t list -> t -> value * B.t **)

  let mk_assign ann zl rs exp0 =
    ({ this = (Some (L.mk_unit ())); exn =
      (fold_left bounded_join (map (fun r -> (fst r).exn) rs) (fst exp0).exn);
      eff = true }, (B.mk_assign ann zl (map snd rs) (snd exp0)))

  (** val known_fields : (id * t) list -> (id_aux * L.t) list option **)

  let known_fields rs =
    option_map rev
      (fold_left (fun acc kv ->
        match acc with
        | Some fs ->
          let (k, v) = kv in
          (match (fst v).this with
           | Some x -> Some (((Aux.unwrap k), x) :: fs)
           | None -> None)
        | None -> None) rs (Some []))

  (** val mk_struct : Tannot.t annot -> struct_name -> (id * t) list -> t **)

  let mk_struct ann sn rs =
    ({ this = (option_map L.mk_record (known_fields rs)); exn =
      (fold_left bounded_join (map (fun kv -> (fst (snd kv)).exn) rs) None);
      eff = (fold_left (||) (map (fun kv -> (fst (snd kv)).eff) rs) false) },
      (B.mk_struct ann sn
        (map (fun kv -> let (k, v) = kv in (k, (snd v))) rs)))

  (** val mk_struct_update :
      Tannot.t annot -> struct_name -> t -> (id * t) list -> t **)

  let mk_struct_update ann sn base rs =
    let updated =
      match (fst base).this with
      | Some b ->
        (match known_fields rs with
         | Some fs -> L.update_record b fs
         | None -> None)
      | None -> None
    in
    ({ this = updated; exn =
    (fold_left bounded_join (map (fun kv -> (fst (snd kv)).exn) rs)
      (fst base).exn);
    eff =
    (fold_left (||) (map (fun kv -> (fst (snd kv)).eff) rs) (fst base).eff) },
    (B.mk_struct_update ann sn (snd base)
      (map (fun kv -> let (k, v) = kv in (k, (snd v))) rs)))

  (** val empty : state **)

  let empty =
    { local_lets = (IdMap.empty :: []); local_vars = (IdMap.empty :: []);
      toplevel_lets = IdMap.empty; registers = IdMap.empty }

  (** val join : state -> state -> state **)

  let join _UU03c3__UU2081_ _UU03c3__UU2082_ =
    { local_lets =
      (zip_with (IdMap.map2 bounded_join) _UU03c3__UU2081_.local_lets
        _UU03c3__UU2082_.local_lets);
      local_vars =
      (zip_with (IdMap.map2 bounded_join) _UU03c3__UU2081_.local_vars
        _UU03c3__UU2082_.local_vars);
      toplevel_lets = _UU03c3__UU2081_.toplevel_lets; registers =
      (IdMap.map2 bounded_join _UU03c3__UU2081_.registers
        _UU03c3__UU2082_.registers) }

  (** val from_semilattice : L.t -> value **)

  let from_semilattice v =
    { this = (Some v); exn = None; eff = false }

  (** val pattern_match :
      l -> match_case -> Tannot.t pat -> t -> (Parse_ast.l, L.t match_result)
      sum **)

  let pattern_match l0 c pat0 head_exp =
    let h = match c with
            | Try -> (fst head_exp).exn
            | _ -> (fst head_exp).this
    in
    (match h with
     | Some v -> Coq_inr (Matching.pattern_match pat0 v)
     | None -> (match c with
                | Try -> Coq_inr Unmatched
                | _ -> Coq_inl l0))

  (** val end_match : match_case -> state option -> state list -> state **)

  let end_match _ fallthrough arms =
    let arms0 =
      match fallthrough with
      | Some _UU03c3_ -> _UU03c3_ :: arms
      | None -> arms
    in
    (match arms0 with
     | [] -> empty
     | _UU03c3_ :: rest -> fold_left join rest _UU03c3_)

  (** val push_scope : state -> state **)

  let push_scope _UU03c3_ =
    { local_lets = (IdMap.empty :: _UU03c3_.local_lets); local_vars =
      (IdMap.empty :: _UU03c3_.local_vars); toplevel_lets =
      _UU03c3_.toplevel_lets; registers = _UU03c3_.registers }

  (** val pop_scope : state -> state **)

  let pop_scope _UU03c3_ =
    match _UU03c3_.local_lets with
    | [] -> _UU03c3_
    | _ :: lets' ->
      (match lets' with
       | [] -> _UU03c3_
       | _ :: _ ->
         (match _UU03c3_.local_vars with
          | [] -> _UU03c3_
          | _ :: vars' ->
            (match vars' with
             | [] -> _UU03c3_
             | _ :: _ ->
               { local_lets = lets'; local_vars = vars'; toplevel_lets =
                 _UU03c3_.toplevel_lets; registers = _UU03c3_.registers })))

  (** val lookup_local_let : state -> id -> L.t option **)

  let lookup_local_let _UU03c3_ id0 =
    match _UU03c3_.local_lets with
    | [] -> None
    | top0 :: _ -> IdMap.find id0 top0

  (** val lookup_local_var : state -> id -> L.t option **)

  let lookup_local_var _UU03c3_ id0 =
    match _UU03c3_.local_vars with
    | [] -> None
    | top0 :: _ -> IdMap.find id0 top0

  (** val lookup : Parse_ast.l -> state -> id -> (Parse_ast.l, L.t) sum **)

  let lookup l0 _UU03c3_ id0 =
    match lookup_local_let _UU03c3_ id0 with
    | Some v -> Coq_inr v
    | None ->
      (match lookup_local_var _UU03c3_ id0 with
       | Some v -> Coq_inr v
       | None ->
         (match IdMap.find id0 _UU03c3_.toplevel_lets with
          | Some v -> Coq_inr v
          | None ->
            (match IdMap.find id0 _UU03c3_.registers with
             | Some v -> Coq_inr v
             | None -> Coq_inl l0)))

  (** val bind_arm : L.t IdMap.t -> state -> L.t option IdMap.t * state **)

  let bind_arm _UU03b2_ _UU03c3_ =
    match _UU03c3_.local_lets with
    | [] -> ((IdMap.map (fun _ -> None) _UU03b2_), _UU03c3_)
    | top0 :: rest ->
      let shadow = IdMap.mapi (fun id0 _ -> IdMap.find id0 top0) _UU03b2_ in
      let top' = IdMap.fold IdMap.add _UU03b2_ top0 in
      (shadow, { local_lets = (top' :: rest); local_vars =
      _UU03c3_.local_vars; toplevel_lets = _UU03c3_.toplevel_lets;
      registers = _UU03c3_.registers })

  (** val restore_arm : L.t option IdMap.t -> state -> state **)

  let restore_arm shadow _UU03c3_ =
    match _UU03c3_.local_lets with
    | [] -> _UU03c3_
    | top0 :: rest ->
      let top' =
        IdMap.fold (fun id0 old m ->
          match old with
          | Some v -> IdMap.add id0 v m
          | None -> IdMap.remove id0 m) shadow top0
      in
      { local_lets = (top' :: rest); local_vars = _UU03c3_.local_vars;
      toplevel_lets = _UU03c3_.toplevel_lets; registers = _UU03c3_.registers }

  (** val state_lookup : state -> id -> L.t **)

  let state_lookup _UU03c3_ id0 =
    match lookup Parse_ast.Unknown _UU03c3_ id0 with
    | Coq_inl _ -> L.top
    | Coq_inr v -> v

  (** val assign_id : id -> L.t -> state -> state **)

  let assign_id id0 new_v _UU03c3_ =
    match _UU03c3_.local_vars with
    | [] ->
      { local_lets = _UU03c3_.local_lets; local_vars = []; toplevel_lets =
        _UU03c3_.toplevel_lets; registers =
        (IdMap.add id0 new_v _UU03c3_.registers) }
    | top0 :: stack ->
      if IdMap.mem id0 _UU03c3_.registers
      then { local_lets = _UU03c3_.local_lets; local_vars =
             _UU03c3_.local_vars; toplevel_lets = _UU03c3_.toplevel_lets;
             registers = (IdMap.add id0 new_v _UU03c3_.registers) }
      else { local_lets = _UU03c3_.local_lets; local_vars =
             ((IdMap.add id0 new_v top0) :: stack); toplevel_lets =
             _UU03c3_.toplevel_lets; registers = _UU03c3_.registers }

  (** val subexp_values : t list -> L.t list **)

  let subexp_values rs =
    map (fun r -> match (fst r).this with
                  | Some v -> v
                  | None -> L.top) rs

  (** val assign_place : state -> (L.t place * L.t) -> state **)

  let assign_place _UU03c3_ = function
  | (p, x) ->
    (match L.place_root p with
     | Some id0 ->
       assign_id id0 (L.update_place p x (state_lookup _UU03c3_ id0)) _UU03c3_
     | None -> _UU03c3_)

  (** val assign : Tannot.t zlexp -> t list -> t -> state -> state **)

  let assign zl rs exp0 _UU03c3_ =
    let v = match (fst exp0).this with
            | Some v -> v
            | None -> L.top in
    let (o, _) = Destructure.zlexp_to_destructure (subexp_values rs) zl in
    (match o with
     | Some d ->
       fold_left assign_place (L.destructure_assignment d v) _UU03c3_
     | None -> _UU03c3_)
 end

module Make =
 functor (Tannot:S) ->
 functor (B:sig
  type t

  val mk_app : Tannot.t annot -> id -> t list -> t

  val mk_config : Tannot.t annot -> string list -> t

  val mk_id : Tannot.t annot -> id -> t

  val mk_block : Tannot.t annot -> t list -> t

  val mk_exit : Tannot.t annot -> t -> t

  val mk_ite : Tannot.t annot -> t -> t -> t -> t

  val mk_list : Tannot.t annot -> list_case -> t list -> t

  val mk_literal : Tannot.t annot -> lit -> t

  val mk_match :
    Tannot.t annot -> match_case -> t -> ((Tannot.t pat * t option) * t) list
    -> t

  val mk_pair : Tannot.t annot -> pair_case -> t -> t -> t

  val mk_ref : Tannot.t annot -> id -> t

  val mk_return : Tannot.t annot -> t -> t

  val mk_inline : Tannot.t annot -> t -> t

  val mk_single : Tannot.t annot -> single_case -> t -> t

  val mk_var : Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t -> t

  val mk_assign : Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t

  val mk_undef : Tannot.t annot -> t

  val mk_struct : Tannot.t annot -> struct_name -> (id * t) list -> t

  val mk_struct_update :
    Tannot.t annot -> struct_name -> t -> (id * t) list -> t
 end) ->
 functor (L:SAIL_VALUE) ->
 struct
  module R = Residual(Tannot)(B)(L)

  module Monad =
   struct
    type function_return =
    | Return_inlined of ((Tannot.t pat * Tannot.t exp option) * Tannot.t exp)
                        list
    | Return_value of R.value

    (** val function_return_rect :
        (((Tannot.t pat * Tannot.t exp option) * Tannot.t exp) list -> 'a1)
        -> (R.value -> 'a1) -> function_return -> 'a1 **)

    let function_return_rect f f0 = function
    | Return_inlined l0 -> f l0
    | Return_value v -> f0 v

    (** val function_return_rec :
        (((Tannot.t pat * Tannot.t exp option) * Tannot.t exp) list -> 'a1)
        -> (R.value -> 'a1) -> function_return -> 'a1 **)

    let function_return_rec f f0 = function
    | Return_inlined l0 -> f l0
    | Return_value v -> f0 v

    type 'a t =
    | Pure of 'a
    | Early_return of R.value * (unit -> 'a t)
    | Exit of R.value * (unit -> 'a t)
    | Call of id * R.value list * (function_return -> 'a t)
    | Get_config of string list * (R.value -> 'a t)
    | Runtime_type_error of Parse_ast.l
    | Get_undefined of typ * (R.value -> 'a t)

    (** val t_rect :
        ('a1 -> 'a2) -> (R.value -> (unit -> 'a1 t) -> (unit -> 'a2) -> 'a2)
        -> (R.value -> (unit -> 'a1 t) -> (unit -> 'a2) -> 'a2) -> (id ->
        R.value list -> (function_return -> 'a1 t) -> (function_return ->
        'a2) -> 'a2) -> (string list -> (R.value -> 'a1 t) -> (R.value ->
        'a2) -> 'a2) -> (Parse_ast.l -> 'a2) -> (typ -> (R.value -> 'a1 t) ->
        (R.value -> 'a2) -> 'a2) -> 'a1 t -> 'a2 **)

    let rec t_rect f f0 f1 f2 f3 f4 f5 = function
    | Pure y -> f y
    | Early_return (v, t1) ->
      f0 v t1 (fun u -> t_rect f f0 f1 f2 f3 f4 f5 (t1 u))
    | Exit (v, t1) -> f1 v t1 (fun u -> t_rect f f0 f1 f2 f3 f4 f5 (t1 u))
    | Call (i, l0, t1) ->
      f2 i l0 t1 (fun f6 -> t_rect f f0 f1 f2 f3 f4 f5 (t1 f6))
    | Get_config (l0, t1) ->
      f3 l0 t1 (fun v -> t_rect f f0 f1 f2 f3 f4 f5 (t1 v))
    | Runtime_type_error l0 -> f4 l0
    | Get_undefined (t1, t2) ->
      f5 t1 t2 (fun v -> t_rect f f0 f1 f2 f3 f4 f5 (t2 v))

    (** val t_rec :
        ('a1 -> 'a2) -> (R.value -> (unit -> 'a1 t) -> (unit -> 'a2) -> 'a2)
        -> (R.value -> (unit -> 'a1 t) -> (unit -> 'a2) -> 'a2) -> (id ->
        R.value list -> (function_return -> 'a1 t) -> (function_return ->
        'a2) -> 'a2) -> (string list -> (R.value -> 'a1 t) -> (R.value ->
        'a2) -> 'a2) -> (Parse_ast.l -> 'a2) -> (typ -> (R.value -> 'a1 t) ->
        (R.value -> 'a2) -> 'a2) -> 'a1 t -> 'a2 **)

    let rec t_rec f f0 f1 f2 f3 f4 f5 = function
    | Pure y -> f y
    | Early_return (v, t1) ->
      f0 v t1 (fun u -> t_rec f f0 f1 f2 f3 f4 f5 (t1 u))
    | Exit (v, t1) -> f1 v t1 (fun u -> t_rec f f0 f1 f2 f3 f4 f5 (t1 u))
    | Call (i, l0, t1) ->
      f2 i l0 t1 (fun f6 -> t_rec f f0 f1 f2 f3 f4 f5 (t1 f6))
    | Get_config (l0, t1) ->
      f3 l0 t1 (fun v -> t_rec f f0 f1 f2 f3 f4 f5 (t1 v))
    | Runtime_type_error l0 -> f4 l0
    | Get_undefined (t1, t2) ->
      f5 t1 t2 (fun v -> t_rec f f0 f1 f2 f3 f4 f5 (t2 v))

    (** val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t **)

    let rec bind m f =
      match m with
      | Pure x -> f x
      | Early_return (v, cont) ->
        Early_return (v, (fun _ -> bind (cont ()) f))
      | Exit (v, cont) -> Exit (v, (fun _ -> bind (cont ()) f))
      | Call (id0, args, cont) -> Call (id0, args, (fun v -> bind (cont v) f))
      | Get_config (key, cont) -> Get_config (key, (fun v -> bind (cont v) f))
      | Runtime_type_error l0 -> Runtime_type_error l0
      | Get_undefined (t0, cont) ->
        Get_undefined (t0, (fun v -> bind (cont v) f))

    (** val lift_sum : (Parse_ast.l, 'a1) sum -> 'a1 t **)

    let lift_sum = function
    | Coq_inl l0 -> Runtime_type_error l0
    | Coq_inr r -> Pure r
   end

  (** val pure : 'a1 -> 'a1 Monad.t **)

  let pure x =
    Monad.Pure x

  type t = (L.t option IdMap.t, R.t, R.state, Tannot.t) zexp

  (** val down :
      t -> R.state -> Tannot.t exp -> ((t * R.state) * (Tannot.t exp, R.t)
      sum) Monad.t **)

  let down ctx _UU03c3_ = function
  | E_aux (aux, annot0) ->
    let wrap = fun aux0 exp0 ->
      pure (((Z_aux (aux0, annot0)), _UU03c3_), (Coq_inl exp0))
    in
    (match aux with
     | E_block exps ->
       (match exps with
        | [] -> pure ((ctx, _UU03c3_), (Coq_inr (R.mk_block annot0 [])))
        | exp0 :: exps0 -> wrap (Z_block (ctx, [], exps0)) exp0)
     | E_id i ->
       (match Tannot.get_id_type (snd annot0) i with
        | Types.Enum_member ->
          pure ((ctx, _UU03c3_), (Coq_inr
            ((R.from_semilattice (L.mk_member (Aux.unwrap i))),
            (B.mk_id annot0 i))))
        | _ ->
          Monad.bind (Monad.lift_sum (R.lookup (fst annot0) _UU03c3_ i))
            (fun v ->
            pure ((ctx, _UU03c3_), (Coq_inr ((R.from_semilattice v),
              (B.mk_id annot0 i))))))
     | E_lit lit0 ->
       pure ((ctx, _UU03c3_), (Coq_inr (R.mk_literal annot0 lit0)))
     | E_typ (t0, exp0) -> wrap (Z_single (ctx, (Typ t0))) exp0
     | E_app (f, xs) ->
       (match xs with
        | [] ->
          Monad.bind (Monad.Call (f, [], pure)) (fun ret ->
            match ret with
            | Monad.Return_inlined arms ->
              pure (((Z_aux ((Z_match_head ((Z_aux ((Z_inline (ctx, None)),
                annot0)), Match, [], (Some arms))), annot0)),
                (R.push_scope _UU03c3_)), (Coq_inr
                ((R.from_semilattice (L.mk_unit ())),
                (B.mk_literal annot0 (L_aux (L_unit, (fst annot0)))))))
            | Monad.Return_value r ->
              pure ((ctx, _UU03c3_), (Coq_inr (r, (B.mk_app annot0 f [])))))
        | x :: xs0 -> wrap (Z_app (ctx, f, [], xs0)) x)
     | E_tuple exps ->
       (match exps with
        | [] -> pure ((ctx, _UU03c3_), (Coq_inr (R.mk_list annot0 Tuple [])))
        | exp0 :: exps0 -> wrap (Z_list (ctx, Tuple, [], exps0)) exp0)
     | E_if (i, t0, e) -> wrap (Z_if_cond (ctx, t0, e)) i
     | E_vector exps ->
       (match exps with
        | [] -> pure ((ctx, _UU03c3_), (Coq_inr (R.mk_list annot0 Vector [])))
        | exp0 :: exps0 ->
          if Tannot.is_bitvector (snd annot0)
          then wrap (Z_list (ctx, Bitvector, [], exps0)) exp0
          else wrap (Z_list (ctx, Vector, [], exps0)) exp0)
     | E_vector_append (l0, r) -> wrap (Z_pair_1 (ctx, Vector_append, r)) l0
     | E_list exps ->
       (match exps with
        | [] -> pure ((ctx, _UU03c3_), (Coq_inr (R.mk_list annot0 List [])))
        | exp0 :: exps0 -> wrap (Z_list (ctx, List, [], exps0)) exp0)
     | E_cons (h, t0) -> wrap (Z_pair_1 (ctx, Cons, t0)) h
     | E_struct (sn, fes) ->
       (match fes with
        | [] -> pure ((ctx, _UU03c3_), (Coq_inr (R.mk_struct annot0 sn [])))
        | f0 :: rest ->
          let FE_aux (f1, _) = f0 in
          let FE_fexp (f, e) = f1 in wrap (Z_struct (ctx, sn, [], f, rest)) e)
     | E_struct_update (base, fes) ->
       wrap (Z_struct_update_base (ctx, SN_anon, fes)) base
     | E_field (exp0, fld) -> wrap (Z_single (ctx, (Field fld))) exp0
     | E_match (head, arms) ->
       wrap (Z_match_head (ctx, Match, [], (Some (map unwrap_arm arms)))) head
     | E_let (pat0, exp0, body) ->
       wrap (Z_match_head (ctx, Letbind, [], (Some (((pat0, None),
         body) :: [])))) exp0
     | E_assign (l0, exp0) ->
       let subexps = lexp_subexps l0 in
       (match subexps with
        | [] -> wrap (Z_assign_right (ctx, (lexp_to_z l0), [])) exp0
        | x :: xs ->
          wrap (Z_assign_left (ctx, (lexp_to_z l0), [], xs, exp0)) x)
     | E_return exp0 -> wrap (Z_return ctx) exp0
     | E_exit exp0 -> wrap (Z_exit ctx) exp0
     | E_config key ->
       Monad.bind (Monad.Get_config (key, pure)) (fun v ->
         pure ((ctx, _UU03c3_), (Coq_inr (v, (B.mk_config annot0 key)))))
     | E_ref id0 -> pure ((ctx, _UU03c3_), (Coq_inr (R.mk_ref annot0 id0)))
     | E_throw exp0 -> wrap (Z_single (ctx, Throw)) exp0
     | E_try (head, arms) ->
       wrap (Z_match_head (ctx, Try, [], (Some (map unwrap_arm arms)))) head
     | E_assert (exp0, msg) -> wrap (Z_pair_1 (ctx, Assert, msg)) exp0
     | E_var (l0, exp0, body) ->
       let subexps = lexp_subexps l0 in
       (match subexps with
        | [] -> wrap (Z_var_right (ctx, (lexp_to_z l0), [], body)) exp0
        | x :: xs ->
          wrap (Z_var_left (ctx, (lexp_to_z l0), [], xs, exp0, body)) x)
     | E_undef ->
       Monad.bind (Monad.Get_undefined ((Tannot.get_type (snd annot0)),
         pure)) (fun u ->
         pure ((ctx, _UU03c3_), (Coq_inr (u, (B.mk_undef annot0)))))
     | E_internal_plet (pat0, exp0, body) ->
       wrap (Z_match_head (ctx, Internal_plet, [], (Some (((pat0, None),
         body) :: [])))) exp0
     | E_internal_return exp0 -> wrap (Z_single (ctx, Internal_return)) exp0
     | E_internal_assume (constr, exp0) ->
       wrap (Z_single (ctx, (Internal_assume constr))) exp0
     | _ -> Monad.Runtime_type_error (fst annot0))

  (** val join_inline_return : R.t -> t -> t option **)

  let rec join_inline_return ret = function
  | Z_aux (aux, annot0) ->
    (match aux with
     | Z_single (parent, c) ->
       option_map (fun p -> Z_aux ((Z_single (p, c)), annot0))
         (join_inline_return ret parent)
     | Z_return parent ->
       option_map (fun p -> Z_aux ((Z_return p), annot0))
         (join_inline_return ret parent)
     | Z_inline (parent, acc) ->
       Some (Z_aux ((Z_inline (parent, (Some (R.join_returns acc ret)))),
         annot0))
     | Z_exit parent ->
       option_map (fun p -> Z_aux ((Z_exit p), annot0))
         (join_inline_return ret parent)
     | Z_pair_1 (parent, c, e) ->
       option_map (fun p -> Z_aux ((Z_pair_1 (p, c, e)), annot0))
         (join_inline_return ret parent)
     | Z_pair_2 (parent, c, r) ->
       option_map (fun p -> Z_aux ((Z_pair_2 (p, c, r)), annot0))
         (join_inline_return ret parent)
     | Z_list (parent, c, rs, es) ->
       option_map (fun p -> Z_aux ((Z_list (p, c, rs, es)), annot0))
         (join_inline_return ret parent)
     | Z_app (parent, f, rs, es) ->
       option_map (fun p -> Z_aux ((Z_app (p, f, rs, es)), annot0))
         (join_inline_return ret parent)
     | Z_block (parent, rs, es) ->
       option_map (fun p -> Z_aux ((Z_block (p, rs, es)), annot0))
         (join_inline_return ret parent)
     | Z_if_cond (parent, thn, els) ->
       option_map (fun p -> Z_aux ((Z_if_cond (p, thn, els)), annot0))
         (join_inline_return ret parent)
     | Z_if_then (parent, sr, els) ->
       option_map (fun p -> Z_aux ((Z_if_then (p, sr, els)), annot0))
         (join_inline_return ret parent)
     | Z_if_else (parent, thn, sr) ->
       option_map (fun p -> Z_aux ((Z_if_else (p, thn, sr)), annot0))
         (join_inline_return ret parent)
     | Z_match_head (parent, mc, ev, un) ->
       option_map (fun p -> Z_aux ((Z_match_head (p, mc, ev, un)), annot0))
         (join_inline_return ret parent)
     | Z_match_arms_guard (parent, mc, bnd, sr, ev, pt, gm, bd, un) ->
       option_map (fun p -> Z_aux ((Z_match_arms_guard (p, mc, bnd, sr, ev,
         pt, gm, bd, un)), annot0)) (join_inline_return ret parent)
     | Z_match_arms_body (parent, mc, bnd, sr, ev, pt, gd, un) ->
       option_map (fun p -> Z_aux ((Z_match_arms_body (p, mc, bnd, sr, ev,
         pt, gd, un)), annot0)) (join_inline_return ret parent)
     | Z_assign_left (parent, l0, rs, es, e) ->
       option_map (fun p -> Z_aux ((Z_assign_left (p, l0, rs, es, e)),
         annot0)) (join_inline_return ret parent)
     | Z_assign_right (parent, l0, rs) ->
       option_map (fun p -> Z_aux ((Z_assign_right (p, l0, rs)), annot0))
         (join_inline_return ret parent)
     | Z_var_left (parent, l0, rs, es, e1, e2) ->
       option_map (fun p -> Z_aux ((Z_var_left (p, l0, rs, es, e1, e2)),
         annot0)) (join_inline_return ret parent)
     | Z_var_right (parent, l0, rs, e) ->
       option_map (fun p -> Z_aux ((Z_var_right (p, l0, rs, e)), annot0))
         (join_inline_return ret parent)
     | Z_var_body (parent, l0, rs, r) ->
       option_map (fun p -> Z_aux ((Z_var_body (p, l0, rs, r)), annot0))
         (join_inline_return ret parent)
     | Z_struct (parent, sn, rs, f, fes) ->
       option_map (fun p -> Z_aux ((Z_struct (p, sn, rs, f, fes)), annot0))
         (join_inline_return ret parent)
     | Z_struct_update_base (parent, sn, fes) ->
       option_map (fun p -> Z_aux ((Z_struct_update_base (p, sn, fes)),
         annot0)) (join_inline_return ret parent)
     | Z_struct_update (parent, sn, r, rs, f, fes) ->
       option_map (fun p -> Z_aux ((Z_struct_update (p, sn, r, rs, f, fes)),
         annot0)) (join_inline_return ret parent))
  | Z_top -> None

  (** val next :
      (L.t option IdMap.t, R.t, R.state, Tannot.t) zexp_aux -> Tannot.t annot
      -> R.state -> R.t -> ((t * R.state) * (Tannot.t exp, R.t) sum) Monad.t **)

  let next aux annot0 _UU03c3_ focus =
    match aux with
    | Z_single (parent, _UU03b3_) ->
      pure ((parent, _UU03c3_), (Coq_inr (R.mk_single annot0 _UU03b3_ focus)))
    | Z_return parent ->
      (match join_inline_return focus parent with
       | Some parent' ->
         pure ((parent', _UU03c3_), (Coq_inr (R.mk_return annot0 focus)))
       | None ->
         Monad.bind (Monad.Early_return ((fst focus), pure)) (fun _ ->
           pure ((parent, _UU03c3_), (Coq_inr (R.mk_return annot0 focus)))))
    | Z_inline (parent, acc) ->
      pure ((parent, (R.pop_scope _UU03c3_)), (Coq_inr
        (R.mk_inline annot0 acc focus)))
    | Z_exit parent ->
      Monad.bind (Monad.Exit ((fst focus), pure)) (fun _ ->
        pure ((parent, _UU03c3_), (Coq_inr (R.mk_exit annot0 focus))))
    | Z_pair_1 (parent, _UU03b3_, y) ->
      pure (((Z_aux ((Z_pair_2 (parent, _UU03b3_, focus)), annot0)),
        _UU03c3_), (Coq_inl y))
    | Z_pair_2 (parent, _UU03b3_, x) ->
      pure ((parent, _UU03c3_), (Coq_inr (R.mk_pair annot0 _UU03b3_ x focus)))
    | Z_list (parent, _UU03b3_, evaluated, unevaluated) ->
      (match unevaluated with
       | [] ->
         pure ((parent, _UU03c3_), (Coq_inr
           (R.mk_list annot0 _UU03b3_ (focus :: evaluated))))
       | u :: us ->
         pure (((Z_aux ((Z_list (parent, _UU03b3_, (focus :: evaluated),
           us)), annot0)), _UU03c3_), (Coq_inl u)))
    | Z_app (parent, f, evaluated, unevaluated) ->
      let Id_aux (i, _) = f in
      (match i with
       | And_bool ->
         (match evaluated with
          | [] ->
            (match unevaluated with
             | [] ->
               Monad.bind (Monad.Call (f,
                 (rev (map fst (focus :: evaluated))), pure)) (fun ret ->
                 match ret with
                 | Monad.Return_inlined arms ->
                   (match evaluated with
                    | [] ->
                      pure (((Z_aux ((Z_match_head ((Z_aux ((Z_inline
                        (parent, None)), annot0)), Match, [], (Some arms))),
                        annot0)), (R.push_scope _UU03c3_)), (Coq_inr focus))
                    | _ :: _ ->
                      pure (((Z_aux ((Z_match_head ((Z_aux ((Z_inline
                        (parent, None)), annot0)), Match, [], (Some arms))),
                        annot0)), (R.push_scope _UU03c3_)), (Coq_inr
                        (R.mk_list annot0 Tuple (focus :: evaluated)))))
                 | Monad.Return_value r ->
                   pure ((parent, _UU03c3_), (Coq_inr (r,
                     (B.mk_app annot0 f (rev (map snd (focus :: evaluated))))))))
             | u :: us ->
               (match us with
                | [] ->
                  let false_lit = E_aux ((E_lit (L_aux (L_false,
                    Parse_ast.Unknown))), annot0)
                  in
                  if R.is_true (fst focus)
                  then pure ((parent, _UU03c3_), (Coq_inl u))
                  else if R.is_false (fst focus)
                       then pure ((parent, _UU03c3_), (Coq_inr focus))
                       else pure (((Z_aux ((Z_if_then (parent, (_UU03c3_,
                              focus), false_lit)), annot0)), _UU03c3_),
                              (Coq_inl u))
                | _ :: _ ->
                  pure (((Z_aux ((Z_app (parent, f, (focus :: evaluated),
                    us)), annot0)), _UU03c3_), (Coq_inl u))))
          | _ :: _ ->
            (match unevaluated with
             | [] ->
               Monad.bind (Monad.Call (f,
                 (rev (map fst (focus :: evaluated))), pure)) (fun ret ->
                 match ret with
                 | Monad.Return_inlined arms ->
                   (match evaluated with
                    | [] ->
                      pure (((Z_aux ((Z_match_head ((Z_aux ((Z_inline
                        (parent, None)), annot0)), Match, [], (Some arms))),
                        annot0)), (R.push_scope _UU03c3_)), (Coq_inr focus))
                    | _ :: _ ->
                      pure (((Z_aux ((Z_match_head ((Z_aux ((Z_inline
                        (parent, None)), annot0)), Match, [], (Some arms))),
                        annot0)), (R.push_scope _UU03c3_)), (Coq_inr
                        (R.mk_list annot0 Tuple (focus :: evaluated)))))
                 | Monad.Return_value r ->
                   pure ((parent, _UU03c3_), (Coq_inr (r,
                     (B.mk_app annot0 f (rev (map snd (focus :: evaluated))))))))
             | u :: us ->
               pure (((Z_aux ((Z_app (parent, f, (focus :: evaluated), us)),
                 annot0)), _UU03c3_), (Coq_inl u))))
       | Or_bool ->
         (match evaluated with
          | [] ->
            (match unevaluated with
             | [] ->
               Monad.bind (Monad.Call (f,
                 (rev (map fst (focus :: evaluated))), pure)) (fun ret ->
                 match ret with
                 | Monad.Return_inlined arms ->
                   (match evaluated with
                    | [] ->
                      pure (((Z_aux ((Z_match_head ((Z_aux ((Z_inline
                        (parent, None)), annot0)), Match, [], (Some arms))),
                        annot0)), (R.push_scope _UU03c3_)), (Coq_inr focus))
                    | _ :: _ ->
                      pure (((Z_aux ((Z_match_head ((Z_aux ((Z_inline
                        (parent, None)), annot0)), Match, [], (Some arms))),
                        annot0)), (R.push_scope _UU03c3_)), (Coq_inr
                        (R.mk_list annot0 Tuple (focus :: evaluated)))))
                 | Monad.Return_value r ->
                   pure ((parent, _UU03c3_), (Coq_inr (r,
                     (B.mk_app annot0 f (rev (map snd (focus :: evaluated))))))))
             | u :: us ->
               (match us with
                | [] ->
                  let true_lit = E_aux ((E_lit (L_aux (L_true,
                    Parse_ast.Unknown))), annot0)
                  in
                  if R.is_true (fst focus)
                  then pure ((parent, _UU03c3_), (Coq_inr focus))
                  else if R.is_false (fst focus)
                       then pure ((parent, _UU03c3_), (Coq_inl u))
                       else pure (((Z_aux ((Z_if_then (parent, (_UU03c3_,
                              focus), u)), annot0)), _UU03c3_), (Coq_inl
                              true_lit))
                | _ :: _ ->
                  pure (((Z_aux ((Z_app (parent, f, (focus :: evaluated),
                    us)), annot0)), _UU03c3_), (Coq_inl u))))
          | _ :: _ ->
            (match unevaluated with
             | [] ->
               Monad.bind (Monad.Call (f,
                 (rev (map fst (focus :: evaluated))), pure)) (fun ret ->
                 match ret with
                 | Monad.Return_inlined arms ->
                   (match evaluated with
                    | [] ->
                      pure (((Z_aux ((Z_match_head ((Z_aux ((Z_inline
                        (parent, None)), annot0)), Match, [], (Some arms))),
                        annot0)), (R.push_scope _UU03c3_)), (Coq_inr focus))
                    | _ :: _ ->
                      pure (((Z_aux ((Z_match_head ((Z_aux ((Z_inline
                        (parent, None)), annot0)), Match, [], (Some arms))),
                        annot0)), (R.push_scope _UU03c3_)), (Coq_inr
                        (R.mk_list annot0 Tuple (focus :: evaluated)))))
                 | Monad.Return_value r ->
                   pure ((parent, _UU03c3_), (Coq_inr (r,
                     (B.mk_app annot0 f (rev (map snd (focus :: evaluated))))))))
             | u :: us ->
               pure (((Z_aux ((Z_app (parent, f, (focus :: evaluated), us)),
                 annot0)), _UU03c3_), (Coq_inl u))))
       | _ ->
         (match unevaluated with
          | [] ->
            Monad.bind (Monad.Call (f, (rev (map fst (focus :: evaluated))),
              pure)) (fun ret ->
              match ret with
              | Monad.Return_inlined arms ->
                (match evaluated with
                 | [] ->
                   pure (((Z_aux ((Z_match_head ((Z_aux ((Z_inline (parent,
                     None)), annot0)), Match, [], (Some arms))), annot0)),
                     (R.push_scope _UU03c3_)), (Coq_inr focus))
                 | _ :: _ ->
                   pure (((Z_aux ((Z_match_head ((Z_aux ((Z_inline (parent,
                     None)), annot0)), Match, [], (Some arms))), annot0)),
                     (R.push_scope _UU03c3_)), (Coq_inr
                     (R.mk_list annot0 Tuple (focus :: evaluated)))))
              | Monad.Return_value r ->
                pure ((parent, _UU03c3_), (Coq_inr (r,
                  (B.mk_app annot0 f (rev (map snd (focus :: evaluated))))))))
          | u :: us ->
            pure (((Z_aux ((Z_app (parent, f, (focus :: evaluated), us)),
              annot0)), _UU03c3_), (Coq_inl u))))
    | Z_block (parent, evaluated, unevaluated) ->
      (match unevaluated with
       | [] ->
         pure ((parent, _UU03c3_), (Coq_inr
           (R.mk_block annot0 (focus :: evaluated))))
       | u :: us ->
         if is_none (R.this (fst focus))
         then pure ((parent, _UU03c3_), (Coq_inr focus))
         else if R.is_unit (fst focus)
              then pure (((Z_aux ((Z_block (parent, evaluated, us)),
                     annot0)), _UU03c3_), (Coq_inl u))
              else pure (((Z_aux ((Z_block (parent, (focus :: evaluated),
                     us)), annot0)), _UU03c3_), (Coq_inl u)))
    | Z_if_cond (parent, t0, e) ->
      if R.is_true (fst focus)
      then pure (((Z_aux ((Z_block (parent, (focus :: []), [])), annot0)),
             _UU03c3_), (Coq_inl t0))
      else if R.is_false (fst focus)
           then pure (((Z_aux ((Z_block (parent, (focus :: []), [])),
                  annot0)), _UU03c3_), (Coq_inl e))
           else pure (((Z_aux ((Z_if_then (parent, (_UU03c3_, focus), e)),
                  annot0)), _UU03c3_), (Coq_inl t0))
    | Z_if_then (parent, p, e) ->
      let (_UU03c3__i, i) = p in
      pure (((Z_aux ((Z_if_else (parent, i, (_UU03c3_, focus))), annot0)),
        _UU03c3__i), (Coq_inl e))
    | Z_if_else (parent, i, p) ->
      let (_UU03c3__t, t0) = p in
      pure ((parent, (R.join _UU03c3__t _UU03c3_)), (Coq_inr
        (R.mk_ite annot0 i t0 focus)))
    | Z_match_head (parent, _UU03b3_, evaluated, unevaluated) ->
      (match unevaluated with
       | Some l0 ->
         (match l0 with
          | [] ->
            pure ((parent,
              (R.end_match _UU03b3_ (Some _UU03c3_)
                (map (fun pat0 ->
                  let (y, _) = pat0 in
                  let (y1, _) = y in let (_UU03c3_0, _) = y1 in _UU03c3_0)
                  evaluated))),
              (Coq_inr (R.mk_match annot0 _UU03b3_ false focus evaluated)))
          | p :: arms ->
            let (p0, body) = p in
            let (pat0, guard) = p0 in
            Monad.bind
              (Monad.lift_sum
                (R.pattern_match (fst annot0) _UU03b3_ pat0 focus))
              (fun mr ->
              match mr with
              | Matched _UU03b2_ ->
                let (shadow, _UU03c3_') =
                  R.bind_arm (IdMap.map L.complete _UU03b2_) _UU03c3_
                in
                (match guard with
                 | Some g ->
                   pure (((Z_aux ((Z_match_arms_guard (parent, _UU03b3_,
                     shadow, (_UU03c3_, focus), evaluated, pat0, true, body,
                     (Some arms))), annot0)), _UU03c3_'), (Coq_inl g))
                 | None ->
                   pure (((Z_aux ((Z_match_arms_body (parent, _UU03b3_,
                     shadow, (_UU03c3_, focus), evaluated, pat0, None,
                     None)), annot0)), _UU03c3_'), (Coq_inl body)))
              | MaybeMatched _UU03b2_ ->
                let (shadow, _UU03c3_') =
                  R.bind_arm (IdMap.map L.complete _UU03b2_) _UU03c3_
                in
                (match guard with
                 | Some g ->
                   pure (((Z_aux ((Z_match_arms_guard (parent, _UU03b3_,
                     shadow, (_UU03c3_, focus), evaluated, pat0, false, body,
                     (Some arms))), annot0)), _UU03c3_'), (Coq_inl g))
                 | None ->
                   pure (((Z_aux ((Z_match_arms_body (parent, _UU03b3_,
                     shadow, (_UU03c3_, focus), evaluated, pat0, None, (Some
                     arms))), annot0)), _UU03c3_'), (Coq_inl body)))
              | Unmatched ->
                pure (((Z_aux ((Z_match_head (parent, _UU03b3_, evaluated,
                  (Some arms))), annot0)), _UU03c3_), (Coq_inr focus))))
       | None ->
         pure ((parent,
           (R.end_match _UU03b3_ None
             (map (fun pat0 ->
               let (y, _) = pat0 in
               let (y1, _) = y in let (_UU03c3_0, _) = y1 in _UU03c3_0)
               evaluated))),
           (Coq_inr (R.mk_match annot0 _UU03b3_ true focus evaluated))))
    | Z_match_arms_guard (parent, _UU03b3_, shadow, p, evaluated, pat0,
                          guaranteed_match, body, unevaluated) ->
      let (_UU03c3__h, h) = p in
      if (&&) (is_none (R.this (fst focus)))
           (negb (is_none (R.exn (fst focus))))
      then pure ((parent, (R.restore_arm shadow _UU03c3_)), (Coq_inr focus))
      else if R.is_true (fst focus)
           then let unevaluated' =
                  if guaranteed_match then None else unevaluated
                in
                pure (((Z_aux ((Z_match_arms_body (parent, _UU03b3_, shadow,
                  (_UU03c3__h, h), evaluated, pat0, None, unevaluated')),
                  annot0)), _UU03c3_), (Coq_inl body))
           else if R.is_false (fst focus)
                then pure (((Z_aux ((Z_match_head (parent, _UU03b3_,
                       evaluated, unevaluated)), annot0)), _UU03c3__h),
                       (Coq_inr h))
                else pure (((Z_aux ((Z_match_arms_body (parent, _UU03b3_,
                       shadow, (_UU03c3__h, h), evaluated, pat0, (Some
                       focus), unevaluated)), annot0)), _UU03c3_), (Coq_inl
                       body))
    | Z_match_arms_body (parent, _UU03b3_, shadow, p, evaluated, pat0, guard,
                         unevaluated) ->
      let (_UU03c3__h, h) = p in
      pure (((Z_aux ((Z_match_head (parent, _UU03b3_,
        (((((R.restore_arm shadow _UU03c3_), pat0), guard),
        focus) :: evaluated), unevaluated)), annot0)), _UU03c3__h), (Coq_inr
        h))
    | Z_assign_left (parent, l0, evaluated, unevaluated, exp0) ->
      (match unevaluated with
       | [] ->
         pure (((Z_aux ((Z_assign_right (parent, l0,
           (rev (focus :: evaluated)))), annot0)), _UU03c3_), (Coq_inl exp0))
       | u :: us ->
         pure (((Z_aux ((Z_assign_left (parent, l0, (focus :: evaluated), us,
           exp0)), annot0)), _UU03c3_), (Coq_inl u)))
    | Z_assign_right (parent, l0, evaluated) ->
      pure ((parent, (R.assign l0 evaluated focus _UU03c3_)), (Coq_inr
        (R.mk_assign annot0 l0 evaluated focus)))
    | Z_var_left (parent, l0, evaluated, unevaluated, exp0, body) ->
      (match unevaluated with
       | [] ->
         pure (((Z_aux ((Z_var_right (parent, l0, (rev (focus :: evaluated)),
           body)), annot0)), _UU03c3_), (Coq_inl exp0))
       | u :: us ->
         pure (((Z_aux ((Z_var_left (parent, l0, (focus :: evaluated), us,
           exp0, body)), annot0)), _UU03c3_), (Coq_inl u)))
    | Z_var_right (parent, l0, evaluated, body) ->
      pure (((Z_aux ((Z_var_body (parent, l0, evaluated, focus)), annot0)),
        (R.assign l0 evaluated focus _UU03c3_)), (Coq_inl body))
    | Z_var_body (parent, l0, evaluated, v) ->
      pure ((parent, _UU03c3_), (Coq_inr
        (R.mk_var annot0 l0 evaluated v focus)))
    | Z_struct (parent, sn, evaluated, cur, unevaluated) ->
      let evaluated' = (cur, focus) :: evaluated in
      (match unevaluated with
       | [] ->
         pure ((parent, _UU03c3_), (Coq_inr
           (R.mk_struct annot0 sn evaluated')))
       | f0 :: rest ->
         let FE_aux (f1, _) = f0 in
         let FE_fexp (f, e) = f1 in
         pure (((Z_aux ((Z_struct (parent, sn, evaluated', f, rest)),
           annot0)), _UU03c3_), (Coq_inl e)))
    | Z_struct_update_base (parent, sn, fes) ->
      (match fes with
       | [] ->
         pure ((parent, _UU03c3_), (Coq_inr
           (R.mk_struct_update annot0 sn focus [])))
       | f0 :: rest ->
         let FE_aux (f1, _) = f0 in
         let FE_fexp (f, e) = f1 in
         pure (((Z_aux ((Z_struct_update (parent, sn, focus, [], f, rest)),
           annot0)), _UU03c3_), (Coq_inl e)))
    | Z_struct_update (parent, sn, base, evaluated, cur, unevaluated) ->
      let evaluated' = (cur, focus) :: evaluated in
      (match unevaluated with
       | [] ->
         pure ((parent, _UU03c3_), (Coq_inr
           (R.mk_struct_update annot0 sn base evaluated')))
       | f0 :: rest ->
         let FE_aux (f1, _) = f0 in
         let FE_fexp (f, e) = f1 in
         pure (((Z_aux ((Z_struct_update (parent, sn, base, evaluated', f,
           rest)), annot0)), _UU03c3_), (Coq_inl e)))

  (** val step :
      t -> R.state -> (Tannot.t exp, R.t) sum -> ((t * R.state) * (Tannot.t
      exp, R.t) sum) Monad.t **)

  let step ctx _UU03c3_ = function
  | Coq_inl exp0 -> down ctx _UU03c3_ exp0
  | Coq_inr v ->
    (match ctx with
     | Z_aux (aux, annot0) -> next aux annot0 _UU03c3_ v
     | Z_top -> pure ((Z_top, _UU03c3_), (Coq_inr v)))
 end
