(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(****************************************************************************)

open Ast
open Ast_util
open Util

module Big_int = Nat_big_num

open Type_internal

(* Linearize cases involving power where we would otherwise require
   the SMT solver to use non-linear arithmetic. *)
let opt_smt_linearize = ref false

let opt_string_literal_type = ref false

module StringMap = Map.Make (String)

module IdPair = struct
  type t = id * id
  let compare (a, b) (c, d) =
    let x = Id.compare a c in
    if x = 0 then Id.compare b d else x
end

module IdPairMap = Map.Make (IdPair)

type ('a, 'b) generic_env_item = { item : 'a; loc : 'b; mod_id : Project.mod_id; visibility : visibility }

type 'a env_item = ('a, Parse_ast.l) generic_env_item

type 'a multiple_env_item = ('a, Parse_ast.l list) generic_env_item

let item_loc item = item.loc

type global_env = {
  default_order : order option;
  modules : Project.project_structure option;
  val_specs : (typquant * typ) env_item Bindings.t;
  defined_val_specs : IdSet.t;
  externs : extern Bindings.t;
  mappings : (typquant * typ * typ) env_item Bindings.t;
  unions : (typquant * type_union list) env_item Bindings.t;
  union_ids : (typquant * typ) env_item Bindings.t;
  scattered_union_envs : global_env Bindings.t;
  abstract_typs : kind env_item Bindings.t;
  constraints : (constraint_reason * n_constraint) list;
  enums : (bool * IdSet.t) env_item Bindings.t;
  records : (typquant * (typ * id) list) env_item Bindings.t;
  synonyms : (typquant * typ_arg) env_item Bindings.t;
  accessors : (typquant * typ) env_item IdPairMap.t;
  bitfields : (typ * index_range Bindings.t) env_item Bindings.t;
  allow_undefined : IdSet.t;
  letbinds : typ env_item Bindings.t;
  registers : typ env_item Bindings.t;
  overloads : id list multiple_env_item Bindings.t;
  outcomes : (typquant * typ * kinded_id list * id list * (typquant * typ) env_item Bindings.t) env_item Bindings.t;
  outcome_instantiation : (Ast.l * typ) KBindings.t;
}

let empty_global_env =
  {
    default_order = None;
    modules = None;
    val_specs = Bindings.empty;
    defined_val_specs = IdSet.empty;
    externs = Bindings.empty;
    mappings = Bindings.empty;
    unions = Bindings.empty;
    union_ids = Bindings.empty;
    scattered_union_envs = Bindings.empty;
    abstract_typs = Bindings.empty;
    constraints = [];
    enums = Bindings.empty;
    records = Bindings.empty;
    accessors = IdPairMap.empty;
    synonyms = Bindings.empty;
    bitfields = Bindings.empty;
    allow_undefined = IdSet.empty;
    letbinds = Bindings.empty;
    registers = Bindings.empty;
    overloads = Bindings.empty;
    outcomes = Bindings.empty;
    outcome_instantiation = KBindings.empty;
  }

type env = {
  global : global_env;
  current_module : Project.mod_id;
  current_visibility : visibility;
  open_all : bool;
  opened : Project.ModSet.t;
  locals : (mut * typ) Bindings.t;
  typ_vars : (Ast.l * kind_aux) KBindings.t;
  shadow_vars : int KBindings.t;
  allow_bindings : bool;
  constraints : (constraint_reason * n_constraint) list;
  ret_typ : typ option;
  prove : (env -> n_constraint -> bool) option;
  allow_unknowns : bool;
  toplevel : l option;
  outcome_typschm : (typquant * typ) option;
}

let update_global f env = { env with global = f env.global }

let mk_item ~loc:l env item = { item; loc = l; mod_id = env.current_module; visibility = env.current_visibility }
let mk_item_in ~loc:l scope env item = { item; loc = l; mod_id = scope; visibility = env.current_visibility }

let mk_item_in_opt ~loc scope_opt env item =
  match scope_opt with Some scope -> mk_item_in ~loc scope env item | None -> mk_item ~loc env item

let item_in_scope env item =
  item.mod_id = env.current_module
  || (Project.ModSet.mem item.mod_id env.opened && is_public item.visibility)
  || env.open_all

let filter_items_with f env bindings =
  Bindings.map (fun item -> f item.item) (Bindings.filter (fun _ item -> item_in_scope env item) bindings)

let filter_items env bindings = filter_items_with (fun x -> x) env bindings

let err_not_in_scope env msg l item =
  match env.global.modules with
  | None -> Err_not_in_scope (msg, l, None, None, is_private item.visibility)
  | Some proj ->
      let module_name_opt mod_id =
        if Project.valid_module_id proj mod_id then Some (Project.module_name proj mod_id) else None
      in
      Err_not_in_scope
        (msg, l, module_name_opt item.mod_id, module_name_opt env.current_module, is_private item.visibility)

let get_item_with_loc get_loc l env item =
  if item_in_scope env item then item.item
  else (
    match env.global.modules with
    | None -> typ_raise l (err_not_in_scope env None (get_loc item.loc) item)
    | Some proj -> typ_raise l (err_not_in_scope env None (get_loc item.loc) item)
  )

let get_item l env item = get_item_with_loc (fun l -> Some l) l env item

let hd_opt = function x :: _ -> Some x | [] -> None

type type_variables = Type_internal.type_variables

type t = env

let set_modules proj env = update_global (fun global -> { global with modules = Some proj }) env

let get_module_id_opt env name = Option.bind env.global.modules (fun proj -> Project.get_module_id proj name)

let get_module_id ~at:l env name =
  match get_module_id_opt env name with Some mod_id -> mod_id | None -> typ_error l ("Failed to find module " ^ name)

let start_module ~at:l mod_id env =
  match env.global.modules with
  | None -> Reporting.unreachable l __POS__ "start_module called in environment with no modules" [@coverage off]
  | Some proj ->
      if not (Project.valid_module_id proj mod_id) then
        Reporting.unreachable l __POS__ "start_module got an invalid module id" [@coverage off];
      let requires = Project.module_requires proj mod_id in
      { env with current_module = mod_id; opened = Project.ModSet.of_list (Project.global_scope :: requires) }

let end_module env = { env with current_module = Project.global_scope; opened = Project.ModSet.empty }

let open_all_modules env = { env with open_all = true }

let with_private_visibility ?(restore = fun env -> env) ~at:l env =
  let saved_visibility = env.current_visibility in
  ({ env with current_visibility = Private l }, fun env -> { (restore env) with current_visibility = saved_visibility })

let with_private_visibility_if ?(restore : env -> env = fun env -> env) ~at:l b env =
  if b then with_private_visibility ~restore ~at:l env else (env, restore)

let get_current_visibility env = env.current_visibility

type module_state = Project.mod_id * Project.ModSet.t

let with_global_scope env =
  let current_module = env.current_module in
  let opened = env.opened in
  (open_all_modules (end_module env), (current_module, opened))

let restore_scope (current_module, opened) env = { env with current_module; opened; open_all = false }

let empty =
  {
    global = empty_global_env;
    current_module = Project.global_scope;
    current_visibility = Public;
    open_all = false;
    opened = Project.ModSet.empty;
    locals = Bindings.empty;
    typ_vars = KBindings.empty;
    shadow_vars = KBindings.empty;
    allow_bindings = true;
    constraints = [];
    ret_typ = None;
    prove = None;
    allow_unknowns = false;
    toplevel = None;
    outcome_typschm = None;
  }

let counter = ref 0

let fresh_kid ?(kid = mk_kid "") _env =
  let suffix = if Kid.compare kid (mk_kid "") = 0 then "#" else "#" ^ string_of_id (id_of_kid kid) in
  let fresh = Kid_aux (Var ("'fv" ^ string_of_int !counter ^ suffix), Parse_ast.Unknown) in
  incr counter;
  fresh

let freshen_kid env kid (typq, typ) =
  if KidSet.mem kid (KidSet.of_list (List.map kopt_kid (quant_kopts typq))) then (
    let fresh = fresh_kid ~kid env in
    (typquant_subst_kid kid fresh typq, subst_kid typ_subst kid fresh typ)
  )
  else (typq, typ)

let freshen_bind env bind =
  List.fold_left (fun bind (kid, _) -> freshen_kid env kid bind) bind (KBindings.bindings env.typ_vars)

let set_prover f env = { env with prove = f }

let allow_unknowns env = env.allow_unknowns
let set_allow_unknowns b env = { env with allow_unknowns = b }

let is_user_undefined id env = IdSet.mem id env.global.allow_undefined

let allow_user_undefined id env =
  update_global (fun global -> { global with allow_undefined = IdSet.add id global.allow_undefined }) env

(* First, we define how type variables are added to the
   environment. If we add a new variable shadowing a previous
   variable, we need to modify the environment so the shadowed
   variable is renamed. We can't just remove it because it may be
   referenced by constraints. *)
let shadows v env = match KBindings.find_opt v env.shadow_vars with Some n -> n | None -> 0

let add_typ_var_shadow l (KOpt_aux (KOpt_kind (K_aux (k, _), v), _)) env =
  if KBindings.mem v env.typ_vars then begin
    let n = match KBindings.find_opt v env.shadow_vars with Some n -> n | None -> 0 in
    let s_l, s_k = KBindings.find v env.typ_vars in
    let s_v = Kid_aux (Var (string_of_kid v ^ "#" ^ string_of_int n), l) in
    typ_print
      ( lazy
        (Printf.sprintf "%stype variable (shadowing %s) %s : %s" adding (string_of_kid s_v) (string_of_kid v)
           (string_of_kind_aux k)
        )
        ) [@coverage off];
    ( {
        env with
        constraints = List.map (fun (l, nc) -> (l, constraint_subst v (arg_kopt (mk_kopt s_k s_v)) nc)) env.constraints;
        typ_vars = KBindings.add v (l, k) (KBindings.add s_v (s_l, s_k) env.typ_vars);
        locals = Bindings.map (fun (mut, typ) -> (mut, typ_subst v (arg_kopt (mk_kopt s_k s_v)) typ)) env.locals;
        shadow_vars = KBindings.add v (n + 1) env.shadow_vars;
      },
      Some s_v
    )
  end
  else begin
    typ_print (lazy (adding ^ "type variable " ^ string_of_kid v ^ " : " ^ string_of_kind_aux k)) [@coverage off];
    ({ env with typ_vars = KBindings.add v (l, k) env.typ_vars }, None)
  end

let add_typ_var l kopt env = fst (add_typ_var_shadow l kopt env)

let get_typ_var_loc_opt kid env = match KBindings.find_opt kid env.typ_vars with Some (l, _) -> Some l | None -> None

let get_typ_var kid env =
  try snd (KBindings.find kid env.typ_vars)
  with Not_found -> typ_error (kid_loc kid) ("No type variable " ^ string_of_kid kid)

let get_typ_vars env = KBindings.map snd env.typ_vars
let get_typ_var_locs env = KBindings.map fst env.typ_vars

let get_typ_vars_info env = { vars = env.typ_vars; shadows = env.shadow_vars }

let lookup_typ_var v tv_info = match KBindings.find_opt v tv_info.vars with Some v -> Some v | None -> None

let is_shadowed v tv_info = match KBindings.find_opt v tv_info.shadows with Some _ -> true | None -> false

let k_counter = ref 0
let k_name () =
  let kid = mk_kid ("k#" ^ string_of_int !k_counter) in
  incr k_counter;
  kid

let kinds_typq kinds = mk_typquant (List.map (fun k -> mk_qi_id k (k_name ())) kinds)

let builtin_typs =
  List.fold_left
    (fun m (name, kinds) -> Bindings.add (mk_id name) (kinds_typq kinds) m)
    Bindings.empty
    [
      ("range", [K_int; K_int]);
      ("atom", [K_int]);
      ("implicit", [K_int]);
      ("vector", [K_int; K_type]);
      ("bitvector", [K_int]);
      ("register", [K_type]);
      ("bit", []);
      ("unit", []);
      ("int", []);
      ("nat", []);
      ("bool", []);
      ("real", []);
      ("list", [K_type]);
      ("string", []);
      ("string_literal", []);
      ("itself", [K_int]);
      ("atom_bool", [K_bool]);
      ("float16", []);
      ("float32", []);
      ("float64", []);
      ("float128", []);
      ("float_rounding_mode", []);
    ]

let bound_typ_id env id =
  Bindings.mem id env.global.synonyms || Bindings.mem id env.global.unions || Bindings.mem id env.global.records
  || Bindings.mem id env.global.enums || Bindings.mem id builtin_typs
  || Bindings.mem id env.global.abstract_typs

let get_binding_loc env id =
  let find map = Some (item_loc (Bindings.find id map)) in
  if Bindings.mem id builtin_typs then None
  else if Bindings.mem id env.global.unions then find env.global.unions
  else if Bindings.mem id env.global.records then find env.global.records
  else if Bindings.mem id env.global.enums then find env.global.enums
  else if Bindings.mem id env.global.synonyms then find env.global.synonyms
  else if Bindings.mem id env.global.abstract_typs then find env.global.abstract_typs
  else None

let already_bound str id env =
  match get_binding_loc env id with
  | Some l ->
      typ_raise (id_loc id)
        (Err_inner
           ( Err_other ("Cannot create " ^ str ^ " type " ^ string_of_id id ^ ", name is already bound"),
             l,
             "",
             Some "previous binding",
             Err_other ""
           )
        )
  | None ->
      let suffix = if Bindings.mem id builtin_typs then " as a built-in type" else "" in
      typ_error (id_loc id) ("Cannot create " ^ str ^ " type " ^ string_of_id id ^ ", name is already bound" ^ suffix)

let bound_ctor_fn env id = Bindings.mem id env.global.val_specs || Bindings.mem id env.global.union_ids

let get_ctor_fn_binding_loc env id =
  if Bindings.mem id env.global.val_specs then Some (item_loc (Bindings.find id env.global.val_specs))
  else if Bindings.mem id env.global.union_ids then Some (item_loc (Bindings.find id env.global.union_ids))
  else None

let already_bound_ctor_fn str id env =
  match get_ctor_fn_binding_loc env id with
  | Some l ->
      typ_raise (id_loc id)
        (Err_inner
           ( Err_other
               ("Cannot create " ^ str ^ " " ^ string_of_id id
              ^ ", name is already bound to a union constructor or function"
               ),
             l,
             "",
             Some "previous binding",
             Err_other ""
           )
        )
  | None ->
      Reporting.unreachable (id_loc id) __POS__
        ("Could not find original binding for duplicate " ^ str ^ " called " ^ string_of_id id) [@coverage off]

let overload_item_in_scope env id =
  match Bindings.find_opt id env.global.val_specs with
  | Some item -> item_in_scope env item
  | None -> (
      match Bindings.find_opt id env.global.union_ids with
      | Some item -> item_in_scope env item
      | None -> (
          match Bindings.find_opt id env.global.overloads with
          | Some item -> item_in_scope env item
          | None ->
              Reporting.unreachable (id_loc id) __POS__ "Does not appear to be a valid overload item" [@coverage off]
        )
    )

let is_overload id env = Bindings.mem id env.global.overloads

let get_overload_locs id env = match Bindings.find_opt id env.global.overloads with Some item -> item.loc | None -> []

let get_overloads id env =
  match Bindings.find_opt id env.global.overloads with
  | None -> []
  | Some item ->
      let ids = get_item_with_loc hd_opt (id_loc id) env item in
      List.filter (overload_item_in_scope env) ids

let add_overloads l id ids env =
  typ_print
    (lazy (adding ^ "overloads for " ^ string_of_id id ^ " [" ^ string_of_list ", " string_of_id ids ^ "]"))
  [@coverage off];
  if bound_ctor_fn env id then (
    let bound_l = Option.get (get_ctor_fn_binding_loc env id) in
    typ_error
      (Hint ("Previous binding", bound_l, l))
      (string_of_id id ^ " cannot be defined as an overload, as it is already bound")
  );
  List.iter
    (fun overload ->
      if not (bound_ctor_fn env overload || Bindings.mem overload env.global.overloads) then
        typ_error
          (Hint ("unbound identifier", id_loc overload, l))
          ("Cannot create or extend overload " ^ string_of_id id ^ ", " ^ string_of_id overload ^ " is not bound")
    )
    ids;
  match Bindings.find_opt id env.global.overloads with
  | Some existing ->
      update_global
        (fun global ->
          {
            global with
            overloads =
              Bindings.add id
                (mk_item_in Project.global_scope env ~loc:(l :: item_loc existing)
                   (get_item_with_loc hd_opt l env existing @ ids)
                )
                global.overloads;
          }
        )
        env
  | None ->
      update_global
        (fun global ->
          {
            global with
            overloads = Bindings.add id (mk_item_in Project.global_scope env ~loc:[l] ids) global.overloads;
          }
        )
        env

let infer_kind env id =
  let l = id_loc id in
  if Bindings.mem id builtin_typs then Bindings.find id builtin_typs
  else if Bindings.mem id env.global.unions then fst (get_item l env (Bindings.find id env.global.unions))
  else if Bindings.mem id env.global.records then fst (get_item l env (Bindings.find id env.global.records))
  else if Bindings.mem id env.global.enums then mk_typquant []
  else if Bindings.mem id env.global.synonyms then
    typ_error (id_loc id) ("Cannot infer kind of type synonym " ^ string_of_id id)
  else if Bindings.mem id env.global.abstract_typs then mk_typquant []
  else typ_error (id_loc id) ("Cannot infer kind of " ^ string_of_id id)

let check_args_typquant id env args typq =
  let kopts, ncs = quant_split typq in
  let rec subst_args kopts args =
    match (kopts, args) with
    | kopt :: kopts, (A_aux (A_nexp _, _) as arg) :: args when is_int_kopt kopt ->
        List.map (constraint_subst (kopt_kid kopt) arg) (subst_args kopts args)
    | kopt :: kopts, A_aux (A_typ _, _) :: args when is_typ_kopt kopt -> subst_args kopts args
    | kopt :: kopts, A_aux (A_bool _, _) :: args when is_bool_kopt kopt -> subst_args kopts args
    | [], [] -> ncs
    | _, A_aux (_, l) :: _ -> typ_error l ("Error when processing type quantifer arguments " ^ string_of_typquant typq)
    | _, _ -> typ_error Parse_ast.Unknown ("Error when processing type quantifer arguments " ^ string_of_typquant typq)
  in
  let ncs = subst_args kopts args in
  if match env.prove with Some prover -> List.for_all (prover env) ncs | None -> false then ()
  else
    typ_error (id_loc id)
      ("Could not prove " ^ string_of_list ", " string_of_n_constraint ncs ^ " for type constructor " ^ string_of_id id)

let get_constraints env = List.map snd env.global.constraints @ List.map snd env.constraints

let get_constraint_reasons env = env.global.constraints @ env.constraints

let mk_synonym typq typ_arg =
  let kopts, ncs = quant_split typq in
  let kopts = List.map (fun kopt -> (kopt, fresh_existential (kopt_loc kopt) (unaux_kind (kopt_kind kopt)))) kopts in
  let ncs =
    List.map
      (fun nc -> List.fold_left (fun nc (kopt, fresh) -> constraint_subst (kopt_kid kopt) (arg_kopt fresh) nc) nc kopts)
      ncs
  in
  let typ_arg =
    List.fold_left (fun typ_arg (kopt, fresh) -> typ_arg_subst (kopt_kid kopt) (arg_kopt fresh) typ_arg) typ_arg kopts
  in
  let kopts = List.map snd kopts in
  let rec subst_args env l kopts args =
    match (kopts, args) with
    | kopt :: kopts, A_aux (A_nexp arg, _) :: args when is_int_kopt kopt ->
        let typ_arg, ncs = subst_args env l kopts args in
        ( typ_arg_subst (kopt_kid kopt) (arg_nexp arg) typ_arg,
          List.map (constraint_subst (kopt_kid kopt) (arg_nexp arg)) ncs
        )
    | kopt :: kopts, A_aux (A_typ arg, _) :: args when is_typ_kopt kopt ->
        let typ_arg, ncs = subst_args env l kopts args in
        (typ_arg_subst (kopt_kid kopt) (arg_typ arg) typ_arg, ncs)
    | kopt :: kopts, A_aux (A_bool arg, _) :: args when is_bool_kopt kopt ->
        let typ_arg, ncs = subst_args env l kopts args in
        (typ_arg_subst (kopt_kid kopt) (arg_bool arg) typ_arg, ncs)
    | [], [] -> (typ_arg, ncs)
    | kopts, args ->
        typ_error l
          ("Synonym applied to bad arguments "
          ^ Util.string_of_list ", " string_of_kinded_id kopts
          ^ Util.string_of_list ", " string_of_typ_arg args
          )
  in
  fun l env args ->
    let typ_arg, ncs = subst_args env l kopts args in
    if match env.prove with Some prover -> List.for_all (prover env) ncs | None -> false then typ_arg
    else
      typ_error l
        ("Could not prove constraints "
        ^ string_of_list ", " string_of_n_constraint ncs
        ^ " in type synonym " ^ string_of_typ_arg typ_arg ^ " with "
        ^ Util.string_of_list ", " string_of_n_constraint (get_constraints env)
        )

let get_typ_synonym id env =
  match Option.map (get_item (id_loc id) env) (Bindings.find_opt id env.global.synonyms) with
  | Some (typq, arg) -> mk_synonym typq arg
  | None -> raise Not_found

let get_typ_synonyms env = filter_items env env.global.synonyms

module Well_formedness = struct
  let wf_debug str f x exs =
    typ_debug ~level:2
      (lazy ("wf_" ^ str ^ ": " ^ f x ^ " exs: " ^ Util.string_of_list ", " string_of_kid (KidSet.elements exs)))
  [@@coverage off]

  (* Check if a type, order, n-expression or constraint is
     well-formed. Throws a type error if the type is badly formed. *)
  let rec wf_typ exs env (Typ_aux (typ_aux, l) as typ) =
    match typ_aux with
    | Typ_id id when bound_typ_id env id ->
        let typq = infer_kind env id in
        if not (Util.list_empty (quant_kopts typq)) then
          typ_error l ("Type constructor " ^ string_of_id id ^ " expected " ^ string_of_typquant typq)
        else ()
    | Typ_id id -> typ_error l ("Undefined type " ^ string_of_id id)
    | Typ_var kid -> begin
        match KBindings.find kid env.typ_vars with
        | _, K_type -> ()
        | _, k ->
            typ_error l
              ("Type variable " ^ string_of_kid kid ^ " in type " ^ string_of_typ typ ^ " is " ^ string_of_kind_aux k
             ^ " rather than Type"
              )
        | exception Not_found ->
            typ_error l ("Unbound type variable " ^ string_of_kid kid ^ " in type " ^ string_of_typ typ)
      end
    | Typ_fn (arg_typs, ret_typ) ->
        List.iter (wf_typ exs env) arg_typs;
        wf_typ exs env ret_typ
    | Typ_bidir (typ1, typ2) when unloc_typ typ1 = unloc_typ typ2 ->
        typ_error l "Bidirectional types cannot be the same on both sides"
    | Typ_bidir (typ1, typ2) ->
        wf_typ exs env typ1;
        wf_typ exs env typ2
    | Typ_tuple typs -> List.iter (wf_typ exs env) typs
    | Typ_app (id, [(A_aux (A_nexp _, _) as arg)]) when string_of_id id = "implicit" -> wf_typ_arg exs env arg
    | Typ_app (id, args) when bound_typ_id env id ->
        List.iter (wf_typ_arg exs env) args;
        check_args_typquant id env args (infer_kind env id)
    | Typ_app (id, _) -> typ_error l ("Undefined type " ^ string_of_id id)
    | Typ_exist ([], _, _) -> typ_error l "Existential must have some type variables"
    | Typ_exist (kopts, nc, typ) when KidSet.is_empty exs ->
        wf_constraint (KidSet.of_list (List.map kopt_kid kopts)) env nc;
        wf_typ (KidSet.of_list (List.map kopt_kid kopts)) env typ
    | Typ_exist (_, _, _) -> typ_error l "Nested existentials are not allowed"
    | Typ_internal_unknown -> Reporting.unreachable l __POS__ "escaped Typ_internal_unknown" [@coverage off]

  and wf_typ_arg exs env (A_aux (typ_arg_aux, _)) =
    match typ_arg_aux with
    | A_nexp nexp -> wf_nexp exs env nexp
    | A_typ typ -> wf_typ exs env typ
    | A_bool nc -> wf_constraint exs env nc

  and wf_nexp exs env (Nexp_aux (nexp_aux, l) as nexp) =
    wf_debug "nexp" string_of_nexp nexp exs;
    match nexp_aux with
    | Nexp_id id when Bindings.mem id env.global.abstract_typs -> ()
    | Nexp_id id -> typ_error l ("Undefined type synonym " ^ string_of_id id)
    | Nexp_var kid when KidSet.mem kid exs -> ()
    | Nexp_var kid -> begin
        match get_typ_var kid env with
        | K_int -> ()
        | kind ->
            typ_error l
              ("Constraint is badly formed, " ^ string_of_kid kid ^ " has kind " ^ string_of_kind_aux kind
             ^ " but should have kind Int"
              )
      end
    | Nexp_constant _ -> ()
    | Nexp_app (id, nexps) ->
        let name = string_of_id id in
        (* We allow the abs, mod, and div functions that are included in the SMTLIB2 integer theory *)
        if name = "abs" || name = "mod" || name = "div" || Bindings.mem id env.global.synonyms then
          List.iter (fun n -> wf_nexp exs env n) nexps
        else typ_error l ("Unknown type level operator or function " ^ name)
    | Nexp_times (nexp1, nexp2) ->
        wf_nexp exs env nexp1;
        wf_nexp exs env nexp2
    | Nexp_sum (nexp1, nexp2) ->
        wf_nexp exs env nexp1;
        wf_nexp exs env nexp2
    | Nexp_minus (nexp1, nexp2) ->
        wf_nexp exs env nexp1;
        wf_nexp exs env nexp2
    | Nexp_exp nexp -> wf_nexp exs env nexp (* MAYBE: Could put restrictions on what is allowed here *)
    | Nexp_neg nexp -> wf_nexp exs env nexp
    | Nexp_if (i, t, e) ->
        wf_constraint exs env i;
        wf_nexp exs env t;
        wf_nexp exs env e

  and wf_constraint exs env (NC_aux (nc_aux, l) as nc) =
    wf_debug "constraint" string_of_n_constraint nc exs;
    match nc_aux with
    | NC_id id when Bindings.mem id env.global.abstract_typs -> ()
    | NC_id id -> typ_error l ("Undefined type synonym " ^ string_of_id id)
    | NC_equal (n1, n2) ->
        wf_nexp exs env n1;
        wf_nexp exs env n2
    | NC_not_equal (n1, n2) ->
        wf_nexp exs env n1;
        wf_nexp exs env n2
    | NC_bounded_ge (n1, n2) ->
        wf_nexp exs env n1;
        wf_nexp exs env n2
    | NC_bounded_gt (n1, n2) ->
        wf_nexp exs env n1;
        wf_nexp exs env n2
    | NC_bounded_le (n1, n2) ->
        wf_nexp exs env n1;
        wf_nexp exs env n2
    | NC_bounded_lt (n1, n2) ->
        wf_nexp exs env n1;
        wf_nexp exs env n2
    | NC_set (nexp, _) -> wf_nexp exs env nexp
    | NC_or (nc1, nc2) ->
        wf_constraint exs env nc1;
        wf_constraint exs env nc2
    | NC_and (nc1, nc2) ->
        wf_constraint exs env nc1;
        wf_constraint exs env nc2
    | NC_app (_, args) -> List.iter (wf_typ_arg exs env) args
    | NC_var kid when KidSet.mem kid exs -> ()
    | NC_var kid -> begin
        match get_typ_var kid env with
        | K_bool -> ()
        | kind -> typ_error l (string_of_kid kid ^ " has kind " ^ string_of_kind_aux kind ^ " but should have kind Bool")
      end
    | NC_true | NC_false -> ()
end

let add_abstract_typ id kind env =
  if bound_typ_id env id then
    typ_error (id_loc id)
      ("Cannot introduce abstract type " ^ string_of_id id ^ " as a type or synonym with that name already exists")
  else (
    typ_print (lazy (adding ^ "abstract type " ^ string_of_id id ^ " : " ^ string_of_kind kind)) [@coverage off];
    update_global
      (fun global ->
        { global with abstract_typs = Bindings.add id (mk_item env ~loc:(id_loc id) kind) global.abstract_typs }
      )
      env
  )

let get_abstract_typs env = filter_items env env.global.abstract_typs

let is_abstract_typ id env = Bindings.mem id env.global.abstract_typs

let rec expand_constraint_synonyms env (NC_aux (aux, l) as nc) =
  match aux with
  | NC_or (nc1, nc2) -> NC_aux (NC_or (expand_constraint_synonyms env nc1, expand_constraint_synonyms env nc2), l)
  | NC_and (nc1, nc2) -> NC_aux (NC_and (expand_constraint_synonyms env nc1, expand_constraint_synonyms env nc2), l)
  | NC_equal (n1, n2) -> NC_aux (NC_equal (expand_nexp_synonyms env n1, expand_nexp_synonyms env n2), l)
  | NC_not_equal (n1, n2) -> NC_aux (NC_not_equal (expand_nexp_synonyms env n1, expand_nexp_synonyms env n2), l)
  | NC_bounded_le (n1, n2) -> NC_aux (NC_bounded_le (expand_nexp_synonyms env n1, expand_nexp_synonyms env n2), l)
  | NC_bounded_lt (n1, n2) -> NC_aux (NC_bounded_lt (expand_nexp_synonyms env n1, expand_nexp_synonyms env n2), l)
  | NC_bounded_ge (n1, n2) -> NC_aux (NC_bounded_ge (expand_nexp_synonyms env n1, expand_nexp_synonyms env n2), l)
  | NC_bounded_gt (n1, n2) -> NC_aux (NC_bounded_gt (expand_nexp_synonyms env n1, expand_nexp_synonyms env n2), l)
  | NC_app (id, args) -> (
      try
        begin
          match get_typ_synonym id env l env args with
          | A_aux (A_bool nc, _) -> expand_constraint_synonyms env nc
          | arg ->
              typ_error l ("Expected Bool when expanding synonym " ^ string_of_id id ^ " got " ^ string_of_typ_arg arg)
        end
      with Not_found -> NC_aux (NC_app (id, List.map (expand_arg_synonyms env) args), l)
    )
  | NC_id id -> (
      try
        begin
          match get_typ_synonym id env l env [] with
          | A_aux (A_bool nc, _) -> expand_constraint_synonyms env nc
          | arg ->
              typ_error l ("Expected Bool when expanding synonym " ^ string_of_id id ^ " got " ^ string_of_typ_arg arg)
        end
      with Not_found -> nc
    )
  | NC_true | NC_false | NC_var _ | NC_set _ -> nc

and expand_nexp_synonyms env (Nexp_aux (aux, l) as nexp) =
  match aux with
  | Nexp_app (id, args) -> (
      try
        begin
          match get_typ_synonym id env l env (List.map arg_nexp args) with
          | A_aux (A_nexp nexp, _) -> expand_nexp_synonyms env nexp
          | _ -> typ_error l ("Expected Int when expanding synonym " ^ string_of_id id)
        end
      with Not_found -> Nexp_aux (Nexp_app (id, List.map (expand_nexp_synonyms env) args), l)
    )
  | Nexp_id id -> (
      try
        begin
          match get_typ_synonym id env l env [] with
          | A_aux (A_nexp nexp, _) -> expand_nexp_synonyms env nexp
          | _ -> typ_error l ("Expected Int when expanding synonym " ^ string_of_id id)
        end
      with Not_found -> nexp
    )
  | Nexp_times (nexp1, nexp2) ->
      Nexp_aux (Nexp_times (expand_nexp_synonyms env nexp1, expand_nexp_synonyms env nexp2), l)
  | Nexp_sum (nexp1, nexp2) -> Nexp_aux (Nexp_sum (expand_nexp_synonyms env nexp1, expand_nexp_synonyms env nexp2), l)
  | Nexp_minus (nexp1, nexp2) ->
      Nexp_aux (Nexp_minus (expand_nexp_synonyms env nexp1, expand_nexp_synonyms env nexp2), l)
  | Nexp_exp nexp -> Nexp_aux (Nexp_exp (expand_nexp_synonyms env nexp), l)
  | Nexp_neg nexp -> Nexp_aux (Nexp_neg (expand_nexp_synonyms env nexp), l)
  | Nexp_var kid -> Nexp_aux (Nexp_var kid, l)
  | Nexp_constant n -> Nexp_aux (Nexp_constant n, l)
  | Nexp_if (i, t, e) ->
      Nexp_aux (Nexp_if (expand_constraint_synonyms env i, expand_nexp_synonyms env t, expand_nexp_synonyms env e), l)

and expand_synonyms env (Typ_aux (typ, l)) =
  match typ with
  | Typ_internal_unknown -> Typ_aux (Typ_internal_unknown, l)
  | Typ_tuple typs -> Typ_aux (Typ_tuple (List.map (expand_synonyms env) typs), l)
  | Typ_fn (arg_typs, ret_typ) ->
      Typ_aux (Typ_fn (List.map (expand_synonyms env) arg_typs, expand_synonyms env ret_typ), l)
  | Typ_bidir (typ1, typ2) -> Typ_aux (Typ_bidir (expand_synonyms env typ1, expand_synonyms env typ2), l)
  | Typ_app (id, args) -> (
      try
        begin
          match get_typ_synonym id env l env args with
          | A_aux (A_typ typ, _) -> expand_synonyms env typ
          | _ -> typ_error l ("Expected Type when expanding synonym " ^ string_of_id id)
        end
      with Not_found -> Typ_aux (Typ_app (id, List.map (expand_arg_synonyms env) args), l)
    )
  | Typ_id id -> (
      try
        begin
          match get_typ_synonym id env l env [] with
          | A_aux (A_typ typ, _) -> expand_synonyms env typ
          | _ -> typ_error l ("Expected Type when expanding synonym " ^ string_of_id id)
        end
      with Not_found -> Typ_aux (Typ_id id, l)
    )
  | Typ_exist (kopts, nc, typ) ->
      let nc = expand_constraint_synonyms env nc in

      (* When expanding an existential synonym we need to take care
         to add the type variables and constraints to the
         environment, so we can check constraints attached to type
         synonyms within the existential. Furthermore, we must take
         care to avoid clobbering any existing type variables in
         scope while doing this. *)
      let rebindings = ref [] in

      let rename_kopt (KOpt_aux (KOpt_kind (k, kid), l) as kopt) =
        if KBindings.mem kid env.typ_vars then KOpt_aux (KOpt_kind (k, prepend_kid "syn#" kid), l) else kopt
      in
      let add_typ_var env (KOpt_aux (KOpt_kind (k, kid), l)) =
        try
          let l, _ = KBindings.find kid env.typ_vars in
          rebindings := kid :: !rebindings;
          { env with typ_vars = KBindings.add (prepend_kid "syn#" kid) (l, unaux_kind k) env.typ_vars }
        with Not_found -> { env with typ_vars = KBindings.add kid (l, unaux_kind k) env.typ_vars }
      in

      let env = List.fold_left add_typ_var env kopts in
      let kopts = List.map rename_kopt kopts in
      let nc =
        List.fold_left (fun nc kid -> constraint_subst kid (arg_nexp (nvar (prepend_kid "syn#" kid))) nc) nc !rebindings
      in
      let typ =
        List.fold_left (fun typ kid -> typ_subst kid (arg_nexp (nvar (prepend_kid "syn#" kid))) typ) typ !rebindings
      in
      let env = add_constraint nc env in
      Typ_aux (Typ_exist (kopts, nc, expand_synonyms env typ), l)
  | Typ_var v -> Typ_aux (Typ_var v, l)

and expand_arg_synonyms env (A_aux (typ_arg, l)) =
  match typ_arg with
  | A_typ typ -> A_aux (A_typ (expand_synonyms env typ), l)
  | A_bool nc -> A_aux (A_bool (expand_constraint_synonyms env nc), l)
  | A_nexp nexp -> A_aux (A_nexp (expand_nexp_synonyms env nexp), l)

and add_constraint ?(global = false) ?reason constr env =
  let (NC_aux (nc_aux, l) as constr) = constraint_simp (expand_constraint_synonyms env constr) in
  Well_formedness.wf_constraint KidSet.empty env constr;
  let power_vars = constraint_power_variables constr in
  if KidSet.cardinal power_vars > 1 && !opt_smt_linearize then
    typ_error l
      ("Cannot add constraint " ^ string_of_n_constraint constr
     ^ " where more than two variables appear within an exponential"
      )
  else if KidSet.cardinal power_vars = 1 && !opt_smt_linearize then (
    let v = KidSet.choose power_vars in
    let constrs = List.fold_left nc_and nc_true (get_constraints env) in
    begin
      match Constraint.solve_all_smt l (get_abstract_typs env) constrs v with
      | Some solutions ->
          typ_print
            ( lazy
              (Util.("Linearizing " |> red |> clear)
              ^ string_of_n_constraint constr ^ " for " ^ string_of_kid v ^ " in "
              ^ Util.string_of_list ", " Big_int.to_string solutions
              )
              ) [@coverage off];
          let linearized =
            List.fold_left
              (fun c s ->
                nc_or c (nc_and (nc_eq (nvar v) (nconstant s)) (constraint_subst v (arg_nexp (nconstant s)) constr))
              )
              nc_false solutions
          in
          typ_print (lazy (adding ^ "constraint " ^ string_of_n_constraint linearized)) [@coverage off];
          { env with constraints = (reason, linearized) :: env.constraints }
      | None ->
          typ_error l
            ("Type variable " ^ string_of_kid v ^ " must have a finite number of solutions to add "
           ^ string_of_n_constraint constr
            )
    end
  )
  else (
    match nc_aux with
    | NC_true -> env
    | _ ->
        typ_print (lazy (adding ^ "constraint " ^ string_of_n_constraint constr)) [@coverage off];
        if global then
          update_global
            (fun global_env -> { global_env with constraints = (reason, constr) :: global_env.constraints })
            env
        else { env with constraints = (reason, constr) :: env.constraints }
  )

let wf_typ ~at:at_l env (Typ_aux (_, l) as typ) =
  let typ = expand_synonyms env typ in
  Well_formedness.wf_debug "typ" string_of_typ typ KidSet.empty;
  incr depth;
  try
    Well_formedness.wf_typ KidSet.empty env typ;
    decr depth
  with Type_error (err_l, err) ->
    decr depth;
    let extra, l = match l with Parse_ast.Unknown -> (" here", at_l) | _ -> ("", l) in
    typ_raise l (err_because (Err_other ("Well-formedness check failed for type" ^ extra), err_l, err))

let wf_constraint ~at:at_l env (NC_aux (_, l) as nc) =
  let nc = expand_constraint_synonyms env nc in
  Well_formedness.wf_debug "constraint" string_of_n_constraint nc KidSet.empty;
  incr depth;
  try
    Well_formedness.wf_constraint KidSet.empty env nc;
    decr depth
  with Type_error (err_l, err) ->
    decr depth;
    let extra, l = match l with Parse_ast.Unknown -> (" here", at_l) | _ -> ("", l) in
    typ_raise l (err_because (Err_other ("Well-formedness check failed for constraint" ^ extra), err_l, err))

let add_typquant l quant env =
  let rec add_quant_item env = function QI_aux (qi, _) -> add_quant_item_aux env qi
  and add_quant_item_aux env = function
    | QI_constraint constr -> add_constraint constr env
    | QI_id kopt -> add_typ_var l kopt env
  in
  match quant with
  | TypQ_aux (TypQ_no_forall, _) -> env
  | TypQ_aux (TypQ_tq quants, _) -> List.fold_left add_quant_item env quants

let add_typ_synonym id typq arg env =
  if bound_typ_id env id then
    typ_error (id_loc id)
      ("Cannot define type synonym " ^ string_of_id id ^ ", as a type or synonym with that name already exists")
  else (
    let typq =
      quant_map_items
        (function
          | QI_aux (QI_constraint nexp, aux) -> QI_aux (QI_constraint (expand_constraint_synonyms env nexp), aux)
          | quant_item -> quant_item
          )
        typq
    in
    typ_print
      ( lazy
        (adding ^ "type synonym " ^ string_of_id id ^ ", " ^ string_of_typquant typq ^ " = " ^ string_of_typ_arg arg)
        ) [@coverage off];
    update_global
      (fun global ->
        {
          global with
          synonyms =
            Bindings.add id
              (mk_item env ~loc:(id_loc id) (typq, expand_arg_synonyms (add_typquant (id_loc id) typq env) arg))
              global.synonyms;
        }
      )
      env
  )

let get_val_spec_orig id env =
  try get_item (id_loc id) env (Bindings.find id env.global.val_specs)
  with Not_found -> typ_error (id_loc id) ("No function type found for " ^ string_of_id id)

let get_val_spec_opt id env =
  match Bindings.find_opt id env.global.val_specs with
  | Some item ->
      let bind = get_item (id_loc id) env item in
      typ_debug
        ( lazy
          ("get_val_spec: Env has "
          ^ string_of_list ", "
              (fun (kid, (_, k)) -> string_of_kid kid ^ " => " ^ string_of_kind_aux k)
              (KBindings.bindings env.typ_vars)
          )
          ) [@coverage off];
      let bind' =
        List.fold_left (fun bind (kid, _) -> freshen_kid env kid bind) bind (KBindings.bindings env.typ_vars)
      in
      typ_debug (lazy ("get_val_spec: freshened to " ^ string_of_bind bind')) [@coverage off];
      Some (bind', item.loc)
  | None -> None

let get_val_spec id env =
  match get_val_spec_opt id env with
  | Some (bind, _) -> bind
  | None ->
      (* Try to find the most similar function name, within reason, to include in the error *)
      let closest = ref (Int.max_int, None) in
      Bindings.iter
        (fun other_id item ->
          let id_str = string_of_id id in
          let other_str = string_of_id other_id in
          if abs (String.length id_str - String.length other_str) <= 2 then (
            let distance = Util.levenshtein_distance ~osa:true id_str other_str in
            let max_distance = min 4 (max 1 (String.length id_str - 3)) in
            if distance <= max_distance && distance < fst !closest then closest := (distance, Some other_str)
          )
        )
        env.global.val_specs;
      let hint_msg = match snd !closest with Some other_str -> "\n\nDid you mean " ^ other_str ^ "?" | None -> "" in
      typ_error (id_loc id) ("No function type found for " ^ string_of_id id ^ hint_msg)

let get_val_specs env = filter_items env env.global.val_specs

let add_union_id ?in_module id bind env =
  if bound_ctor_fn env id then already_bound_ctor_fn "union constructor" id env
  else (
    typ_print (lazy (adding ^ "union identifier " ^ string_of_id id ^ " : " ^ string_of_bind bind)) [@coverage off];
    update_global
      (fun global ->
        {
          global with
          union_ids = Bindings.add id (mk_item_in_opt in_module env ~loc:(id_loc id) bind) global.union_ids;
        }
      )
      env
  )

let get_union_id id env =
  match Option.map (get_item (id_loc id) env) (Bindings.find_opt id env.global.union_ids) with
  | Some bind -> List.fold_left (fun bind (kid, _) -> freshen_kid env kid bind) bind (KBindings.bindings env.typ_vars)
  | None -> typ_error (id_loc id) ("No union constructor found for " ^ string_of_id id)

let rec valid_implicits env start = function
  | Typ_aux (Typ_app (Id_aux (Id "implicit", _), [A_aux (A_nexp (Nexp_aux (Nexp_var _, _)), _)]), l) :: rest ->
      if start then valid_implicits env true rest
      else typ_error l "Arguments are invalid, implicit arguments must come before all other arguments"
  | Typ_aux (Typ_app (Id_aux (Id "implicit", _), [A_aux (A_nexp _, l)]), _) :: _ ->
      typ_error l "Implicit argument must contain a single type variable"
  | _ :: rest -> valid_implicits env false rest
  | [] -> ()

let rec update_val_spec ?in_module id (typq, typ) env =
  let typq_env = add_typquant (id_loc id) typq env in
  begin
    match expand_synonyms typq_env typ with
    | Typ_aux (Typ_fn (arg_typs, ret_typ), l) ->
        valid_implicits env true arg_typs;

        (* We perform some canonicalisation for function types where existentials appear on the left, so
           ({'n, 'n >= 2, int('n)}, foo) -> bar
           would become
           forall 'n, 'n >= 2. (int('n), foo) -> bar
           this enforces the invariant that all things on the left of functions are 'base types' (i.e. without existentials)
        *)
        let base_args = List.map (fun typ -> destruct_exist (expand_synonyms typq_env typ)) arg_typs in
        let existential_arg typq = function
          | None -> typq
          | Some (exs, nc, _) ->
              List.fold_left (fun typq kopt -> quant_add (mk_qi_kopt kopt) typq) (quant_add (mk_qi_nc nc) typq) exs
        in
        let typq = List.fold_left existential_arg typq base_args in
        let arg_typs = List.map2 (fun typ -> function Some (_, _, typ) -> typ | None -> typ) arg_typs base_args in
        let typ = Typ_aux (Typ_fn (arg_typs, ret_typ), l) in
        typ_print (lazy (adding ^ "val " ^ string_of_id id ^ " : " ^ string_of_bind (typq, typ))) [@coverage off];
        update_global
          (fun global ->
            {
              global with
              val_specs = Bindings.add id (mk_item_in_opt in_module env ~loc:(id_loc id) (typq, typ)) global.val_specs;
            }
          )
          env
    | Typ_aux (Typ_bidir (typ1, typ2), _) ->
        let env = add_mapping id (typq, typ1, typ2) env in
        typ_print (lazy (adding ^ "mapping " ^ string_of_id id ^ " : " ^ string_of_bind (typq, typ))) [@coverage off];
        update_global
          (fun global ->
            { global with val_specs = Bindings.add id (mk_item env ~loc:(id_loc id) (typq, typ)) global.val_specs }
          )
          env
    | _ -> typ_error (id_loc id) "val definition must have a mapping or function type"
  end

and add_val_spec ?in_module ?(ignore_duplicate = false) id (bind_typq, bind_typ) env =
  if (not (Bindings.mem id env.global.val_specs)) || ignore_duplicate then
    update_val_spec ?in_module id (bind_typq, bind_typ) env
  else if ignore_duplicate then env
  else (
    let previous_loc =
      match Bindings.choose_opt (Bindings.filter (fun key _ -> Id.compare id key = 0) env.global.val_specs) with
      | Some (prev_id, _) -> id_loc prev_id
      | None -> Parse_ast.Unknown
    in
    let open Error_format in
    Reporting.format_warn ~once_from:__POS__
      ("Duplicate function type definition for " ^ string_of_id id)
      (id_loc id)
      (Seq
         [
           Line "This duplicate definition is being ignored!";
           Location ("", Some "previous definition here", previous_loc, Seq []);
         ]
      );
    env
  )

and add_outcome id (typq, typ, params, vals, outcome_env) env =
  update_global
    (fun global ->
      {
        global with
        outcomes =
          Bindings.add id
            (mk_item env ~loc:(id_loc id) (typq, typ, params, vals, outcome_env.global.val_specs))
            global.outcomes;
      }
    )
    env

and get_outcome l id env =
  match Option.map (get_item l env) (Bindings.find_opt id env.global.outcomes) with
  | Some (typq, typ, params, vals, val_specs) ->
      (typq, typ, params, vals, { empty with global = { empty_global_env with val_specs } })
  | None -> typ_error l ("Outcome " ^ string_of_id id ^ " does not exist")

and add_mapping id (typq, typ1, typ2) env =
  typ_print (lazy (adding ^ "mapping " ^ string_of_id id)) [@coverage off];
  let forwards_id = mk_id (string_of_id id ^ "_forwards") in
  let forwards_matches_id = mk_id (string_of_id id ^ "_forwards_matches") in
  let backwards_id = mk_id (string_of_id id ^ "_backwards") in
  let backwards_matches_id = mk_id (string_of_id id ^ "_backwards_matches") in
  let forwards_typ = Typ_aux (Typ_fn ([typ1], typ2), Parse_ast.Unknown) in
  let forwards_matches_typ = Typ_aux (Typ_fn ([typ1], bool_typ), Parse_ast.Unknown) in
  let backwards_typ = Typ_aux (Typ_fn ([typ2], typ1), Parse_ast.Unknown) in
  let backwards_matches_typ = Typ_aux (Typ_fn ([typ2], bool_typ), Parse_ast.Unknown) in
  let env =
    env
    |> update_global (fun global ->
           { global with mappings = Bindings.add id (mk_item env ~loc:(id_loc id) (typq, typ1, typ2)) global.mappings }
       )
    |> add_val_spec ~ignore_duplicate:true forwards_id (typq, forwards_typ)
    |> add_val_spec ~ignore_duplicate:true backwards_id (typq, backwards_typ)
    |> add_val_spec ~ignore_duplicate:true forwards_matches_id (typq, forwards_matches_typ)
    |> add_val_spec ~ignore_duplicate:true backwards_matches_id (typq, backwards_matches_typ)
  in
  let prefix_id = mk_id (string_of_id id ^ "_matches_prefix") in
  if unloc_typ typ1 = string_typ then (
    let forwards_prefix_typ =
      Typ_aux
        ( Typ_fn ([typ1], app_typ (mk_id "option") [A_aux (A_typ (tuple_typ [typ2; nat_typ]), Parse_ast.Unknown)]),
          Parse_ast.Unknown
        )
    in
    add_val_spec ~ignore_duplicate:true prefix_id (typq, forwards_prefix_typ) env
  )
  else if unloc_typ typ2 = string_typ then (
    let backwards_prefix_typ =
      Typ_aux
        ( Typ_fn ([typ2], app_typ (mk_id "option") [A_aux (A_typ (tuple_typ [typ1; nat_typ]), Parse_ast.Unknown)]),
          Parse_ast.Unknown
        )
    in
    add_val_spec ~ignore_duplicate:true prefix_id (typq, backwards_prefix_typ) env
  )
  else env

let get_outcome_instantiation env = env.global.outcome_instantiation

let add_outcome_variable l kid typ env =
  update_global
    (fun global -> { global with outcome_instantiation = KBindings.add kid (l, typ) global.outcome_instantiation })
    env

let set_outcome_typschm ~outcome_loc:l (quant, typ) env =
  { env with outcome_typschm = Some (quant, typ); toplevel = Some l }

let get_outcome_typschm_opt env = env.outcome_typschm

let define_val_spec id env =
  if IdSet.mem id env.global.defined_val_specs then
    typ_error (id_loc id) ("Function " ^ string_of_id id ^ " has already been declared")
  else update_global (fun global -> { global with defined_val_specs = IdSet.add id global.defined_val_specs }) env

let get_defined_val_specs env = env.global.defined_val_specs

let is_ctor id (Tu_aux (tu, _)) =
  match tu with Tu_ty_id (_, ctor_id) when Id.compare id ctor_id = 0 -> true | _ -> false

let union_constructor_info id env =
  let type_unions = List.map (fun (id, { item = _, tus; _ }) -> (id, tus)) (Bindings.bindings env.global.unions) in
  Util.find_map
    (fun (union_id, tus) ->
      Option.map (fun (n, tu) -> (n, List.length tus, union_id, tu)) (Util.find_index_opt (is_ctor id) tus)
    )
    type_unions

let is_union_constructor id env =
  Bindings.exists (fun _ { item = _, tus; _ } -> List.exists (is_ctor id) tus) env.global.unions

let is_singleton_union_constructor id env =
  let type_unions = List.map (fun (_, { item = _, tus; _ }) -> tus) (Bindings.bindings env.global.unions) in
  match List.find (List.exists (is_ctor id)) type_unions with l -> List.length l = 1 | exception Not_found -> false

let is_mapping id env = Bindings.mem id env.global.mappings

let add_enum' is_scattered id ids env =
  if bound_typ_id env id then already_bound "enum" id env
  else (
    typ_print (lazy (adding ^ "enum " ^ string_of_id id)) [@coverage off];
    update_global
      (fun global ->
        {
          global with
          enums = Bindings.add id (mk_item env ~loc:(id_loc id) (is_scattered, IdSet.of_list ids)) global.enums;
        }
      )
      env
  )

let add_scattered_enum id env = add_enum' true id [] env
let add_enum id ids env = add_enum' false id ids env

let add_enum_clause id member env =
  match Bindings.find_opt id env.global.enums with
  | Some item ->
      if not (item_in_scope env item) then
        typ_raise (id_loc id)
          (err_not_in_scope env (Some ("Enumeration " ^ string_of_id id ^ " is not in scope")) (Some item.loc) item)
      else (
        match item with
        | { item = true, members; _ } ->
            if IdSet.mem member members then
              typ_error (id_loc id) ("Enumeration " ^ string_of_id id ^ " already has a member " ^ string_of_id member)
            else
              update_global
                (fun global ->
                  {
                    global with
                    enums = Bindings.add id { item with item = (true, IdSet.add member members) } global.enums;
                  }
                )
                env
        | { item = false, _; loc = l; _ } ->
            typ_error
              (Parse_ast.Hint ("Declared as regular enumeration here", l, id_loc id))
              ("Enumeration " ^ string_of_id id ^ " is not scattered - cannot add a new member with 'enum clause'")
      )
  | None -> typ_error (id_loc id) ("Enumeration " ^ string_of_id id ^ " does not exist")

let get_enum_opt id env =
  match Option.map (get_item (id_loc id) env) (Bindings.find_opt id env.global.enums) with
  | Some (_, enum) -> Some (IdSet.elements enum)
  | None -> None

let get_enum id env =
  match get_enum_opt id env with
  | Some enum -> enum
  | None -> typ_error (id_loc id) ("Enumeration " ^ string_of_id id ^ " does not exist")

let get_enums env = filter_items_with snd env env.global.enums

let is_record id env = Bindings.mem id env.global.records

let get_record id env =
  match Option.map (get_item (id_loc id) env) (Bindings.find_opt id env.global.records) with
  | Some record -> record
  | None -> typ_error (id_loc id) ("Struct type " ^ string_of_id id ^ " does not exist")

let get_records env = filter_items env env.global.records

let add_record id typq fields env =
  let fields = List.map (fun (typ, id) -> (expand_synonyms env typ, id)) fields in
  if bound_typ_id env id then already_bound "struct" id env
  else (
    typ_print (lazy (adding ^ "struct " ^ string_of_id id)) [@coverage off];
    let rec record_typ_args = function
      | [] -> []
      | QI_aux (QI_id kopt, _) :: qis when is_int_kopt kopt ->
          mk_typ_arg (A_nexp (nvar (kopt_kid kopt))) :: record_typ_args qis
      | QI_aux (QI_id kopt, _) :: qis when is_typ_kopt kopt ->
          mk_typ_arg (A_typ (mk_typ (Typ_var (kopt_kid kopt)))) :: record_typ_args qis
      | _ :: qis -> record_typ_args qis
    in
    let record_typ =
      match record_typ_args (quant_items typq) with [] -> mk_id_typ id | args -> mk_typ (Typ_app (id, args))
    in
    let fold_accessors accessors (typ, field) =
      let accessor_typ = mk_typ (Typ_fn ([record_typ], typ)) in
      typ_print
        ( lazy
          (indent 1 ^ adding ^ "field accessor " ^ string_of_id id ^ "." ^ string_of_id field ^ " :: "
          ^ string_of_bind (typq, accessor_typ)
          )
          ) [@coverage off];
      IdPairMap.add (id, field) (mk_item env ~loc:(id_loc field) (typq, accessor_typ)) accessors
    in
    update_global
      (fun global ->
        {
          global with
          records = Bindings.add id (mk_item env ~loc:(id_loc id) (typq, fields)) global.records;
          accessors = List.fold_left fold_accessors global.accessors fields;
        }
      )
      env
  )

let get_accessor_fn record_id field env =
  let freshen_bind bind =
    List.fold_left (fun bind (kid, _) -> freshen_kid env kid bind) bind (KBindings.bindings env.typ_vars)
  in
  try freshen_bind (get_item (id_loc field) env (IdPairMap.find (record_id, field) env.global.accessors))
  with Not_found ->
    typ_error (id_loc field) ("No field accessor found for " ^ string_of_id record_id ^ "." ^ string_of_id field)

let get_accessor record_id field env =
  match get_accessor_fn record_id field env with
  (* All accessors should have a single argument (the record itself) *)
  | typq, Typ_aux (Typ_fn ([record_typ], field_typ), _) -> (typq, record_typ, field_typ)
  | _ ->
      typ_error (id_loc field)
        ("Field accessor with non-function type found for " ^ string_of_id record_id ^ "." ^ string_of_id field)

let is_mutable id env =
  let to_bool = function Mutable -> true | Immutable -> false in
  match Bindings.find_opt id env.locals with Some (mut, _) -> to_bool mut | None -> false

let string_of_mtyp (mut, typ) =
  match mut with Immutable -> string_of_typ typ | Mutable -> "ref<" ^ string_of_typ typ ^ ">"

let add_local id mtyp env =
  if not env.allow_bindings then typ_error (id_loc id) "Bindings are not allowed in this context";
  wf_typ ~at:(id_loc id) env (snd mtyp);
  if Bindings.mem id env.global.val_specs then
    typ_error (id_loc id) ("Local variable " ^ string_of_id id ^ " is already bound as a function name")
  else ();
  typ_print (lazy (adding ^ "local binding " ^ string_of_id id ^ " : " ^ string_of_mtyp mtyp)) [@coverage off];
  { env with locals = Bindings.add id mtyp env.locals }

(* Promote a set of identifiers from local bindings to top-level global letbindings *)
let add_toplevel_lets ids (env : env) =
  IdSet.fold
    (fun id (env : env) ->
      match Bindings.find_opt id env.locals with
      | Some (_, typ) ->
          let env = { env with locals = Bindings.remove id env.locals } in
          update_global
            (fun global -> { global with letbinds = Bindings.add id (mk_item env ~loc:(id_loc id) typ) global.letbinds })
            env
      | None -> env
    )
    ids env

let get_toplevel_lets env = Bindings.bindings env.global.letbinds |> List.map fst |> IdSet.of_list

let is_variant id env = Bindings.mem id env.global.unions

let add_variant id (typq, constructors) env =
  let constructors =
    List.map
      (fun (Tu_aux (Tu_ty_id (typ, id), def_annot)) ->
        Tu_aux (Tu_ty_id (expand_synonyms (add_typquant def_annot.loc typq env) typ, id), def_annot)
      )
      constructors
  in
  if bound_typ_id env id then already_bound "union" id env
  else (
    typ_print (lazy (adding ^ "variant " ^ string_of_id id)) [@coverage off];
    update_global
      (fun global ->
        { global with unions = Bindings.add id (mk_item env ~loc:(id_loc id) (typq, constructors)) global.unions }
      )
      env
  )

let add_scattered_variant id typq env =
  if bound_typ_id env id then already_bound "scattered union" id env
  else (
    typ_print (lazy (adding ^ "scattered variant " ^ string_of_id id)) [@coverage off];
    update_global
      (fun global ->
        {
          global with
          unions = Bindings.add id (mk_item env ~loc:(id_loc id) (typq, [])) global.unions;
          scattered_union_envs = Bindings.add id env.global global.scattered_union_envs;
        }
      )
      env
  )

let add_variant_clause id tu env =
  match Bindings.find_opt id env.global.unions with
  | Some ({ item = typq, tus; _ } as item) ->
      update_global
        (fun global -> { global with unions = Bindings.add id { item with item = (typq, tus @ [tu]) } global.unions })
        env
  | None -> typ_error (id_loc id) ("scattered union " ^ string_of_id id ^ " not found")

let get_variants env = filter_items env env.global.unions

let get_variant id env =
  match Option.map (get_item (id_loc id) env) (Bindings.find_opt id env.global.unions) with
  | Some (typq, tus) -> (typq, tus)
  | None -> typ_error (id_loc id) ("union " ^ string_of_id id ^ " not found")

let get_scattered_variant_env id env =
  match Bindings.find_opt id env.global.scattered_union_envs with
  | Some global_env -> { env with global = global_env }
  | None -> typ_error (id_loc id) ("scattered union " ^ string_of_id id ^ " has not been declared")

let set_scattered_variant_env ~variant_env id env =
  update_global
    (fun global -> { global with scattered_union_envs = Bindings.add id variant_env.global global.scattered_union_envs })
    env

let is_register id env = Bindings.mem id env.global.registers

let get_register id env =
  match Option.map (get_item (id_loc id) env) (Bindings.find_opt id env.global.registers) with
  | Some typ -> typ
  | None -> typ_error (id_loc id) ("No register binding found for " ^ string_of_id id)

let get_registers env = filter_items env env.global.registers

let is_extern id env backend =
  try not (Ast_util.extern_assoc backend (Bindings.find_opt id env.global.externs) = None) with Not_found -> false

let add_extern id ext env =
  update_global (fun global -> { global with externs = Bindings.add id ext global.externs }) env

let get_extern id env backend =
  try
    match Ast_util.extern_assoc backend (Bindings.find_opt id env.global.externs) with
    | Some ext -> ext
    | None -> typ_error (id_loc id) ("No extern binding found for " ^ string_of_id id)
  with Not_found -> typ_error (id_loc id) ("No extern binding found for " ^ string_of_id id)

let add_register id typ env =
  wf_typ ~at:(id_loc id) env typ;
  if Bindings.mem id env.global.registers then
    typ_error (id_loc id) ("Register " ^ string_of_id id ^ " is already bound")
  else (
    typ_print (lazy (adding ^ "register binding " ^ string_of_id id ^ " :: " ^ string_of_typ typ)) [@coverage off];
    update_global
      (fun global -> { global with registers = Bindings.add id (mk_item env ~loc:(id_loc id) typ) global.registers })
      env
  )

let get_locals env =
  Bindings.fold
    (fun id { item = typ; _ } locals ->
      if not (Bindings.mem id locals) then Bindings.add id (Immutable, typ) locals else locals
    )
    env.global.letbinds env.locals

let lookup_id id env =
  match Bindings.find_opt id env.locals with
  | Some (mut, typ) -> Local (mut, typ)
  | None -> (
      match Option.map (get_item (id_loc id) env) (Bindings.find_opt id env.global.letbinds) with
      | Some typ -> Local (Immutable, typ)
      | None -> (
          match Option.map (get_item (id_loc id) env) (Bindings.find_opt id env.global.registers) with
          | Some typ -> Register typ
          | None -> (
              match
                List.find_opt
                  (fun (_, { item = _, ctors; _ }) -> IdSet.mem id ctors)
                  (Bindings.bindings env.global.enums)
              with
              | Some (enum_id, item) ->
                  if item_in_scope env item then Enum (mk_typ (Typ_id enum_id))
                  else (
                    let enum_name = string_of_id enum_id in
                    typ_raise (id_loc id)
                      (err_not_in_scope env
                         (Some ("Enumeration " ^ enum_name ^ " containing " ^ string_of_id id ^ " is not in scope"))
                         (Some item.loc) item
                      )
                  )
              | None -> Unbound id
            )
        )
    )

let get_ret_typ env = env.ret_typ

let add_ret_typ typ env = { env with ret_typ = Some typ }

let no_bindings env = { env with allow_bindings = false }

let get_default_order env =
  match env.global.default_order with
  | None -> typ_error Parse_ast.Unknown "No default order has been set"
  | Some ord -> ord

let get_default_order_opt env = env.global.default_order

let set_default_order o env =
  match o with
  | Ord_aux (_, l) -> (
      match env.global.default_order with
      | None -> update_global (fun global -> { global with default_order = Some o }) env
      | Some _ -> typ_error l "Cannot change default order once already set"
    )

let base_typ_of env typ =
  let rec aux (Typ_aux (t, a)) =
    let rewrap t = Typ_aux (t, a) in
    match t with
    | Typ_fn (arg_typs, ret_typ) -> rewrap (Typ_fn (List.map aux arg_typs, aux ret_typ))
    | Typ_tuple ts -> rewrap (Typ_tuple (List.map aux ts))
    | Typ_app (r, [A_aux (A_typ rtyp, _)]) when string_of_id r = "register" -> aux rtyp
    | Typ_app (id, targs) -> rewrap (Typ_app (id, List.map aux_arg targs))
    | t -> rewrap t
  and aux_arg (A_aux (targ, a)) =
    let rewrap targ = A_aux (targ, a) in
    match targ with A_typ typ -> rewrap (A_typ (aux typ)) | targ -> rewrap targ
  in
  aux (expand_synonyms env typ)

let is_bitfield id env = Bindings.mem id env.global.bitfields

let get_bitfield id env =
  match Option.map (get_item (id_loc id) env) (Bindings.find_opt id env.global.bitfields) with
  | Some bitfield -> bitfield
  | None -> typ_error (id_loc id) ("Could not find bitfield " ^ string_of_id id)

let add_bitfield id typ ranges env =
  update_global
    (fun global ->
      { global with bitfields = Bindings.add id (mk_item env ~loc:(id_loc id) (typ, ranges)) global.bitfields }
    )
    env

let is_toplevel env = env.toplevel
