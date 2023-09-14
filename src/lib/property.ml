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
open Ast_defs
open Ast_util
open Parser_combinators

let find_properties { defs; _ } =
  let rec find_prop acc = function
    | DEF_aux (DEF_pragma ((("property" | "counterexample") as prop_type), command, l), _) :: defs -> begin
        match Util.find_next (function DEF_aux (DEF_val _, _) -> true | _ -> false) defs with
        | _, Some (DEF_aux (DEF_val vs, _), defs) -> find_prop ((prop_type, command, l, vs) :: acc) defs
        | _, _ -> raise (Reporting.err_general l "Property is not attached to any function signature")
      end
    | def :: defs -> find_prop acc defs
    | [] -> acc
  in
  find_prop [] defs
  |> List.map (fun ((_, _, _, vs) as prop) -> (id_of_val_spec vs, prop))
  |> List.fold_left (fun m (id, prop) -> Bindings.add id prop m) Bindings.empty

let add_property_guards props ast =
  let open Type_check in
  let open Type_error in
  let rec add_property_guards' acc = function
    | (DEF_aux (DEF_fundef (FD_aux (FD_function (r_opt, t_opt, funcls), fd_aux) as fdef), def_annot) as def) :: defs ->
      begin
        match Bindings.find_opt (id_of_fundef fdef) props with
        | Some (_, _, pragma_l, VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (quant, _), _), _, _), _)) -> begin
            match quant_split quant with
            | _, [] -> add_property_guards' (def :: acc) defs
            | _, constraints ->
                let add_constraints_to_funcl (FCL_aux (FCL_funcl (id, Pat_aux (pexp, pexp_aux)), fcl_aux)) =
                  let add_guard exp =
                    (* FIXME: Use an assert *)
                    let exp' =
                      mk_exp
                        (E_block
                           [
                             mk_exp
                               (E_app
                                  ( mk_id "sail_assume",
                                    [mk_exp (E_constraint (List.fold_left nc_and nc_true constraints))]
                                  )
                               );
                             strip_exp exp;
                           ]
                        )
                    in
                    try Type_check.check_exp (env_of exp) exp' (typ_of exp)
                    with Type_error (l, err) ->
                      let msg =
                        "\n\
                         Type error when generating guard for a property.\n\
                         When generating guards we convert type quantifiers from the function signature\n\
                         into runtime checks so it must be possible to reconstruct the quantifier from\n\
                         the function arguments. For example:\n\n\
                         function f : forall 'n, 'n <= 100. (x: int('n)) -> bool\n\n\
                         would cause the runtime check x <= 100 to be added to the function body.\n\
                         To fix this error, ensure that all quantifiers have corresponding function arguments.\n"
                      in
                      raise (Reporting.err_typ pragma_l (Type_error.string_of_type_error err ^ msg))
                  in
                  let mk_funcl p = FCL_aux (FCL_funcl (id, Pat_aux (p, pexp_aux)), fcl_aux) in
                  match pexp with
                  | Pat_exp (pat, exp) -> mk_funcl (Pat_exp (pat, add_guard exp))
                  | Pat_when (pat, guard, exp) -> mk_funcl (Pat_when (pat, guard, add_guard exp))
                in

                let funcls = List.map add_constraints_to_funcl funcls in
                let fdef = FD_aux (FD_function (r_opt, t_opt, funcls), fd_aux) in

                add_property_guards' (DEF_aux (DEF_fundef fdef, def_annot) :: acc) defs
          end
        | None -> add_property_guards' (def :: acc) defs
      end
    | def :: defs -> add_property_guards' (def :: acc) defs
    | [] -> List.rev acc
  in
  { ast with defs = add_property_guards' [] ast.defs }

let rewrite defs = add_property_guards (find_properties defs) defs

type event = Overflow | Assertion | Assumption | Match | Return

type query =
  | Q_all of event (* All events of type are true *)
  | Q_exist of event (* Some event of type is true *)
  | Q_not of query
  | Q_and of query list
  | Q_or of query list

let default_query =
  Q_or
    [Q_and [Q_not (Q_exist Assertion); Q_all Return; Q_not (Q_exist Match)]; Q_exist Overflow; Q_not (Q_all Assumption)]

module Event = struct
  type t = event
  let compare e1 e2 =
    match (e1, e2) with
    | Overflow, Overflow -> 0
    | Assertion, Assertion -> 0
    | Assumption, Assumption -> 0
    | Match, Match -> 0
    | Return, Return -> 0
    | Overflow, _ -> 1
    | _, Overflow -> -1
    | Assertion, _ -> 1
    | _, Assertion -> -1
    | Assumption, _ -> 1
    | _, Assumption -> -1
    | Match, _ -> 1
    | _, Match -> -1
end

let string_of_event = function
  | Overflow -> "overflow"
  | Assertion -> "assertion"
  | Assumption -> "assumption"
  | Match -> "match_failure"
  | Return -> "return"

let rec _string_of_query = function
  | Q_all ev -> "A " ^ string_of_event ev
  | Q_exist ev -> "E " ^ string_of_event ev
  | Q_not q -> "~(" ^ _string_of_query q ^ ")"
  | Q_and qs -> "(" ^ Util.string_of_list " & " _string_of_query qs ^ ")"
  | Q_or qs -> "(" ^ Util.string_of_list " | " _string_of_query qs ^ ")"

let parse_query =
  let amp = token (function Str.Delim "&" -> Some () | _ -> None) in
  let bar = token (function Str.Delim "|" -> Some () | _ -> None) in
  let lparen = token (function Str.Delim "(" -> Some () | _ -> None) in
  let rparen = token (function Str.Delim ")" -> Some () | _ -> None) in
  let quant =
    token (function
      | Str.Text ("A" | "all") -> Some (fun x -> Q_all x)
      | Str.Text ("E" | "exist") -> Some (fun x -> Q_exist x)
      | _ -> None
      )
  in
  let event =
    token (function
      | Str.Text "overflow" -> Some Overflow
      | Str.Text "assertion" -> Some Assertion
      | Str.Text "assumption" -> Some Assumption
      | Str.Text "match_failure" -> Some Match
      | Str.Text "return" -> Some Return
      | _ -> None
      )
  in
  let tilde = token (function Str.Delim "~" -> Some () | _ -> None) in

  let rec exp0 () =
    pchoose
      ( exp1 () >>= fun x ->
        bar >>= fun _ ->
        exp0 () >>= fun y -> preturn (Q_or [x; y])
      )
      (exp1 ())
  and exp1 () =
    pchoose
      ( exp2 () >>= fun x ->
        amp >>= fun _ ->
        exp1 () >>= fun y -> preturn (Q_and [x; y])
      )
      (exp2 ())
  and exp2 () =
    pchoose
      ( tilde >>= fun _ ->
        exp3 () >>= fun x -> preturn (Q_not x)
      )
      (exp3 ())
  and exp3 () =
    pchoose
      ( lparen >>= fun _ ->
        exp0 () >>= fun x ->
        rparen >>= fun _ -> preturn x
      )
      ( quant >>= fun f ->
        event >>= fun ev -> preturn (f ev)
      )
  in
  parse (exp0 ()) "[ \n\t]+\\|(\\|)\\|&\\||\\|~"

type pragma = { query : query; litmus : string list }

let default_pragma = { query = default_query; litmus = [] }

let parse_pragma l input =
  let key = Str.regexp ":[a-z]+" in
  let tokens = Str.full_split key input in
  let rec process_toks pragma = function
    | Str.Delim ":query" :: Str.Text query :: rest -> begin
        match parse_query query with
        | Some q -> process_toks { pragma with query = q } rest
        | None -> raise (Reporting.err_general l ("Could not parse query " ^ String.trim query))
      end
    | Str.Delim ":litmus" :: rest ->
        let args, rest = Util.take_drop (function Str.Text _ -> true | _ -> false) rest in
        process_toks { pragma with litmus = List.map (function Str.Text t -> t | _ -> assert false) args } rest
    | [] -> pragma
    | _ -> raise (Reporting.err_general l "Could not parse pragma")
  in
  process_toks default_pragma tokens
