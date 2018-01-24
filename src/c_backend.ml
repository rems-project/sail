(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

open Ast
open Ast_util
open Type_check
open PPrint
module Big_int = Nat_big_num

let zencode_id = function
  | Id_aux (Id str, l) -> Id_aux (Id (Util.zencode_string str), l)
  | Id_aux (DeIid str, l) -> Id_aux (Id (Util.zencode_string ("op " ^ str)), l)

let lvar_typ = function
  | Local (_, typ) -> typ
  | Register typ -> typ
  | _ -> assert false
                                    
type aexp =
  | AE_val of aval
  | AE_app of id * aval list * typ
  | AE_cast of aexp * typ
  | AE_assign of id * aexp
  | AE_let of id * aexp * aexp * typ
  | AE_block of aexp list * aexp * typ
  | AE_return of aval * typ

and aval =
  | AV_lit of lit * typ
  | AV_id of id * Type_check.lvar
  | AV_tuple of aval list
  | AV_C_fragment of string * typ

let rec map_aval f = function
  | AE_val v -> AE_val (f v)
  | AE_cast (aexp, typ) -> AE_cast (map_aval f aexp, typ)
  | AE_assign (id, aexp) -> AE_assign (id, map_aval f aexp)
  | AE_app (id, vs, typ) -> AE_app (id, List.map f vs, typ)
  | AE_let (id, aexp1, aexp2, typ) -> AE_let (id, map_aval f aexp1, map_aval f aexp2, typ)
  | AE_block (aexps, aexp, typ) -> AE_block (List.map (map_aval f) aexps, map_aval f aexp, typ)
  | AE_return (aval, typ) -> AE_return (f aval, typ)

let rec map_functions f = function
  | AE_app (id, vs, typ) -> f id vs typ
  | AE_cast (aexp, typ) -> AE_cast (map_functions f aexp, typ)
  | AE_assign (id, aexp) -> AE_assign (id, map_functions f aexp)
  | AE_let (id, aexp1, aexp2, typ) -> AE_let (id, map_functions f aexp1, map_functions f aexp2, typ)
  | AE_block (aexps, aexp, typ) -> AE_block (List.map (map_functions f) aexps, map_functions f aexp, typ)
  | AE_val _ | AE_return _ as v -> v

let pp_id ?color:(color=Util.green) id =
  string (string_of_id id |> color |> Util.clear)

let pp_lvar lvar doc =
  match lvar with
  | Register typ ->
     string "[R/" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Local (Mutable, typ) ->
     string "[M/" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Local (Immutable, typ) ->
     string "[I/" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Enum typ ->
     string "[E/" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Union (typq, typ) ->
     string "[U/" ^^ string (string_of_typquant typq ^ "/" ^ string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Unbound -> string "[?]" ^^ doc

let pp_annot typ doc =
  string "[" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc

let rec pp_aexp = function
  | AE_val v -> pp_aval v
  | AE_cast (aexp, typ) ->
     pp_annot typ (string "$" ^^ pp_aexp aexp)
  | AE_assign (id, aexp) ->
     pp_id id ^^ string " := " ^^ pp_aexp aexp
  | AE_app (id, args, typ) ->
     pp_annot typ (pp_id ~color:Util.red id ^^ parens (separate_map (comma ^^ space) pp_aval args))
  | AE_let (id, binding, body, typ) -> group
     begin
       match binding with
       | AE_let _ ->
          (pp_annot typ (separate space [string "let"; pp_id id; string "="])
           ^^ hardline ^^ nest 2 (pp_aexp binding))
          ^^ hardline ^^ string "in" ^^ space ^^ pp_aexp body
       | _ ->
          pp_annot typ (separate space [string "let"; pp_id id; string "="; pp_aexp binding; string "in"])
          ^^ hardline ^^ pp_aexp body
     end
  | AE_block (aexps, aexp, typ) ->
     pp_annot typ (surround 2 0 lbrace (pp_block (aexps @ [aexp])) rbrace)
  | AE_return (v, typ) -> pp_annot typ (string "return" ^^ parens (pp_aval v))

and pp_block = function
  | [] -> string "()"
  | [aexp] -> pp_aexp aexp
  | aexp :: aexps -> pp_aexp aexp ^^ semi ^^ hardline ^^ pp_block aexps

and pp_aval = function
  | AV_lit (lit, typ) -> pp_annot typ (string (string_of_lit lit))
  | AV_id (id, lvar) -> pp_lvar lvar (pp_id id)
  | AV_tuple avals -> parens (separate_map (comma ^^ space) pp_aval avals)
  | AV_C_fragment (str, typ) -> pp_annot typ (string (str |> Util.cyan |> Util.clear))

let ae_lit lit typ = AE_val (AV_lit (lit, typ))

let gensym_counter = ref 0

let gensym () =
  let id = mk_id ("v" ^ string_of_int !gensym_counter) in
  incr gensym_counter;
  id

let rec split_block = function
  | [exp] -> [], exp
  | exp :: exps ->
     let exps, last = split_block exps in
     exp :: exps, last
  | [] -> failwith "empty block"

let rec anf (E_aux (e_aux, _) as exp) =
  let to_aval = function
    | AE_val v -> (v, fun x -> x)
    | AE_app (_, _, typ) | AE_let (_, _, _, typ) | AE_return (_, typ) | AE_cast (_, typ) as aexp ->
       let id = gensym () in
       (AV_id (id, Local (Immutable, typ)), fun x -> AE_let (id, aexp, x, typ_of exp))
  in
  match e_aux with
  | E_lit lit -> ae_lit lit (typ_of exp)

  | E_block exps ->
     let exps, last = split_block exps in
     let aexps = List.map anf exps in
     let alast = anf last in
     AE_block (aexps, alast, typ_of exp)

  | E_assign (LEXP_aux (LEXP_id id, _), exp) ->
     let aexp = anf exp in
     AE_assign (id, aexp)
              
  | E_app (id, exps) ->
     let aexps = List.map anf exps in
     let avals = List.map to_aval aexps in
     let wrap = List.fold_left (fun f g x -> f (g x)) (fun x -> x) (List.map snd avals) in
     wrap (AE_app (id, List.map fst avals, typ_of exp))

  | E_throw exp ->
     let aexp = anf exp in
     let aval, wrap = to_aval aexp in
     wrap (AE_app (mk_id "throw", [aval], unit_typ))
          
  | E_return exp ->
     let aexp = anf exp in
     let aval, wrap = to_aval aexp in
     wrap (AE_app (mk_id "return", [aval], unit_typ))
     
  | E_id id ->
     let lvar = Env.lookup_id id (env_of exp) in
     AE_val (AV_id (zencode_id id, lvar))

  | E_return exp ->
     let aval, wrap = to_aval (anf exp) in
     wrap (AE_return (aval, typ_of exp))

  | E_let (LB_aux (LB_val (P_aux (P_id id, _), binding), _), body) ->
     AE_let (zencode_id id, anf binding, anf body, typ_of exp)

  | E_tuple exps ->
     let aexps = List.map anf exps in
     let avals = List.map to_aval aexps in
     let wrap = List.fold_left (fun f g x -> f (g x)) (fun x -> x) (List.map snd avals) in
     wrap (AE_val (AV_tuple (List.map fst avals)))

  | E_cast (typ, exp) -> AE_cast (anf exp, typ)

  | E_vector_access _ | E_vector_subrange _ | E_vector_update _ | E_vector_update_subrange _ | E_vector_append _ ->
     (* Should be re-written by type checker *)
     failwith "encountered raw vector operation when converting to ANF"

  | E_internal_value _ ->
     (* Interpreter specific *)
     failwith "encountered E_internal_value when converting to ANF"

  | E_sizeof _ | E_constraint _ ->
     (* Sizeof nodes removed by sizeof rewriting pass *)
     failwith "encountered E_sizeof or E_constraint node when converting to ANF"
              
let max_int64 = Big_int.of_int64 Int64.max_int
let min_int64 = Big_int.of_int64 Int64.min_int

let stack_typ (Typ_aux (typ_aux, _) as typ) =
  match typ_aux with
  | Typ_id id when string_of_id id = "bit" -> Some "uint64_t"
  | Typ_app (id, _) when string_of_id id = "range" || string_of_id id = "atom" ->
     begin
       match destruct_range typ with
       | None -> None
       | Some (n, m) ->
          match nexp_simp n, nexp_simp m with
          | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _) ->
             if Big_int.less_equal min_int64 n && Big_int.less_equal m max_int64 then
               Some "int64_t"
             else
               None
          | _ -> None
     end
  | Typ_app (id, [Typ_arg_aux (Typ_arg_nexp n, _); _; _]) when string_of_id id = "vector" ->
     begin
       match nexp_simp n with
       | Nexp_aux (Nexp_constant n, _) when Big_int.less_equal n (Big_int.of_int 64) -> Some "uint64_t"
       | _ -> None
     end
  | _ -> None

let heap_typ (Typ_aux (typ_aux, _) as typ) =
  match typ_aux with
  | Typ_app (id, _) when string_of_id id = "range" || string_of_id id = "atom" ->
     Some "mpz_t"
  | Typ_id id when string_of_id id = "int" ->
     Some "mpz_t"
  | Typ_app (id, _) when string_of_id id = "vector" ->
     Some "sail_bv"
  | _ -> None

let is_stack_typ typ = match stack_typ typ with
  | Some _ -> true
  | None -> false

let literal_to_cstring (L_aux (l_aux, _) as lit) =
  match l_aux with
  | L_num n when Big_int.less_equal min_int64 n && Big_int.less_equal n max_int64 ->
     Some (Big_int.to_string n ^ "L")
  | L_hex str when String.length str <= 16 ->
     let padding = 16 - String.length str in
     Some ("0x" ^ String.make padding '0' ^ str ^ "ul")
  | _ -> None

let c_literals =
  let c_literal = function
    | AV_lit (lit, typ) as v ->
       begin
         match literal_to_cstring lit with
         | Some str -> AV_C_fragment (str, typ)
         | None -> v
       end
    | v -> v
  in
  map_aval c_literal

let mask m =
  if Big_int.less_equal m (Big_int.of_int 64) then
    let n = Big_int.to_int m in
    if n mod 4 == 0
    then "0x" ^ String.make (16 - n / 4) '0' ^ String.make (n / 4) 'F' ^ "ul"
    else "0b" ^ String.make (64 - n) '0' ^ String.make n '1' ^ "ul"
  else
    failwith "Tried to create a mask literal for a vector greater than 64 bits."

let c_aval = function
  | AV_lit (lit, typ) as v ->
     begin
       match literal_to_cstring lit with
       | Some str -> AV_C_fragment (str, typ)
       | None -> v
     end
  | AV_C_fragment (str, typ) -> AV_C_fragment (str, typ)
  (* An id can be converted to a C fragment if it's type can be stack-allocated. *)
  | AV_id (id, lvar) as v ->
     begin
       match lvar with
       | Local (_, typ) when is_stack_typ typ ->
          AV_C_fragment (string_of_id id, typ)
       | _ -> v
     end
  | AV_tuple avals -> AV_tuple avals

let is_c_fragment = function
  | AV_C_fragment _ -> true
  | _ -> false

let c_fragment_string = function
  | AV_C_fragment (str, _) -> str
  | _ -> assert false

let analyze_primop' id args typ =
  let no_change = AE_app (id, args, typ) in

  (* primops add_range and add_atom *)
  if string_of_id id = "add_range" || string_of_id id = "add_atom" then
    begin
      let n, m, x, y = match destruct_range typ, args with
        | Some (n, m), [x; y] -> n, m, x, y
        | _ -> failwith ("add_range has incorrect return type or arity ^ " ^ string_of_typ typ)
      in
      match nexp_simp n, nexp_simp m with
      | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _) ->
         if Big_int.less_equal min_int64 n && Big_int.less_equal m max_int64 then
           let x, y = c_aval x, c_aval y in
           if is_c_fragment x && is_c_fragment y then
             AE_val (AV_C_fragment (c_fragment_string x ^ " + " ^ c_fragment_string y, typ))
           else
             no_change
         else
           no_change
      | _ -> no_change
    end

  else if string_of_id id = "add_vec" then
    begin
      let n, x, y = match typ, args with
        | Typ_aux (Typ_app (id, [Typ_arg_aux (Typ_arg_nexp n, _); _; _]), _), [x; y]
             when string_of_id id = "vector" -> n, x, y
        | _ -> failwith ("add_vec has incorrect return type or arity " ^ string_of_typ typ)
      in
      match nexp_simp n with
      | Nexp_aux (Nexp_constant n, _) when Big_int.less_equal n (Big_int.of_int 64) ->
         let x, y = c_aval x, c_aval y in
         if is_c_fragment x && is_c_fragment y then
           AE_val (AV_C_fragment ("(" ^ c_fragment_string x ^ " + " ^ c_fragment_string y ^ ") & " ^ mask n, typ))
         else
           no_change
      | _ -> no_change
    end

  else
    no_change

let analyze_primop id args typ =
  let no_change = AE_app (id, args, typ) in
  try analyze_primop' id args typ with
  | Failure _ -> no_change

type allocation =
  | Stack of string
  | Heap of string

let string_of_allocation = function
  | Stack str -> "S$" ^ str
  | Heap str -> "H$" ^ str

let choose_allocation typ =
  match stack_typ typ with
  | Some str -> Stack str
  | None ->
     match heap_typ typ with
     | Some str -> Heap str
     | _ -> failwith "don't know where to allocate type"

type ccall =
  | CCallH of (string -> string)
  | CCallS of string
                     
let compile_funcall env id args typ =
  let setup = ref [] in
  let cleanup = ref [] in

  let _, Typ_aux (fn_typ, _) = Env.get_val_spec id env in
  let arg_typs, ret_typ = match fn_typ with
    | Typ_fn (Typ_aux (Typ_tup arg_typs, _), ret_typ, _) -> arg_typs, ret_typ
    | Typ_fn (arg_typ, ret_typ, _) -> [arg_typ], ret_typ
    | _ -> assert false
  in
  let arg_allocs = List.map choose_allocation arg_typs in
  print_endline (Util.string_of_list ", " string_of_allocation arg_allocs);

  let setup_arg alloc aval =
    match alloc, aval with
    | Heap str_h, AV_C_fragment (c, typ) ->
       let Some str_s = stack_typ typ in
       let g = gensym () in
       setup := (str_h ^ " " ^ string_of_id g ^ ";") :: !setup;
       setup := Printf.sprintf "init_%s_of_%s(%s, %s);" str_h str_s (string_of_id g) c :: !setup;
       cleanup := Printf.sprintf "clear_%s(%s);" str_h (string_of_id g) :: !cleanup;
       string_of_id g
    | Stack str_h, AV_C_fragment (c, typ) -> c
    | Heap str_h, AV_id (id, typ) ->
       begin
         match choose_allocation (lvar_typ typ) with
         | Heap _ -> string_of_id id
         | Stack str_s ->
            let g = gensym () in
            setup := (str_h ^ " " ^ string_of_id g ^ ";") :: !setup;
            setup := Printf.sprintf "init_%s_of_%s(%s, %s);" str_h str_s (string_of_id g) (string_of_id id) :: !setup;
            cleanup := Printf.sprintf "clear_%s(%s);" str_h (string_of_id g) :: !cleanup;
            string_of_id g         
       end
    | Stack str_s, AV_id (id, typ) -> string_of_id id
    | _, AV_id _ -> "AV_id"
    | _, AV_lit _ -> "AV_lit"
  in
  
  let str_args = List.map2 setup_arg arg_allocs args in

  match choose_allocation ret_typ with
  | Heap str_h ->
     let call ret = Printf.sprintf "sail_%s(%s, %s);" (string_of_id id) ret (String.concat ", " str_args) in
     (List.rev !setup, str_h, CCallH call, !cleanup)
  | Stack str_s ->
     let call = Printf.sprintf "sail_%s(%s);" (string_of_id id) (String.concat ", " str_args) in
     (List.rev !setup, str_s, CCallS call, !cleanup)
       
let rec compile_aexp env = function
  | AE_let (id, binding, body, typ) ->
     let setup, ctyp, call, cleanup = compile_aexp env binding in
     let letb1, letb1c = match call with
       | CCallH f -> f (string_of_id id), [Printf.sprintf "clear_%s(%s);" ctyp (string_of_id id)]
       | CCallS str -> string_of_id id ^ " = " ^ str, []    
     in
     let letb2 = setup @ [ctyp ^ " " ^ string_of_id id ^ ";"; letb1] @ cleanup in
     let setup, ctyp, call, cleanup = compile_aexp env body in
     letb2 @ setup, ctyp, call, cleanup @ letb1c
  
  | AE_app (id, vs, typ) ->
     compile_funcall env id vs typ

  | AE_val (AV_C_fragment (c, typ)) ->
     let Some ctyp = stack_typ typ in
     [], ctyp, CCallS c, []

let print_compiled (setup, ctyp, call, cleanup) =
  List.iter print_endline setup;
  begin match call with
  | CCallH f -> print_endline (f ("?" ^ ctyp))
  | CCallS str -> print_endline ("?" ^ ctyp ^ " = " ^ str)
  end;
  List.iter print_endline cleanup
                     
let compile_exp env exp =
  let aexp = anf exp in
  let aexp = c_literals aexp in
  let aexp = map_functions analyze_primop aexp in
  print_compiled (compile_aexp env aexp);
  aexp


(*

{
  uint64_t zx = 0x000000000000F000L;
  uint64_t v0 = (zx + 0x000000000000000FL) & 0x000000000000FFFFL;
  uint64_t res = (v0 + 0x000000000000FFFFL) & 0x000000000000FFFFL;
  return res;
}

*)
