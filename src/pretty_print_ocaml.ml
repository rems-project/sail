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

open Big_int
open Type_internal
open Ast
open PPrint
open Pretty_print_common

(****************************************************************************
 * PPrint-based sail-to-ocaml pretty printer
****************************************************************************)

let star_sp = star ^^ space

let sanitize_name s = 
  "_" ^ s

let doc_id_ocaml (Id_aux(i,_)) =
  match i with
  | Id("bit") -> string "vbit"
  | Id i -> string (sanitize_name i)
  | DeIid x ->
      (* add an extra space through empty to avoid a closing-comment
       * token in case of x ending with star. *)
      parens (separate space [colon; string x; empty])

let doc_id_ocaml_type (Id_aux(i,_)) =
  match i with
  | Id("bit") -> string "vbit"
  | Id i -> string (sanitize_name i)
  | DeIid x ->
      (* add an extra space through empty to avoid a closing-comment
       * token in case of x ending with star. *)
      parens (separate space [colon; string (String.uncapitalize x); empty])

let doc_id_ocaml_ctor n (Id_aux(i,_)) =
  match i with
  | Id("bit") -> string "vbit"
  | Id i -> string ((if n > 246 then "`" else "") ^ (String.capitalize i))
  | DeIid x ->
      (* add an extra space through empty to avoid a closing-comment
       * token in case of x ending with star. *)
      parens (separate space [colon; string (String.capitalize x); empty])

let doc_typ_ocaml, doc_atomic_typ_ocaml =
  (* following the structure of parser for precedence *)
  let rec typ ty = fn_typ ty
  and fn_typ ((Typ_aux (t, _)) as ty) = match t with
  | Typ_fn(arg,ret,efct) ->
      separate space [tup_typ arg; arrow; fn_typ ret]
  | _ -> tup_typ ty
  and tup_typ ((Typ_aux (t, _)) as ty) = match t with
  | Typ_tup typs -> parens (separate_map star app_typ typs)
  | _ -> app_typ ty
  and app_typ ((Typ_aux (t, _)) as ty) = match t with
  | Typ_app(Id_aux (Id "vector", _), [
      Typ_arg_aux(Typ_arg_nexp n, _);
      Typ_arg_aux(Typ_arg_nexp m, _);
      Typ_arg_aux (Typ_arg_order ord, _);
      Typ_arg_aux (Typ_arg_typ typ, _)]) ->
    string "value"
  | Typ_app(Id_aux (Id "range", _), [
    Typ_arg_aux(Typ_arg_nexp n, _);
    Typ_arg_aux(Typ_arg_nexp m, _);]) ->
    (string "number")
  | Typ_app(Id_aux (Id "atom", _), [Typ_arg_aux(Typ_arg_nexp n,_)]) ->
    (string "number")
  | Typ_app(id,args) ->
     (separate_map space doc_typ_arg_ocaml args) ^^ space ^^ (doc_id_ocaml_type id)
  | _ -> atomic_typ ty
  and atomic_typ ((Typ_aux (t, _)) as ty) = match t with
  | Typ_id id  -> doc_id_ocaml_type id
  | Typ_var v  -> doc_var v
  | Typ_wild -> underscore
  | Typ_app _ | Typ_tup _ | Typ_fn _ ->
      (* exhaustiveness matters here to avoid infinite loops
       * if we add a new Typ constructor *)
      group (parens (typ ty))
  and doc_typ_arg_ocaml (Typ_arg_aux(t,_)) = match t with
  | Typ_arg_typ t -> app_typ t
  | Typ_arg_nexp n -> empty
  | Typ_arg_order o -> empty
  | Typ_arg_effect e -> empty
  in typ, atomic_typ

let doc_lit_ocaml in_pat (L_aux(l,_)) =
  utf8string (match l with
  | L_unit  -> "()"
  | L_zero  -> "Vzero"
  | L_one   -> "Vone"
  | L_true  -> "Vone"
  | L_false -> "Vzero"
  | L_num i -> 
     let s = string_of_int i in
     if (i >= 0) && (i <= 257) then
       "bi" ^ s
     else
       "(big_int_of_int (" ^ s ^ "))"
  | L_hex n -> "(num_to_vec " ^ ("0x" ^ n) ^ ")" (*shouldn't happen*)
  | L_bin n -> "(num_to_vec " ^ ("0b" ^ n) ^ ")" (*shouldn't happen*)
  | L_undef -> "(failwith \"undef literal not supported\")" (* XXX Undef vectors get handled with to_vec_undef. We could support undef bit but would need to check type. For the moment treat as runtime error.  *)
  | L_real   r -> r
  | L_string s -> "\"" ^ s ^ "\"")

(* typ_doc is the doc for the type being quantified *)
let doc_typquant_ocaml (TypQ_aux(tq,_)) typ_doc = typ_doc

let doc_typscm_ocaml (TypSchm_aux(TypSchm_ts(tq,t),_)) =
  (doc_typquant_ocaml tq (doc_typ_ocaml t))

(*Note: vector concatenation, literal vectors, indexed vectors, and record should
  be removed prior to pp. The latter two have never yet been seen
*)
let doc_pat_ocaml =
  let rec pat pa = app_pat pa
  and app_pat ((P_aux(p,(l,annot))) as pa) = match p with
    | P_app(id, ((_ :: _) as pats)) ->
      (match annot with
       | Base(_,Constructor n,_,_,_,_) ->
         doc_unop (doc_id_ocaml_ctor n id) (parens (separate_map comma_sp pat pats))
       | _ -> empty)
  | P_lit lit  -> doc_lit_ocaml true lit
  | P_wild -> underscore
  | P_id id -> doc_id_ocaml id
  | P_as(p,id) -> parens (separate space [pat p; string "as"; doc_id_ocaml id])
  | P_typ(typ,p) -> doc_op colon (pat p) (doc_typ_ocaml typ)
  | P_app(id,[]) ->
    (match annot with
     | Base(_,(Constructor n | Enum n),_,_,_,_) ->
       doc_id_ocaml_ctor n id
     | _ -> failwith "encountered unexpected P_app pattern")
  | P_vector pats ->
    let non_bit_print () =
      parens
        (separate space [string "VvectorR";
                         parens (separate comma_sp [squarebars (separate_map semi pat pats);
                                                    underscore;
                                                    underscore])]) in
    (match annot with
     | Base(([],t),_,_,_,_,_) ->
       if is_bit_vector t
       then parens (separate space [string "Vvector";
                                    parens (separate comma_sp [squarebars (separate_map semi pat pats);
                                                                underscore;
                                                                underscore])])
       else non_bit_print()
     | _ -> non_bit_print ())
  | P_tup pats  -> parens (separate_map comma_sp pat pats)
  | P_list pats -> brackets (separate_map semi pat pats) (*Never seen but easy in ocaml*)
  | P_record _ -> raise (Reporting_basic.err_unreachable l "unhandled record pattern")
  | P_vector_indexed _ -> raise (Reporting_basic.err_unreachable l  "unhandled vector_indexed pattern")
  | P_vector_concat _ -> raise (Reporting_basic.err_unreachable l "unhandled vector_concat pattern")
  in pat

let doc_exp_ocaml, doc_let_ocaml =
  let rec top_exp read_registers (E_aux (e, (_,annot))) =
    let exp = top_exp read_registers in
    match e with
    | E_assign((LEXP_aux(le_act,tannot) as le),e) ->
      (match annot with
       | Base(_,(Emp_local | Emp_set),_,_,_,_) ->
         (match le_act with
          | LEXP_id _ | LEXP_cast _ ->
            (*Setting local variable fully *)
            doc_op coloneq (doc_lexp_ocaml true le) (exp e)
          | LEXP_vector _ ->
            doc_op (string "<-") (doc_lexp_array_ocaml le) (exp e)
          | LEXP_vector_range _ ->
            doc_lexp_rwrite le e
          | _ -> failwith "doc_exp_ocaml E_assign: unhandled lexp"
         )
       | _ ->
         (match le_act with
          | LEXP_vector _ | LEXP_vector_range _ | LEXP_cast _ | LEXP_field _ | LEXP_id _ ->
            (doc_lexp_rwrite le e)
          | LEXP_memory _ -> (doc_lexp_fcall le e)
          | _ -> failwith "doc_exp_ocaml _: unhandled lexp"
         )
      )
    | E_vector_append(l,r) ->
      parens ((string "vector_concat ") ^^ (exp l) ^^ space ^^ (exp r))
    | E_cons(l,r) -> doc_op (group (colon^^colon)) (exp l) (exp r)
    | E_if(c,t,E_aux(E_block [], _)) ->
      parens (string "if" ^^ space ^^ string "to_bool" ^^  parens (exp c) ^/^
              string "then" ^^ space ^^ (exp t))
    | E_if(c,t,e) ->
      parens (
      string "if" ^^ space ^^ string "to_bool" ^^ parens (exp c) ^/^
      string "then" ^^ space ^^ group (exp t) ^/^
      string "else" ^^ space ^^ group (exp e))
    | E_for(id,exp1,exp2,exp3,(Ord_aux(order,_)),exp4) ->
      let var= doc_id_ocaml id in
      let (compare,next) = if order = Ord_inc then string "le_big_int",string "add_big_int" else string "ge_big_int",string "sub_big_int" in
      let by = exp exp3 in
      let stop = exp exp2 in
      (*takes over two names but doesn't require building a closure*)
      parens
        (separate space [(string "let (__stop,__by) = ") ^^ (parens (doc_op comma stop by));
                             string "in" ^/^ empty;
                             string "let rec foreach";
                             var;
                             equals;
                             string "if";
                             parens (compare ^^ space ^^ var ^^ space ^^ (string "__stop") );
                             string "then";
                             parens (exp exp4 ^^ space ^^ semi ^^ (string "foreach") ^^
                                     parens (next ^^ space ^^ var ^^ space ^^ (string "__by")));
                             string "in";
                             string "foreach";
                             exp exp1])
        (*Requires fewer introduced names but introduces a closure*)
        (*let forL = if order = Ord_inc then string "foreach_inc" else string "foreach_dec" in
          forL ^^ space ^^ (group (exp exp1)) ^^ (group (exp exp2)) ^^ (group (exp full_exp3)) ^/^
          group ((string "fun") ^^ space ^^ (doc_id id) ^^ space ^^ arrow ^/^ (exp exp4))

        (* this way requires the following OCaml declarations first

         let rec foreach_inc i stop by body =
           if i <= stop then (body i; foreach_inc (i + by) stop by body) else ()

         let rec foreach_dec i stop by body =
           if i >= stop then (body i; foreach_dec (i - by) stop by body) else ()

         *)*)
    | E_let(leb,e) -> doc_op (string "in") (let_exp leb) (exp e)
    | E_app(f,args) ->
      let call,ctor = match annot with
        | Base(_,External (Some n),_,_,_,_) -> string n,false
        | Base(_,Constructor i,_,_,_,_) -> doc_id_ocaml_ctor i f,true
        | _ -> doc_id_ocaml f,false in
      let base_print () = parens (doc_unop call (parens (separate_map comma exp args))) in
      if not(ctor)
      then base_print ()
      else (match args with
        | [] -> call
        | [arg] -> (match arg with
            | E_aux(E_lit (L_aux(L_unit,_)),_) -> call
            | _ -> base_print())
        | args ->  base_print())
    | E_vector_access(v,e) ->
      let call = (match annot with
          | Base((_,t),_,_,_,_,_) ->
            (match t.t with
             | Tid "bit" | Tabbrev(_,{t=Tid "bit"}) -> (string "bit_vector_access")
             | _ -> (string "vector_access"))
          | _ -> (string "vector_access")) in
      parens (call ^^ space ^^ exp v ^^ space ^^ exp e)
    | E_vector_subrange(v,e1,e2) ->
      parens ((string "vector_subrange") ^^ space ^^ (exp v) ^^ space ^^ (exp e1) ^^ space ^^ (exp e2))
    | E_field((E_aux(_,(_,fannot)) as fexp),id) ->
      (match fannot with
       | Base((_,{t= Tapp("register",_)}),_,_,_,_,_) |
         Base((_,{t= Tabbrev(_,{t=Tapp("register",_)})}),_,_,_,_,_)->
         let field_f = match annot with
           | Base((_,{t = Tid "bit"}),_,_,_,_,_) |
             Base((_,{t = Tabbrev(_,{t=Tid "bit"})}),_,_,_,_,_) ->
             string "get_register_field_bit"
           | _ -> string "get_register_field_vec" in
         parens (field_f ^^ space ^^ (exp fexp) ^^ space ^^ string_lit (doc_id id))
      | _ -> exp fexp ^^ dot ^^ doc_id_ocaml id)
    | E_block [] -> string "()"
    | E_block exps | E_nondet exps ->
      let exps_doc = separate_map (semi ^^ hardline) exp exps in
      surround 2 1 (string "begin") exps_doc (string "end")
    | E_id id ->
      (match annot with
      | Base((_, ({t = Tapp("reg",_)} | {t=Tabbrev(_,{t=Tapp("reg",_)})})),_,_,_,_,_) ->
        string "!" ^^ doc_id_ocaml id
      | Base((_, ({t = Tapp("register",_)} | {t=Tabbrev(_,{t=Tapp("register",_)})})),_,_,_,_,_) ->
        if read_registers
        then string "(read_register " ^^ doc_id_ocaml id ^^ string ")"
        else doc_id_ocaml id
      | Base(_,(Constructor i |Enum i),_,_,_,_) -> doc_id_ocaml_ctor i id
      | Base((_,t),Alias alias_info,_,_,_,_) ->
         (match alias_info with
         | Alias_field(reg,field) ->
           let field_f = match t.t with
             | Tid "bit" | Tabbrev(_,{t=Tid "bit"}) -> string "get_register_field_bit"
             | _ -> string "get_register_field_vec" in
           parens (separate space [field_f; string (sanitize_name reg); string_lit (string field)])
         | Alias_extract(reg,start,stop) ->
           if start = stop
           then parens (separate space [string "bit_vector_access";string (sanitize_name reg);doc_int start])
           else parens
               (separate space [string "vector_subrange"; string (sanitize_name reg); doc_int start; doc_int stop])
         | Alias_pair(reg1,reg2) ->
           parens (separate space [string "vector_concat";
                                   string (sanitize_name reg1);
                                   string (sanitize_name reg2)]))
      | _ -> doc_id_ocaml id)
    | E_lit lit -> doc_lit_ocaml false lit
    | E_cast(typ,e) ->
      (match annot with
      | Base(_,External _,_,_,_,_) ->
        if read_registers
        then parens (string "read_register" ^^ space ^^ exp e)
        else exp e
      | _ -> 
         let (Typ_aux (t,_)) = typ in
             (match t with
            | Typ_app (Id_aux (Id "vector",_), [Typ_arg_aux (Typ_arg_nexp(Nexp_aux (Nexp_constant i,_)),_);_;_;_]) ->
               parens ((concat [string "set_start";space;string (string_of_int i)]) ^//^
                           exp e)
            | Typ_var (Kid_aux (Var "length",_)) ->
               parens ((string "set_start_to_length") ^//^ exp e)
            | _ -> 
               parens (doc_op colon (group (exp e)) (doc_typ_ocaml typ)))


)
    | E_tuple exps ->
      parens (separate_map comma exp exps)
    | E_record(FES_aux(FES_Fexps(fexps,_),_)) ->
      braces (separate_map semi_sp doc_fexp fexps)
    | E_record_update(e,(FES_aux(FES_Fexps(fexps,_),_))) ->
      braces (doc_op (string "with") (exp e) (separate_map semi_sp doc_fexp fexps))
    | E_vector exps ->
      (match annot with
       | Base((_,t),_,_,_,_,_) ->
         ( match t.t with
         | Tapp("vector", [TA_nexp start; _; TA_ord order; _])
         | Tabbrev(_,{t= Tapp("vector", [TA_nexp start; _; TA_ord order; _])}) ->
           let call = if is_bit_vector t then (string "Vvector") else (string "VvectorR") in
           let dir,dir_out = match order.order with
             | Oinc -> true,"true"
             | _ -> false, "false" in
           let start = match start.nexp with
             | Nconst i -> string_of_big_int i
             | N2n(_,Some i) -> string_of_big_int i
             | _ -> if dir then "0" else string_of_int (List.length exps) in
           parens (separate space [call; parens (separate comma_sp [squarebars (separate_map semi exp exps);
                                                                   string start;
                                                                   string
                                                                   dir_out])])
         | _ -> failwith "doc_exp_ocaml E_vector: unhandled type"
         )
       | _ -> failwith "doc_exp_ocaml E_vector: unhandled annotation"
      )
    | E_vector_indexed (iexps, (Def_val_aux (default,_))) ->
      (match annot with
       | Base((_,t),_,_,_,_,_) ->
         ( match t.t with
         | Tapp("vector", [TA_nexp start; TA_nexp len; TA_ord order; _])
         | Tabbrev(_,{t= Tapp("vector", [TA_nexp start; TA_nexp len; TA_ord order; _])})
         | Tapp("reg", [TA_typ {t =Tapp("vector", [TA_nexp start; TA_nexp len; TA_ord order; _])}]) ->
           let call = if is_bit_vector t then (string "make_indexed_bitv") else (string "make_indexed_v") in
           let dir,dir_out = match order.order with
             | Oinc -> true,"true"
             | _ -> false, "false" in
           let start = match start.nexp with
             | Nconst i | N2n(_,Some i)-> string_of_big_int i
             | N2n({nexp=Nconst i},_) -> string_of_int (Util.power 2 (int_of_big_int i))
             | _ -> if dir then "0" else string_of_int (List.length iexps) in
           let size = match len.nexp with
             | Nconst i | N2n(_,Some i)-> string_of_big_int i
             | N2n({nexp=Nconst i},_) -> string_of_int (Util.power 2 (int_of_big_int i))
             | _ -> failwith "doc_exp_ocaml E_vector_indexed: unhandled size"
           in
           let default_string =
             (match default with
              | Def_val_empty -> string "None"
              | Def_val_dec e -> parens (string "Some " ^^ (exp e))) in
           let iexp (i,e) = parens (separate_map comma_sp (fun x -> x) [(doc_int i); (exp e)]) in
           parens (separate space [call;
                                   (brackets (separate_map semi iexp iexps));
                                   default_string;
                                   string start;
                                   string size;
                                   string dir_out])
         | _ -> failwith "doc_exp_ocaml E_vector_indexed: unhandled type"
         )
       | _ -> failwith "doc_exp_ocaml E_vector_indexed: unhandled annotation"
      )
  | E_vector_update(v,e1,e2) ->
    (*Has never happened to date*)
      brackets (doc_op (string "with") (exp v) (doc_op equals (exp e1) (exp e2)))
  | E_vector_update_subrange(v,e1,e2,e3) ->
    (*Has never happened to date*)
      brackets (
        doc_op (string "with") (exp v)
        (doc_op equals (exp e1 ^^ colon ^^ exp e2) (exp e3)))
  | E_list exps ->
      brackets (separate_map semi exp exps)
  | E_case(e,pexps) ->
      let opening = separate space [string "("; string "match"; top_exp false e; string "with"] in
      let cases = separate_map (break 1) doc_case pexps in
      surround 2 1 opening cases rparen
  | E_exit e ->
    separate space [string "exit"; exp e;]
  | E_return e ->
    separate space [string "begin ret := Some" ; exp e ; string "; raise Sail_return; end"]
  | E_app_infix (e1,id,e2) ->
    let call =
      match annot with
      | Base((_,t),External(Some name),_,_,_,_) -> string name
      | _ -> doc_id_ocaml id in
    parens (separate space [call; parens (separate_map comma exp [e1;e2])])
  | E_internal_let(lexp, eq_exp, in_exp) ->
    separate space [string "let";
                    doc_lexp_ocaml true lexp; (*Rewriter/typecheck should ensure this is only cast or id*)
                    equals;
                    string "ref";
                    exp eq_exp;
                    string "in";
                    exp in_exp]

  | E_internal_plet (pat,e1,e2) ->
     (separate space [(exp e1); string ">>= fun"; doc_pat_ocaml pat;arrow]) ^/^
     exp e2

  | E_internal_return (e1) ->
     separate space [string "return"; exp e1;]
  | E_assert (e1, e2) ->
     (string "assert") ^^ parens ((string "to_bool") ^^ space ^^ exp e1) (* XXX drops e2 *)
  | _ -> failwith "top_exp: unhandled expression"

  and let_exp (LB_aux(lb,_)) = match lb with
  | LB_val_explicit(ts,pat,e) ->
      prefix 2 1
        (separate space [string "let"; doc_pat_ocaml pat; equals])
        (top_exp false e)
  | LB_val_implicit(pat,e) ->
      prefix 2 1
        (separate space [string "let"; doc_pat_ocaml pat; equals])
        (top_exp false e)

  and doc_fexp (FE_aux(FE_Fexp(id,e),_)) = doc_op equals (doc_id_ocaml id) (top_exp false e)

  and doc_case (Pat_aux(Pat_exp(pat,e),_)) =
    doc_op arrow (separate space [pipe; doc_pat_ocaml pat]) (group (top_exp false e))

  and doc_lexp_ocaml top_call ((LEXP_aux(lexp,(l,annot))) as le) =
    let exp = top_exp false in
    ( match lexp with
    | LEXP_vector(v,e) -> doc_lexp_array_ocaml le
    | LEXP_vector_range(v,e1,e2) ->
      parens ((string "vector_subrange") ^^ space ^^ (doc_lexp_ocaml false v) ^^ space ^^ (exp e1) ^^ space ^^ (exp e2))
    | LEXP_field(v,id) -> (doc_lexp_ocaml false v) ^^ dot ^^ doc_id_ocaml id
    | LEXP_id id | LEXP_cast(_,id) ->
      let name = doc_id_ocaml id in
      ( match annot,top_call with
      | Base((_,{t=Tapp("reg",_)}),Emp_set,_,_,_,_),false | Base((_,{t=Tabbrev(_,{t=Tapp("reg",_)})}),Emp_set,_,_,_,_),false ->
        string "!" ^^ name
      | _ -> name
      )
    | _ -> failwith "doc_lexp_ocaml: unhandled lexp"
    )

  and doc_lexp_array_ocaml ((LEXP_aux(lexp,(l,annot))) as le) = match lexp with
    | LEXP_vector(v,e) ->
      (match annot with
       | Base((_,t),_,_,_,_,_) ->
         let t_act = match t.t with | Tapp("reg",[TA_typ t]) | Tabbrev(_,{t=Tapp("reg",[TA_typ t])}) -> t | _ -> t in
         (match t_act.t with
          | Tid "bit" | Tabbrev(_,{t=Tid "bit"}) ->
            parens ((string "get_barray") ^^ space ^^ doc_lexp_ocaml false v) ^^ dot ^^ parens ((string "int_of_big_int") ^^ space ^^ (top_exp false e))
          | _ -> parens ((string "get_varray") ^^ space ^^ doc_lexp_ocaml false v) ^^ dot ^^ parens ((string "int_of_big_int") ^^ space ^^ (top_exp false e)))
       | _ ->
         parens ((string "get_varray") ^^ space ^^ doc_lexp_ocaml false v) ^^ dot ^^ parens ((string "int_of_big_int") ^^ space ^^ (top_exp false e)))
    | _ -> empty

  and doc_lexp_rwrite ((LEXP_aux(lexp,(l,annot))) as le) e_new_v =
    let exp = top_exp false in
    let (is_bit,is_bitv) = match e_new_v with
      | E_aux(_,(_,Base((_,t),_,_,_,_,_))) ->
        (match t.t with
         | Tapp("vector", [_;_;_;(TA_typ ({t=Tid "bit"} | {t=Tabbrev(_,{t=Tid "bit"})}))]) |
           Tabbrev(_,{t=Tapp("vector",[_;_;_;TA_typ ({t=Tid "bit"} | {t=Tabbrev(_,{t=Tid "bit"})})])}) |
           Tapp("reg", [TA_typ {t= Tapp("vector", [_;_;_;(TA_typ ({t=Tid "bit"} | {t=Tabbrev(_,{t=Tid "bit"})}))])}])
           ->
           (false,true)
         | Tid "bit" | Tabbrev(_,{t=Tid "bit"}) | Tapp("reg",[TA_typ ({t=Tid "bit"} | {t=Tabbrev(_,{t=Tid "bit"})})])
           -> (true,false)
         | _ -> (false,false))
      | _ -> (false,false) in
    match lexp with
    | LEXP_vector(v,e) ->
       if is_bit then (* XXX check whether register or not?? *)
         parens ((string "set_register_bit" ^^ space ^^ doc_lexp_ocaml false v ^^ space ^^ exp e ^^ space ^^ exp e_new_v))
          else  (* XXX Check whether vector of reg? XXX Does not work for decreasing vector. *) 
         parens ((string "set_register") ^^ space ^^ 
         ((group (parens ((string "get_varray") ^^ space ^^ doc_lexp_ocaml false v)) ^^ 
             dot ^^ parens ((string "int_of_big_int") ^^ space ^^ (exp e))) ^^ space ^^ (exp e_new_v)))
    | LEXP_vector_range(v,e1,e2) ->
      parens ((string (if is_bitv then "set_vector_subrange_bit" else "set_vector_subrange_vec")) ^^ space ^^
              doc_lexp_ocaml false v ^^ space ^^ exp e1 ^^ space ^^ exp e2 ^^ space ^^ exp e_new_v)
    | LEXP_field(v,id) ->
      parens ((string (if is_bit then "set_register_field_bit" else "set_register_field_v")) ^^ space ^^
              doc_lexp_ocaml false v ^^ space ^^string_lit (doc_id id) ^^ space ^^ exp e_new_v)
    | LEXP_id id | LEXP_cast (_,id) ->
      (match annot with
       | Base(_,Alias alias_info,_,_,_,_) ->
         (match alias_info with
          | Alias_field(reg,field) ->
            parens ((if is_bit then string "set_register_field_bit" else string "set_register_field_v") ^^ space ^^
                    string (sanitize_name reg) ^^ space ^^string_lit (string field) ^^ space ^^ exp e_new_v)
          | Alias_extract(reg,start,stop) ->
            if start = stop
            then
              doc_op (string "<-")
                (group (parens ((string (if is_bit then "get_barray" else "get_varray")) ^^ space ^^ string reg)) ^^
                 dot ^^ parens ((string "int_of_big_int") ^^ space ^^ (doc_int start)))
                (exp e_new_v)
            else
              parens ((string (if is_bitv then "set_vector_subrange_bit" else "set_vector_subrange_vec")) ^^ space ^^
                      string reg ^^ space ^^ doc_int start ^^ space ^^ doc_int stop ^^ space ^^ exp e_new_v)
          | Alias_pair(reg1,reg2) ->
            parens ((string "set_two_regs") ^^ space ^^ string reg1 ^^ space ^^ string reg2 ^^ space ^^ exp e_new_v))
       | _ ->
         parens (separate space [string "set_register"; doc_id_ocaml id; exp e_new_v]))
    | _ -> failwith "doc_lexp_rwrite: unhandled lexp"

  and doc_lexp_fcall ((LEXP_aux(lexp,(l,annot))) as le) e_new_v = match lexp with
    | LEXP_memory(id,args) -> doc_id_ocaml id ^^ parens (separate_map comma (top_exp false) (args@[e_new_v]))
    | _ -> failwith "doc_lexp_fcall: unhandled lexp"

  (* expose doc_exp and doc_let *)
  in top_exp false, let_exp

(*TODO Upcase and downcase type and constructors as needed*)
let doc_type_union_ocaml n (Tu_aux(typ_u,_)) = match typ_u with
  | Tu_ty_id(typ,id) -> separate space [pipe; doc_id_ocaml_ctor n id; string "of"; doc_typ_ocaml typ;]
  | Tu_id id -> separate space [pipe; doc_id_ocaml_ctor n id]

let rec doc_range_ocaml (BF_aux(r,_)) = match r with
  | BF_single i -> parens (doc_op comma (doc_int i) (doc_int i))
  | BF_range(i1,i2) -> parens (doc_op comma (doc_int i1) (doc_int i2))
  | BF_concat(ir1,ir2) -> (doc_range ir1) ^^ comma ^^ (doc_range ir2)

let doc_typdef_ocaml (TD_aux(td,_)) = match td with
  | TD_abbrev(id,nm,typschm) ->
      doc_op equals (concat [string "type"; space; doc_id_ocaml_type id;]) (doc_typscm_ocaml typschm)
  | TD_record(id,nm,typq,fs,_) ->
      let f_pp (typ,id) = concat [doc_id_ocaml_type id; space; colon; doc_typ_ocaml typ; semi] in
      let fs_doc = group (separate_map (break 1) f_pp fs) in
      doc_op equals
        (concat [string "type"; space; doc_id_ocaml_type id;]) (doc_typquant_ocaml typq (braces fs_doc))
  | TD_variant(id,nm,typq,ar,_) ->
    let n = List.length ar in
    let ar_doc = group (separate_map (break 1) (doc_type_union_ocaml n) ar) in
    doc_op equals
      (concat [string "type"; space; doc_id_ocaml_type id;])
      (if n > 246
       then brackets (space ^^(doc_typquant_ocaml typq ar_doc))
       else (doc_typquant_ocaml typq ar_doc))
  | TD_enum(id,nm,enums,_) ->
    let n = List.length enums in
    let enums_doc = group (separate_map (break 1 ^^ pipe) (doc_id_ocaml_ctor n) enums) in
    doc_op equals
      (concat [string "type"; space; doc_id_ocaml_type id;])
      (enums_doc)
  | TD_register(id,n1,n2,rs) ->
    let doc_rid (r,id) = parens (separate comma_sp [string_lit (doc_id id); doc_range_ocaml r;]) in
    let doc_rids = group (separate_map (semi ^^ (break 1)) doc_rid rs) in
    match n1,n2 with
    | Nexp_aux(Nexp_constant i1,_),Nexp_aux(Nexp_constant i2,_) ->
      let dir = i1 < i2 in
      let size = if dir then i2-i1 +1 else i1-i2+1  in
      doc_op equals
        ((string "let") ^^ space ^^ doc_id_ocaml id ^^ space ^^ (string "init_val"))
        (separate space [string "Vregister";
                         (parens (separate comma_sp
                                    [parens (separate space
                                               [string "match init_val with";
                                                pipe;
                                                string "None";
                                                arrow;
                                                string "ref";
                                                string "(Array.make";
                                                doc_int size;
                                                string "Vzero)";
                                                pipe;
                                                string "Some init_val";
                                                arrow;
                                                string "ref init_val";]);
                                     doc_nexp n1;
                                     string (if dir then "true" else "false");
                                     string_lit (doc_id id);
                                     brackets doc_rids]))])
    | _ -> failwith "doc_typedef_ocaml: unhandled nexp"

let doc_kdef_ocaml (KD_aux(kd,_)) = match kd with
  | KD_nabbrev (k, id, name_scm, nexp) -> 
     separate space [string "let" ; 
                     doc_id_ocaml id;
                     equals;
                     doc_nexp nexp]
  | KD_abbrev(_,id,nm,typschm) ->
      doc_op equals (concat [string "type"; space; doc_id_ocaml_type id;]) (doc_typscm_ocaml typschm)
  | KD_record(_,id,nm,typq,fs,_) ->
      let f_pp (typ,id) = concat [doc_id_ocaml_type id; space; colon; doc_typ_ocaml typ; semi] in
      let fs_doc = group (separate_map (break 1) f_pp fs) in
      doc_op equals
        (concat [string "type"; space; doc_id_ocaml_type id;]) (doc_typquant_ocaml typq (braces fs_doc))
  | KD_variant(_,id,nm,typq,ar,_) ->
    let n = List.length ar in
    let ar_doc = group (separate_map (break 1) (doc_type_union_ocaml n) ar) in
    doc_op equals
      (concat [string "type"; space; doc_id_ocaml_type id;])
      (if n > 246
       then brackets (space ^^(doc_typquant_ocaml typq ar_doc))
       else (doc_typquant_ocaml typq ar_doc))
  | KD_enum(_,id,nm,enums,_) ->
    let n = List.length enums in
    let enums_doc = group (separate_map (break 1 ^^ pipe) (doc_id_ocaml_ctor n) enums) in
    doc_op equals
      (concat [string "type"; space; doc_id_ocaml_type id;])
      (enums_doc)
  | KD_register(_,id,n1,n2,rs) ->
    let doc_rid (r,id) = parens (separate comma_sp [string_lit (doc_id id); doc_range_ocaml r;]) in
    let doc_rids = group (separate_map (semi ^^ (break 1)) doc_rid rs) in
    match n1,n2 with
    | Nexp_aux(Nexp_constant i1,_),Nexp_aux(Nexp_constant i2,_) ->
      let dir = i1 < i2 in
      let size = if dir then i2-i1 +1 else i1-i2 in
      doc_op equals
        ((string "let") ^^ space ^^ doc_id_ocaml id ^^ space ^^ (string "init_val"))
        (separate space [string "Vregister";
                         (parens (separate comma_sp
                                    [parens (separate space
                                               [string "match init_val with";
                                                pipe;
                                                string "None";
                                                arrow;
                                                string "ref";
                                                string "(Array.make";
                                                doc_int size;
                                                string "Vzero)";
                                                pipe;
                                                string "Some init_val";
                                                arrow;
                                                string "ref init_val";]);
                                     doc_nexp n1;
                                     string (if dir then "true" else "false");
                                     string_lit (doc_id id);
                                     brackets doc_rids]))])
    | _ -> failwith "doc_kdef_ocaml: unhandled nexp"

let doc_rec_ocaml (Rec_aux(r,_)) = match r with
  | Rec_nonrec -> empty
  | Rec_rec -> string "rec" ^^ space

let doc_tannot_opt_ocaml (Typ_annot_opt_aux(t,_)) = match t with
  | Typ_annot_opt_some(tq,typ) -> doc_typquant_ocaml tq (doc_typ_ocaml typ)

let doc_funcl_exp_ocaml (E_aux (e, (l, annot)) as ea) = match annot with
  | Base((_,t),tag,nes,efct,efctsum,_) ->
     if has_lret_effect efctsum then
       separate hardline [string "let ret = ref None in"; 
                       string "try";
                       (doc_exp_ocaml ea);
                       string "with Sail_return -> match(!ret) with";
                       string "| Some(x) -> x";
                       string "| None -> failwith \"ret unset\""
                      ]
     else
       doc_exp_ocaml ea
  | _ -> doc_exp_ocaml ea

let doc_funcl_ocaml (FCL_aux(FCL_Funcl(id,pat,exp),_)) =
  group (doc_op arrow (doc_pat_ocaml pat) (doc_funcl_exp_ocaml exp))

let get_id = function
  | [] -> failwith "FD_function with empty list"
  | (FCL_aux (FCL_Funcl (id,_,_),_))::_ -> id

let doc_fundef_ocaml (FD_aux(FD_function(r, typa, efa, fcls),_)) =
  match fcls with
  | [] -> failwith "FD_function with empty function list"
  | [FCL_aux (FCL_Funcl(id,pat,exp),_)] -> 
     (separate space [(string "let"); (doc_rec_ocaml r); (doc_id_ocaml id); (doc_pat_ocaml pat); equals]) ^^ hardline ^^ (doc_funcl_exp_ocaml exp)
  | _ ->
    let id = get_id fcls in
    let sep = hardline ^^ pipe ^^ space in
    let clauses = separate_map sep doc_funcl_ocaml fcls in
    separate space [string "let";
                    doc_rec_ocaml r;
                    doc_id_ocaml id;
                    equals;
                    (string "function");
                    (hardline^^pipe);
                    clauses]

let doc_dec_ocaml (DEC_aux (reg,(l,annot))) =
  match reg with
  | DEC_reg(typ,id) ->
    (match annot with
     | Base((_,t),_,_,_,_,_) ->
       (match t.t with
        | Tapp("register", [TA_typ {t= Tapp("vector", [TA_nexp start; TA_nexp size; TA_ord order; TA_typ itemt])}]) 
        | Tapp("register", [TA_typ {t= Tabbrev(_,{t=Tapp("vector", [TA_nexp start; TA_nexp size; TA_ord order; TA_typ itemt])})}]) ->
          (match itemt.t,start.nexp,size.nexp with
           | Tid "bit", Nconst start, Nconst size ->
             let o = if order.order = Oinc then string "true" else string "false" in
             separate space [string "let";
                             doc_id_ocaml id;
                             equals;
                             string "Vregister";
                             parens (separate comma [separate space [string "ref";
                                                                     parens (separate space
                                                                               [string "Array.make";
                                                                                doc_int (int_of_big_int size);
                                                                                string "Vzero";])];
                                                     doc_int (int_of_big_int start);
                                                     o;
                                                     string_lit (doc_id id);
                                                     brackets empty])]
           | _ -> empty)
        | Tapp("register", [TA_typ {t=Tid idt}]) |
          Tabbrev( {t= Tid idt}, _) ->
          separate space [string "let";
                          doc_id_ocaml id;
                          equals;
                          doc_id_ocaml (Id_aux (Id idt, Unknown));
                          string "None"]
        |_-> failwith "type was not handled in register declaration")
     | _ -> failwith "annot was not Base")
    | DEC_alias(id,alspec) -> empty (*
        doc_op equals (string "register alias" ^^ space ^^ doc_id id) (doc_alias alspec) *)
    | DEC_typ_alias(typ,id,alspec) -> empty (*
        doc_op equals (string "register alias" ^^ space ^^ doc_atomic_typ typ) (doc_alias alspec) *)

let doc_def_ocaml def = group (match def with
  | DEF_default df -> empty
  | DEF_spec v_spec -> empty (*unless we want to have a separate pass to create mli files*)
  | DEF_type t_def -> doc_typdef_ocaml t_def
  | DEF_fundef f_def -> doc_fundef_ocaml f_def
  | DEF_val lbind -> doc_let_ocaml lbind
  | DEF_reg_dec dec -> doc_dec_ocaml dec
  | DEF_scattered sdef -> empty (*shoulnd't still be here*)
  | DEF_kind k_def -> doc_kdef_ocaml k_def
  | DEF_comm _ -> failwith "unhandled DEF_comm"
  ) ^^ hardline

let doc_defs_ocaml (Defs(defs)) =
  separate_map hardline doc_def_ocaml defs
let pp_defs_ocaml f d top_line opens =
  print f (string "(*" ^^ (string top_line) ^^ string "*)" ^/^
           (separate_map hardline (fun lib -> (string "open") ^^ space ^^ (string lib)) opens) ^/^
           (doc_defs_ocaml d))

