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

open Type_internal
open Ast
open Big_int
open PPrint
open Pretty_print_common

(****************************************************************************
 * PPrint-based sail-to-lem pprinter
****************************************************************************)

let print_to_from_interp_value = ref true
let langlebar = string "<|"
let ranglebar = string "|>"
let anglebars = enclose langlebar ranglebar

let fix_id name = match name with
  | "assert"
  | "lsl"
  | "lsr"
  | "asr"
  | "type"
  | "fun"
  | "function"
  | "raise"
  | "try"
  | "match"
  | "with"
  | "field"
  | "LT"
  | "GT"
  | "EQ"
  | "integer"
    -> name ^ "'"
  | _ -> name

let is_number char =
  char = '0' || char = '1' || char = '2' || char = '3' || char = '4' || char = '5' ||
  char = '6' || char = '7' || char = '8' || char = '9'

let doc_id_lem (Id_aux(i,_)) =
  match i with
  | Id i ->
     (* this not the right place to do this, just a workaround *)
     if i.[0] = '\'' then
       string ((String.sub i 1 (String.length i - 1)) ^ "'")
     else if is_number(i.[0]) then
       string ("v" ^ i ^ "'")
     else
       string (fix_id i)
  | DeIid x ->
     (* add an extra space through empty to avoid a closing-comment
      * token in case of x ending with star. *)
     parens (separate space [colon; string x; empty])

let doc_id_lem_type (Id_aux(i,_)) =
  match i with
  | Id("int") -> string "ii"
  | Id("nat") -> string "ii"
  | Id("option") -> string "maybe"
  | Id i -> string (fix_id i)
  | DeIid x ->
     (* add an extra space through empty to avoid a closing-comment
      * token in case of x ending with star. *)
     parens (separate space [colon; string x; empty])

let doc_id_lem_ctor (Id_aux(i,_)) =
  match i with
  | Id("bit") -> string "bitU"
  | Id("int") -> string "integer"
  | Id("nat") -> string "integer"
  | Id("Some") -> string "Just"
  | Id("None") -> string "Nothing"
  | Id i -> string (fix_id (String.capitalize i))
  | DeIid x ->
     (* add an extra space through empty to avoid a closing-comment
      * token in case of x ending with star. *)
     separate space [colon; string (String.capitalize x); empty]

let effectful (Effect_aux (eff,_)) =
  match eff with
  | Effect_var _ -> failwith "effectful: Effect_var not supported"
  | Effect_set effs ->
     List.exists
       (fun (BE_aux (eff,_)) ->
         match eff with
         | BE_rreg | BE_wreg | BE_rmem | BE_rmemt | BE_wmem | BE_eamem
         | BE_exmem | BE_wmv | BE_wmvt | BE_barr | BE_depend | BE_nondet
         | BE_escape -> true
         | _ -> false)
       effs

let rec is_number {t=t} =
  match t with
  | Tabbrev (t1,t2) -> is_number t1 || is_number t2
  | Tapp ("range",_)
  | Tapp ("implicit",_)
  | Tapp ("atom",_) -> true
  | _ -> false

let doc_typ_lem, doc_atomic_typ_lem =
  (* following the structure of parser for precedence *)
  let rec typ regtypes ty = fn_typ regtypes true ty
    and typ' regtypes ty = fn_typ regtypes false ty
    and fn_typ regtypes atyp_needed ((Typ_aux (t, _)) as ty) = match t with
      | Typ_fn(arg,ret,efct) ->
         (*let exc_typ = string "string" in*)
         let ret_typ =
           if effectful efct
           then separate space [string "M";(*parens exc_typ;*) fn_typ regtypes true ret]
           else separate space [fn_typ regtypes false ret] in
         let tpp = separate space [tup_typ regtypes true arg; arrow;ret_typ] in
         (* once we have proper excetions we need to know what the exceptions type is *)
         if atyp_needed then parens tpp else tpp
      | _ -> tup_typ regtypes atyp_needed ty
    and tup_typ regtypes atyp_needed ((Typ_aux (t, _)) as ty) = match t with
      | Typ_tup typs ->
         let tpp = separate_map (space ^^ star ^^ space) (app_typ regtypes false) typs in
         if atyp_needed then parens tpp else tpp
      | _ -> app_typ regtypes atyp_needed ty
    and app_typ regtypes atyp_needed ((Typ_aux (t, _)) as ty) = match t with
      | Typ_app(Id_aux (Id "vector", _),[_;_;_;Typ_arg_aux (Typ_arg_typ typa, _)]) ->
         let tpp = string "vector" ^^ space ^^ typ regtypes typa in
         if atyp_needed then parens tpp else tpp
      | Typ_app(Id_aux (Id "range", _),_) ->
         (string "integer")
      | Typ_app(Id_aux (Id "implicit", _),_) ->
         (string "integer")
      | Typ_app(Id_aux (Id "atom", _), [Typ_arg_aux(Typ_arg_nexp n,_)]) ->
         (string "integer")
      | Typ_app(id,args) ->
         let tpp = (doc_id_lem_type id) ^^ space ^^ (separate_map space (doc_typ_arg_lem regtypes) args) in
         if atyp_needed then parens tpp else tpp
      | _ -> atomic_typ regtypes atyp_needed ty
    and atomic_typ regtypes atyp_needed ((Typ_aux (t, _)) as ty) = match t with
      | Typ_id (Id_aux (Id "bool",_)) -> string "bitU"
      | Typ_id (Id_aux (Id "boolean",_)) -> string "bitU"
      | Typ_id (Id_aux (Id "bit",_)) -> string "bitU"
      | Typ_id ((Id_aux (Id name,_)) as id) ->
         if List.exists ((=) name) regtypes
         then string "register"
         else doc_id_lem_type id
      | Typ_var v -> doc_var v
      | Typ_wild -> underscore
      | Typ_app _ | Typ_tup _ | Typ_fn _ ->
         (* exhaustiveness matters here to avoid infinite loops
          * if we add a new Typ constructor *)
         let tpp = typ regtypes ty in
         if atyp_needed then parens tpp else tpp
    and doc_typ_arg_lem regtypes (Typ_arg_aux(t,_)) = match t with
      | Typ_arg_typ t -> app_typ regtypes false t
      | Typ_arg_nexp n -> empty
      | Typ_arg_order o -> empty
      | Typ_arg_effect e -> empty
  in typ', atomic_typ

(* doc_lit_lem gets as an additional parameter the type information from the
 * expression around it: that's a hack, but how else can we distinguish between
 * undefined values of different types ? *)
let doc_lit_lem in_pat (L_aux(lit,l)) a =
  utf8string (match lit with
  | L_unit  -> "()"
  | L_zero  -> "B0"
  | L_one   -> "B1"
  | L_false -> "B0"
  | L_true  -> "B1"
  | L_num i ->
     let ipp = string_of_int i in
     if in_pat then "("^ipp^":nn)"
     else if i < 0 then "((0"^ipp^"):ii)"
     else "("^ipp^":ii)"
  | L_hex n -> failwith "Shouldn't happen" (*"(num_to_vec " ^ ("0x" ^ n) ^ ")" (*shouldn't happen*)*)
  | L_bin n -> failwith "Shouldn't happen" (*"(num_to_vec " ^ ("0b" ^ n) ^ ")" (*shouldn't happen*)*)
  | L_undef ->
     let (Base ((_,{t = t}),_,_,_,_,_)) = a in
     (match t with
      | Tid "bit"
      | Tabbrev ({t = Tid "bit"},_) -> "BU"
      | Tapp ("register",_)
      | Tabbrev ({t = Tapp ("register",_)},_) -> "UndefinedRegister 0"
      | Tid "string"
      | Tabbrev ({t = Tapp ("string",_)},_) -> "\"\""
      | _ -> "(failwith \"undefined value of unsupported type\")")
  | L_string s -> "\"" ^ s ^ "\"")

(* typ_doc is the doc for the type being quantified *)

let doc_typquant_lem (TypQ_aux(tq,_)) typ_doc = typ_doc

let doc_typschm_lem regtypes (TypSchm_aux(TypSchm_ts(tq,t),_)) =
  (doc_typquant_lem tq (doc_typ_lem regtypes t))

(*Note: vector concatenation, literal vectors, indexed vectors, and record should
  be removed prior to pp. The latter two have never yet been seen
*)
let rec doc_pat_lem regtypes apat_needed (P_aux (p,(l,annot)) as pa) = match p with
  | P_app(id, ((_ :: _) as pats)) ->
     (match annot with
      | Base(_,(Constructor _ | Enum _),_,_,_,_) ->
         let ppp = doc_unop (doc_id_lem_ctor id)
                            (parens (separate_map comma (doc_pat_lem regtypes true) pats)) in
         if apat_needed then parens ppp else ppp
      | _ -> empty)
  | P_app(id,[]) ->
    (match annot with
     | Base(_,(Constructor _| Enum _),_,_,_,_) -> doc_id_lem_ctor id
     | _ -> empty)
  | P_lit lit  -> doc_lit_lem true lit annot
  | P_wild -> underscore
  | P_id id ->
     begin match id with
     | Id_aux (Id "None",_) -> string "Nothing" (* workaround temporary issue *)
     | _ -> doc_id_lem id end
  | P_as(p,id) -> parens (separate space [doc_pat_lem regtypes true p; string "as"; doc_id_lem id])
  | P_typ(typ,p) -> doc_op colon (doc_pat_lem regtypes true p) (doc_typ_lem regtypes typ)
  | P_vector pats ->
     let ppp =
       (separate space)
         [string "Vector";brackets (separate_map semi (doc_pat_lem regtypes true) pats);underscore;underscore] in
     if apat_needed then parens ppp else ppp
  | P_vector_concat pats ->
     let ppp =
       (separate space)
         [string "Vector";parens (separate_map (string "::") (doc_pat_lem regtypes true) pats);underscore;underscore] in
     if apat_needed then parens ppp else ppp
  | P_tup pats  ->
     (match pats with
      | [p] -> doc_pat_lem regtypes apat_needed p
      | _ -> parens (separate_map comma_sp (doc_pat_lem regtypes false) pats))
     | P_list pats -> brackets (separate_map semi (doc_pat_lem regtypes false) pats) (*Never seen but easy in lem*)

let prefix_recordtype = true
let report = Reporting_basic.err_unreachable
let doc_exp_lem, doc_let_lem =
  let rec top_exp regtypes (aexp_needed : bool) (E_aux (e, (l,annot))) =
    let expY = top_exp regtypes true in
    let expN = top_exp regtypes false in
    let expV = top_exp regtypes in
    match e with
    | E_assign((LEXP_aux(le_act,tannot) as le),e) ->
       (* can only be register writes *)
       let (_,(Base ((_,{t = t}),tag,_,_,_,_))) = tannot in
       (match le_act, t, tag with
        | LEXP_vector_range (le,e2,e3),_,_ ->
           (match le with
            | LEXP_aux (LEXP_field (le,id), (_,((Base ((_,{t = t}),_,_,_,_,_))))) ->
               if t = Tid "bit" then
                 raise (report l "indexing a register's (single bit) bitfield not supported")
               else
                 (prefix 2 1)
                   (string "write_reg_field_range")
                   (align (doc_lexp_deref_lem regtypes le ^^ space^^
                             string_lit (doc_id_lem id) ^/^ expY e2 ^/^ expY e3 ^/^ expY e))
            | _ ->
               (prefix 2 1)
                 (string "write_reg_range")
                 (align (doc_lexp_deref_lem regtypes le ^^ space ^^ expY e2 ^/^ expY e3 ^/^ expY e))
           )
        | LEXP_vector (le,e2), (Tid "bit" | Tabbrev (_,{t=Tid "bit"})),_ ->
           (match le with
            | LEXP_aux (LEXP_field (le,id), (_,((Base ((_,{t = t}),_,_,_,_,_))))) ->
               if t = Tid "bit" then
                 raise (report l "indexing a register's (single bit) bitfield not supported")
               else
                 (prefix 2 1)
                   (string "write_reg_field_bit")
                   (align (doc_lexp_deref_lem regtypes le ^^ space ^^ doc_id_lem id ^/^ expY e2 ^/^ expY e))
            | _ ->
               (prefix 2 1)
                 (string "write_reg_bit")
                 (doc_lexp_deref_lem regtypes le ^^ space ^^ expY e2 ^/^ expY e)
           )
        | LEXP_field (le,id), (Tid "bit"| Tabbrev (_,{t=Tid "bit"})), _ ->
           (prefix 2 1)
             (string "write_reg_bitfield")
             (doc_lexp_deref_lem regtypes le ^^ space ^^ string_lit(doc_id_lem id) ^/^ expY e)
        | LEXP_field (le,id), _, _ ->
           (prefix 2 1)
             (string "write_reg_field")
             (doc_lexp_deref_lem regtypes le ^^ space ^^
                string_lit(doc_id_lem id) ^/^ expY e)
        | (LEXP_id id | LEXP_cast (_,id)), t, Alias alias_info ->
           (match alias_info with
            | Alias_field(reg,field) ->
               let f = match t with
                 | (Tid "bit" | Tabbrev (_,{t=Tid "bit"})) ->
                    string "write_reg_bitfield"
                 | _ -> string "write_reg_field" in
               (prefix 2 1)
                 f
                 (separate space [string reg;string_lit(string field);expY e])
            | Alias_pair(reg1,reg2) ->
               string "write_two_regs" ^^ space ^^ string reg1 ^^ space ^^
                 string reg2 ^^ space ^^ expY e)
        | _ ->
           (prefix 2 1) (string "write_reg") (doc_lexp_deref_lem regtypes le ^/^ expY e))
    | E_vector_append(l,r) ->
       let epp =
         align (group (separate space [expY l;string "^^"] ^/^ expY r)) in
       if aexp_needed then parens epp else epp
    | E_cons(l,r) -> doc_op (group (colon^^colon)) (expY l) (expY r)
    | E_if(c,t,e) ->
       let (E_aux (_,(_,cannot))) = c in
       let epp =
         separate space [string "if";group (align (string "bitU_to_bool" ^//^ group (expY c)))] ^^
           break 1 ^^
             (prefix 2 1 (string "then") (expN t)) ^^ (break 1) ^^
               (prefix 2 1 (string "else") (expN e)) in
       if aexp_needed then parens (align epp) else epp
    | E_for(id,exp1,exp2,exp3,(Ord_aux(order,_)),exp4) ->
       raise (report l "E_for should have been removed till now")
    | E_let(leb,e) ->
       let epp = let_exp regtypes leb ^^ space ^^ string "in" ^^ hardline ^^ expN e in
       if aexp_needed then parens epp else epp
    | E_app(f,args) ->
       begin match f with
       (* temporary hack to make the loop body a function of the temporary variables *)
       | Id_aux ((Id (("foreach_inc" | "foreach_dec" |
                       "foreachM_inc" | "foreachM_dec" ) as loopf),_)) ->
          let [id;indices;body;e5] = args in
          let varspp = match e5 with
            | E_aux (E_tuple vars,_) ->
               let vars = List.map (fun (E_aux (E_id (Id_aux (Id name,_)),_)) -> string name) vars in
               begin match vars with
               | [v] -> v
               | _ -> parens (separate comma vars) end
            | E_aux (E_id (Id_aux (Id name,_)),_) ->
               string name
            | E_aux (E_lit (L_aux (L_unit,_)),_) ->
               string "_" in
          parens (
              (prefix 2 1)
                ((separate space) [string loopf;group (expY indices);expY e5])
                (parens
                   (prefix 1 1 (separate space [string "fun";expY id;varspp;arrow]) (expN body))
                )
            )
       | Id_aux (Id "append",_) ->
          let [e1;e2] = args in
          let epp = align (expY e1 ^^ space ^^ string "++" ^//^ expY e2) in
          if aexp_needed then parens (align epp) else epp
       | Id_aux (Id "slice_raw",_) ->
          let [e1;e2;e3] = args in
          let epp = separate space [string "slice_raw";expY e1;expY e2;expY e3] in
          if aexp_needed then parens (align epp) else epp
       | _ ->
          begin match annot with
          | Base (_,External (Some "bitwise_not_bit"),_,_,_,_) ->
             let [a] = args in
             let epp = align (string "~" ^^ expY a) in
             if aexp_needed then parens (align epp) else epp
          | Base (_,Constructor _,_,_,_,_) ->
             let argpp a_needed arg =
               let (E_aux (_,(_,Base((_,{t=t}),_,_,_,_,_)))) = arg in
               match t with
               | Tapp("vector",_) ->
                  let epp = concat [string "reset_vector_start";space;expY arg] in
                  if a_needed then parens epp else epp
               | _ -> expV a_needed arg in
             let epp =
               match args with
               | [] -> doc_id_lem_ctor f
               | [arg] -> doc_id_lem_ctor f ^^ space ^^ argpp true arg
               | _ ->
                  doc_id_lem_ctor f ^^ space ^^ 
                    parens (separate_map comma (argpp false) args) in
             if aexp_needed then parens (align epp) else epp
          | _ ->
             let call = match annot with
               | Base(_,External (Some n),_,_,_,_) -> string n
               | _ -> doc_id_lem f in
             let argpp a_needed arg =
               let (E_aux (_,(_,Base((_,{t=t}),_,_,_,_,_)))) = arg in
               match t with
               | Tapp("vector",_) ->
                  let epp = concat [string "reset_vector_start";space;expY arg] in
                  if a_needed then parens epp else epp
               | _ -> expV a_needed arg in
             let argspp = match args with
               | [arg] -> argpp true arg
               | args -> parens (align (separate_map (comma ^^ break 0) (argpp false) args)) in
             let epp = align (call ^//^ argspp) in
             if aexp_needed then parens (align epp) else epp
          end
       end
    | E_vector_access (v,e) ->
       let (Base (_,_,_,_,eff,_)) = annot in
       let epp =
         if has_rreg_effect eff then
           separate space [string "read_reg_bit";expY v;expY e]
         else
           separate space [string "access";expY v;expY e] in
       if aexp_needed then parens (align epp) else epp
    | E_vector_subrange (v,e1,e2) ->
       let (Base (_,_,_,_,eff,_)) = annot in
       let epp =
         if has_rreg_effect eff then
           align (string "read_reg_range" ^^ space ^^ expY v ^//^ expY e1 ^//^ expY e2)
         else
           align (string "slice" ^^ space ^^ expY v ^//^ expY e1 ^//^ expY e2) in
       if aexp_needed then parens (align epp) else epp
    | E_field((E_aux(_,(l,fannot)) as fexp),id) ->
       let (Base ((_,{t = t}),_,_,_,_,_)) = fannot in
       (match t with
        | Tabbrev({t = Tid regtyp},{t=Tapp("register",_)}) ->
           let field_f = match annot with
             | Base((_,{t = Tid "bit"}),_,_,_,_,_)
               | Base((_,{t = Tabbrev(_,{t=Tid "bit"})}),_,_,_,_,_) ->
                string "read_reg_bitfield"
             | _ -> string "read_reg_field" in
           let epp = field_f ^^ space ^^ (expY fexp) ^^ space ^^ string_lit (doc_id_lem id) in
           if aexp_needed then parens (align epp) else epp
        | Tid recordtyp
          | Tabbrev ({t = Tid recordtyp},_) ->
           let fname =
             if prefix_recordtype
             then (string (recordtyp ^ "_")) ^^ doc_id_lem id
             else doc_id_lem id in
           expY fexp ^^ dot ^^ fname
        | _ ->
           raise (report l "E_field expression with no register or record type"))
    | E_block [] -> string "()"
    | E_block exps -> raise (report l "Blocks should have been removed till now.")
    | E_nondet exps -> raise (report l "Nondet blocks not supported.")
    | E_id id ->
       (match annot with
        | Base((_, ({t = Tapp("register",_)} | {t=Tabbrev(_,{t=Tapp("register",_)})})),
               External _,_,eff,_,_) ->
           if has_rreg_effect eff then
             separate space [string "read_reg";doc_id_lem id]
           else
             doc_id_lem id
        | Base(_,(Constructor i |Enum i),_,_,_,_) -> doc_id_lem_ctor id
        | Base((_,t),Alias alias_info,_,eff,_,_) ->
           (match alias_info with
            | Alias_field(reg,field) ->
               let epp = match t.t with
                 | Tid "bit" | Tabbrev (_,{t=Tid "bit"}) ->
                    (separate space)
                      [string "read_reg_bitfield"; string reg;string_lit(string field)]
                 | _ ->
                    (separate space)
                      [string "read_reg_field"; string reg; string_lit(string field)] in
               if aexp_needed then parens (align epp) else epp
            | Alias_pair(reg1,reg2) ->
               let epp =
                 if has_rreg_effect eff then
                   separate space [string "read_two_regs";string reg1;string reg2]
                 else
                   separate space [string "RegisterPair";string reg1;string reg2] in
               if aexp_needed then parens (align epp) else epp
            | Alias_extract(reg,start,stop) ->
               let epp =
                 if start = stop then
                   (separate space)
                     [string "access";doc_int start;
                      parens (string "read_reg" ^^ space ^^ string reg)]
                 else
                   (separate space)
                     [string "slice"; doc_int start; doc_int stop;
                      parens (string "read_reg" ^^ space ^^ string reg)] in
               if aexp_needed then parens (align epp) else epp
           )
        | _ -> doc_id_lem id)
    | E_lit lit -> doc_lit_lem false lit annot
    | E_cast(Typ_aux (typ,_),e) ->
       (match annot with
        | Base(_,External _,_,_,_,_) -> string "read_reg" ^^ space ^^ expY e
        | _ ->
           (match typ with
            | Typ_app (Id_aux (Id "vector",_), [Typ_arg_aux (Typ_arg_nexp(Nexp_aux (Nexp_constant i,_)),_);_;_;_]) ->
               let epp = (concat [string "set_vector_start";space;string (string_of_int i)]) ^//^
                           expY e in
               if aexp_needed then parens epp else epp
            | Typ_var (Kid_aux (Var "length",_)) ->
               let epp = (string "set_vector_start_to_length") ^//^ expY e in
               if aexp_needed then parens epp else epp
            | _ -> 
               expV aexp_needed e)) (*(parens (doc_op colon (group (expY e)) (doc_typ_lem typ)))) *)
    | E_tuple exps ->
       (match exps with
        (* | [e] -> expV aexp_needed e *)
        | _ -> parens (separate_map comma expN exps))
    | E_record(FES_aux(FES_Fexps(fexps,_),_)) ->
       let (Base ((_,{t = t}),_,_,_,_,_)) = annot in
       let recordtyp = match t with
         | Tid recordtyp
           | Tabbrev ({t = Tid recordtyp},_) -> recordtyp
         | _ ->  raise (report l "cannot get record type") in
       let epp = anglebars (space ^^ (align (separate_map
                                          (semi_sp ^^ break 1)
                                          (doc_fexp regtypes recordtyp) fexps)) ^^ space) in
       if aexp_needed then parens epp else epp
    | E_record_update(e,(FES_aux(FES_Fexps(fexps,_),_))) ->
       let (Base ((_,{t = t}),_,_,_,_,_)) = annot in
       let recordtyp = match t with
         | Tid recordtyp
           | Tabbrev ({t = Tid recordtyp},_) -> recordtyp
         | _ ->  raise (report l "cannot get record type") in
       anglebars (doc_op (string "with") (expY e) (separate_map semi_sp (doc_fexp regtypes recordtyp) fexps))
    | E_vector exps ->
       (match annot with
        | Base((_,t),_,_,_,_,_) ->
           match t.t with
           | Tapp("vector", [TA_nexp start; _; TA_ord order; _])
             | Tabbrev(_,{t= Tapp("vector", [TA_nexp start; _; TA_ord order; _])}) ->
              let dir,dir_out = match order.order with
                | Oinc -> true,"true"
                | _ -> false, "false" in
              let start = match start.nexp with
                | Nconst i -> string_of_big_int i
                | N2n(_,Some i) -> string_of_big_int i
                | _ -> if dir then "0" else string_of_int (List.length exps) in
              let expspp =
                match exps with
                | [] -> empty
                | e :: es ->
                   let (expspp,_) =
                     List.fold_left
                       (fun (pp,count) e ->
                         (pp ^^ semi ^^ (if count = 20 then break 0 else empty) ^^
                            expN e),
                         if count = 20 then 0 else count + 1)
                       (expN e,0) es in
                   align (group expspp) in
              let epp =
                group (separate space [string "Vector"; brackets expspp;string start;string dir_out]) in
              if aexp_needed then parens (align epp) else epp
       )
    | E_vector_indexed (iexps, (Def_val_aux (default,(dl,dannot)))) ->
       let (Base((_,t),_,_,_,_,_)) = annot in
       let call = string "make_indexed_vector" in
       let (start,len,order) = match t.t with
         | Tapp("vector", [TA_nexp start; TA_nexp len; TA_ord order; _])
         | Tabbrev(_,{t= Tapp("vector", [TA_nexp start; TA_nexp len; TA_ord order; _])})
         | Tapp("reg", [TA_typ {t =Tapp("vector", [TA_nexp start; TA_nexp len; TA_ord order; _])}]) ->
            (start,len,order.order) in
       let dir,dir_out = match order with
         | Oinc -> true,"true"
         | _ -> false, "false" in
       let start = match start.nexp with
         | Nconst i | N2n(_,Some i)-> string_of_big_int i
         | N2n({nexp=Nconst i},_) -> string_of_int (Util.power 2 (int_of_big_int i))
         | _ -> if dir then "0" else string_of_int (List.length iexps) in
       let size = match len.nexp with
         | Nconst i | N2n(_,Some i)-> string_of_big_int i
         | N2n({nexp=Nconst i},_) -> string_of_int (Util.power 2 (int_of_big_int i)) in
       let default_string =
         match default with
         | Def_val_empty ->
            if is_bit_vector t then string "BU"
            else failwith "E_vector_indexed of non-bitvector type without default argument"
         | Def_val_dec e ->
            let (Base ((_,{t = t}),_,_,_,_,_)) = dannot in
            match t with
            | Tapp ("register",
                    [TA_typ ({t = rt})]) ->

               let n = match rt with
                 | Tapp ("vector",TA_nexp {nexp = Nconst i} :: TA_nexp {nexp = Nconst j} ::_) ->
                    abs_big_int (sub_big_int i j)
                 | _ ->
                    raise ((Reporting_basic.err_unreachable dl)
                             ("not the right type information available to construct "^
                                "undefined register")) in
               parens (string ("UndefinedRegister " ^ string_of_big_int n))
            | _ -> expY e in
       let iexp (i,e) = parens (doc_int i ^^ comma ^^ expN e) in
       let expspp =
         match iexps with
         | [] -> empty
         | e :: es ->
            let (expspp,_) =
              List.fold_left
                (fun (pp,count) e ->
                  (pp ^^ semi ^^ (if count = 5 then break 1 else empty) ^^ iexp e),
                  if count = 5 then 0 else count + 1)
                (iexp e,0) es in
            align (expspp) in
       let epp =
         align (group (call ^//^ brackets expspp ^/^
                         separate space [default_string;string start;string size;string dir_out])) in
       if aexp_needed then parens (align epp) else epp
    | E_vector_update(v,e1,e2) ->
       let epp = separate space [string "update_pos";expY v;expY e1;expY e2] in
       if aexp_needed then parens (align epp) else epp
    | E_vector_update_subrange(v,e1,e2,e3) ->
       let epp = align (string "update" ^//^
                          group (group (expY v) ^/^ group (expY e1) ^/^ group (expY e2)) ^/^
                            group (expY e3)) in
       if aexp_needed then parens (align epp) else epp
    | E_list exps ->
       brackets (separate_map semi (expN) exps)
    | E_case(e,pexps) ->

       let only_integers (E_aux(_,(_,annot)) as e) =
         match annot with
         | Base((_,t),_,_,_,_,_) ->
            if is_number t then
              let e_pp = expY e in
              align (string "toNatural" ^//^ e_pp)
            else
              (match t with
               | {t = Ttup ([t1;t2;t3;t4;t5] as ts)} when List.for_all is_number ts ->
                  let e_pp = expY e in
                  align (string "toNaturalFiveTup" ^//^ e_pp)
               | _ -> expY e)
         | _ -> expY e
       in

       (* This is a hack, incomplete. It's because lem does not allow
        pattern-matching on integers *)
       let epp =
         group ((separate space [string "match"; only_integers e; string "with"]) ^/^
                  (separate_map (break 1) (doc_case regtypes) pexps) ^/^
                    (string "end")) in
       if aexp_needed then parens (align epp) else align epp
    | E_exit e -> separate space [string "exit"; expY e;]
    | E_assert (e1,e2) ->
       let epp = separate space [string "assert'"; expY e1; expY e2] in
       if aexp_needed then parens (align epp) else align epp
    | E_app_infix (e1,id,e2) ->
       (match annot with
        | Base((_,t),External(Some name),_,_,_,_) ->
           let argpp arg =
             let (E_aux (_,(_,Base((_,{t=t}),_,_,_,_,_)))) = arg in
             match t with
             | Tapp("vector",_) -> parens (concat [string "reset_vector_start";space;expY arg])
             | _ -> expY arg in
           let epp =
             let aux name = align (argpp e1 ^^ space ^^ string name ^//^ argpp e2) in
             let aux2 name = align (string name ^//^ argpp e1 ^/^ argpp e2) in
             align
               (match name with
                | "power" -> aux2 "pow"

                | "bitwise_and_bit" -> aux "&."
                | "bitwise_or_bit" -> aux "|."
                | "bitwise_xor_bit" -> aux "+."
                | "add" -> aux "+"
                | "minus" -> aux "-"
                | "multiply" -> aux "*"

                | "quot" -> aux2 "quot"
                | "quot_signed" -> aux2 "quot"
                | "modulo" -> aux2 "modulo"
                | "add_vec" -> aux2 "add_VVV"
                | "add_vec_signed" -> aux2 "addS_VVV"
                | "add_overflow_vec" -> aux2 "addO_VVV"
                | "add_overflow_vec_signed" -> aux2 "addSO_VVV"
                | "minus_vec" -> aux2 "minus_VVV"
                | "minus_overflow_vec" -> aux2 "minusO_VVV"
                | "minus_overflow_vec_signed" -> aux2 "minusSO_VVV"
                | "multiply_vec" -> aux2 "mult_VVV"
                | "multiply_vec_signed" -> aux2 "multS_VVV"
                | "mult_overflow_vec" -> aux2 "multO_VVV"
                | "mult_overflow_vec_signed" -> aux2 "multSO_VVV"
                | "quot_vec" -> aux2 "quot_VVV"
                | "quot_vec_signed" -> aux2 "quotS_VVV"
                | "quot_overflow_vec" -> aux2 "quotO_VVV"
                | "quot_overflow_vec_signed" -> aux2 "quotSO_VVV"
                | "mod_vec" -> aux2 "mod_VVV"

                | "add_vec_range" -> aux2 "add_VIV"
                | "add_vec_range_signed" -> aux2 "addS_VIV"
                | "minus_vec_range" -> aux2 "minus_VIV"
                | "mult_vec_range" -> aux2 "mult_VIV"
                | "mult_vec_range_signed" -> aux2 "multS_VIV"
                | "mod_vec_range" -> aux2 "minus_VIV"

                | "add_range_vec" -> aux2 "add_IVV"
                | "add_range_vec_signed" -> aux2 "addS_IVV"
                | "minus_range_vec" -> aux2 "minus_IVV"
                | "mult_range_vec" -> aux2 "mult_IVV"
                | "mult_range_vec_signed" -> aux2 "multS_IVV"

                | "add_range_vec_range" -> aux2 "add_IVI"
                | "add_range_vec_range_signed" -> aux2 "addS_IVI"
                | "minus_range_vec_range" -> aux2 "minus_IVI"

                | "add_vec_range_range" -> aux2 "add_VII"
                | "add_vec_range_range_signed" -> aux2 "addS_VII"
                | "minus_vec_range_range" -> aux2 "minus_VII"
                | "add_vec_vec_range" -> aux2 "add_VVI"
                | "add_vec_vec_range_signed" -> aux2 "addS_VVI"

                | "add_vec_bit" -> aux2 "add_VBV"
                | "add_vec_bit_signed" -> aux2 "addS_VBV"
                | "add_overflow_vec_bit_signed" -> aux2 "addSO_VBV"
                | "minus_vec_bit_signed" -> aux2 "minus_VBV"
                | "minus_overflow_vec_bit" -> aux2 "minusO_VBV"
                | "minus_overflow_vec_bit_signed" -> aux2 "minusSO_VBV"

                | _ ->
                   string name ^//^ parens (expN e1 ^^ comma ^/^ expN e2)) in
           if aexp_needed then parens (align epp) else epp
        | _ ->
           let epp =
             align (doc_id_lem id ^//^ parens (expN e1 ^^ comma ^/^ expN e2)) in
           if aexp_needed then parens (align epp) else epp)
    | E_internal_let(lexp, eq_exp, in_exp) ->
       raise (report l "E_internal_lets should have been removed till now")
    (*     (separate
        space
        [string "let internal";
         (match lexp with (LEXP_aux ((LEXP_id id | LEXP_cast (_,id)),_)) -> doc_id_lem id);
         coloneq;
         exp eq_exp;
         string "in"]) ^/^
       exp in_exp *)
    | E_internal_plet (pat,e1,e2) ->
       let epp =
         let b = match e1 with E_aux (E_if _,_) -> true | _ -> false in
         match pat with
         | P_aux (P_wild,_) ->
            (separate space [expV b e1; string ">>"]) ^^ hardline ^^ expN e2
         | _ ->
            (separate space [expV b e1; string ">>= fun";
                             doc_pat_lem regtypes true pat;arrow]) ^^ hardline ^^ expN e2 in
       if aexp_needed then parens (align epp) else epp
    | E_internal_return (e1) ->
       separate space [string "return"; expY e1;]
  and let_exp regtypes (LB_aux(lb,_)) = match lb with
    | LB_val_explicit(_,pat,e)
      | LB_val_implicit(pat,e) ->
       prefix 2 1
              (separate space [string "let"; doc_pat_lem regtypes true pat; equals])
              (top_exp regtypes false e)

  and doc_fexp regtypes recordtyp (FE_aux(FE_Fexp(id,e),_)) =
    let fname =
      if prefix_recordtype
      then (string (recordtyp ^ "_")) ^^ doc_id_lem id
      else doc_id_lem id in
    group (doc_op equals fname (top_exp regtypes true e))

  and doc_case regtypes (Pat_aux(Pat_exp(pat,e),_)) =
    group (prefix 3 1 (separate space [pipe; doc_pat_lem regtypes false pat;arrow])
                  (group (top_exp regtypes false e)))

  and doc_lexp_deref_lem regtypes ((LEXP_aux(lexp,(l,annot))) as le) = match lexp with
    | LEXP_field (le,id) ->
       parens (separate empty [doc_lexp_deref_lem regtypes le;dot;doc_id_lem id])
    | LEXP_vector(le,e) ->
       parens ((separate space) [string "access";doc_lexp_deref_lem regtypes le;
                                 top_exp regtypes true e])
    | LEXP_id id -> doc_id_lem id
    | LEXP_cast (typ,id) -> doc_id_lem id
    | _ ->
       raise (Reporting_basic.err_unreachable l ("doc_lexp_deref_lem: Shouldn't happen"))
             (* expose doc_exp_lem and doc_let *)
  in top_exp, let_exp

(*TODO Upcase and downcase type and constructors as needed*)
let doc_type_union_lem regtypes (Tu_aux(typ_u,_)) = match typ_u with
  | Tu_ty_id(typ,id) -> separate space [pipe; doc_id_lem_ctor id; string "of";
                                        parens (doc_typ_lem regtypes typ)]
  | Tu_id id -> separate space [pipe; doc_id_lem_ctor id]

let rec doc_range_lem (BF_aux(r,_)) = match r with
  | BF_single i -> parens (doc_op comma (doc_int i) (doc_int i))
  | BF_range(i1,i2) -> parens (doc_op comma (doc_int i1) (doc_int i2))
  | BF_concat(ir1,ir2) -> (doc_range ir1) ^^ comma ^^ (doc_range ir2)

let doc_typdef_lem regtypes (TD_aux(td,_)) = match td with
  | TD_abbrev(id,nm,typschm) ->
     (doc_op equals (concat [string "type"; space; doc_id_lem_type id])
             (doc_typschm_lem regtypes typschm),empty)
  | TD_record(id,nm,typq,fs,_) ->
     let f_pp (typ,fid) =
       let fname = if prefix_recordtype
                   then concat [doc_id_lem id;string "_";doc_id_lem_type fid;]
                   else doc_id_lem_type fid in
       concat [fname;space;colon;space;doc_typ_lem regtypes typ; semi] in
      let fs_doc = group (separate_map (break 1) f_pp fs) in
      (doc_op equals
             (concat [string "type"; space; doc_id_lem_type id;])
             (doc_typquant_lem typq (anglebars (space ^^ align fs_doc ^^ space))),empty)
  | TD_variant(id,nm,typq,ar,_) ->
     (match id with
      | Id_aux ((Id "read_kind"),_) -> (empty,empty)
      | Id_aux ((Id "write_kind"),_) -> (empty,empty)
      | Id_aux ((Id "barrier_kind"),_) -> (empty,empty)
      | Id_aux ((Id "trans_kind"),_) -> (empty,empty)
      | Id_aux ((Id "instruction_kind"),_) -> (empty,empty)
      | Id_aux ((Id "regfp"),_) -> (empty,empty)
      | Id_aux ((Id "niafp"),_) -> (empty,empty)
      | Id_aux ((Id "diafp"),_) -> (empty,empty)
      | _ ->
         let ar_doc = group (separate_map (break 1) (doc_type_union_lem regtypes) ar) in
         let typ_pp =

           (doc_op equals)
             (concat [string "type"; space; doc_id_lem_type id;])
             (doc_typquant_lem typq ar_doc) in
         let make_id pat id =
           separate space [string "Interp_ast.Id_aux";
                           parens (string "Interp_ast.Id " ^^ string_lit (doc_id id));
                           if pat then underscore else string "Interp_ast.Unknown"] in
         let fromInterpValueF = concat [doc_id_lem_type id;string "FromInterpValue"] in
         let toInterpValueF = concat [doc_id_lem_type id;string "ToInterpValue"] in
         let fromInterpValuePP =
           (prefix 2 1)
             (separate space [string "let rec";fromInterpValueF;string "v";equals;string "match v with"])
             (
               ((separate_map (break 1))
                  (fun (Tu_aux (tu,_)) ->
                    match tu with
                    | Tu_ty_id (ty,cid) ->
                       (separate space)
                         [pipe;string "Interp_ast.V_ctor";parens (make_id true cid);underscore;underscore;string "v";
                          arrow;
                          doc_id_lem_ctor cid;
                          parens (string "fromInterpValue v")]
                    | Tu_id cid ->
                       (separate space)
                         [pipe;string "Interp_ast.V_ctor";parens (make_id true cid);underscore;underscore;string "v";
                          arrow;
                          doc_id_lem_ctor cid])
                  ar) ^/^

                  ((separate space) [pipe;string "Interp_ast.V_tuple [v]";arrow;fromInterpValueF;string "v"]) ^/^

                 let failmessage =
                    (string_lit
                       (concat [string "fromInterpValue";space;doc_id_lem_type id;colon;space;string "unexpected value. ";]))
                    ^^
                      (string " ^ Interp.debug_print_value v") in
                  ((separate space) [pipe;string "v";arrow;string "failwith";parens failmessage]) ^/^
                 string "end") in
         let toInterpValuePP =
           (prefix 2 1)
             (separate space [string "let";toInterpValueF;equals;string "function"])
             (
               ((separate_map (break 1))
                  (fun (Tu_aux (tu,_)) ->
                    match tu with
                    | Tu_ty_id (ty,cid) ->
                       (separate space)
                         [pipe;doc_id_lem_ctor cid;string "v";arrow;
                          string "Interp_ast.V_ctor";
                          parens (make_id false cid);
                          parens (string "Interp_ast.T_id " ^^ string_lit (doc_id id));
                          string "Interp_ast.C_Union";
                          parens (string "toInterpValue v")]
                    | Tu_id cid ->
                       (separate space)
                         [pipe;doc_id_lem_ctor cid;arrow;
                          string "Interp_ast.V_ctor";
                          parens (make_id false cid);
                          parens (string "Interp_ast.T_id " ^^ string_lit (doc_id id));
                          string "Interp_ast.C_Union";
                          parens (string "toInterpValue ()")])
                  ar) ^/^
                 string "end") in
         let fromToInterpValuePP =
          toInterpValuePP ^^ hardline ^^ hardline ^^
          fromInterpValuePP ^^ hardline ^^ hardline ^^           
           ((prefix 2 1)
              (concat [string "instance ";parens (string "ToFromInterpValue " ^^ doc_id_lem_type id)])
              (concat [string "let toInterpValue = ";toInterpValueF;hardline;
                       string "let fromInterpValue = ";fromInterpValueF]))
           ^/^ string "end" in
         (typ_pp ^^ hardline,fromToInterpValuePP ^^ hardline))
  | TD_enum(id,nm,enums,_) ->
     (match id with
      | Id_aux ((Id "read_kind"),_) -> (empty,empty)
      | Id_aux ((Id "write_kind"),_) -> (empty,empty)
      | Id_aux ((Id "barrier_kind"),_) -> (empty,empty)
      | Id_aux ((Id "trans_kind"),_) -> (empty,empty)
      | Id_aux ((Id "instruction_kind"),_) -> (empty,empty)
      | Id_aux ((Id "regfp"),_) -> (empty,empty)
      | Id_aux ((Id "niafp"),_) -> (empty,empty)
      | Id_aux ((Id "diafp"),_) -> (empty,empty)
      | _ ->
         let rec range i j = if i > j then [] else i :: (range (i+1) j) in
         let nats = range 0 in
         let enums_doc = group (separate_map (break 1 ^^ pipe ^^ space) doc_id_lem_ctor enums) in
         let typ_pp = (doc_op equals)
                        (concat [string "type"; space; doc_id_lem_type id;])
                        (enums_doc) in
         let fromInterpValueF = concat [doc_id_lem_type id;string "FromInterpValue"] in
         let toInterpValueF = concat [doc_id_lem_type id;string "ToInterpValue"] in
         let make_id pat id =
           separate space [string "Interp_ast.Id_aux";
                           parens (string "Interp_ast.Id " ^^ string_lit (doc_id id));
                           if pat then underscore else string "Interp_ast.Unknown"] in
         let fromInterpValuePP =
           (prefix 2 1)
             (separate space [string "let rec";fromInterpValueF;string "v";equals;string "match v with"])
             (
               ((separate_map (break 1))
                  (fun (cid) ->
                    (separate space)
                      [pipe;string "Interp_ast.V_ctor";parens (make_id true cid);underscore;underscore;string "v";
                       arrow;doc_id_lem_ctor cid]
                  )
                  enums
               ) ^/^
                 (
                   (align
                      ((prefix 3 1)
                         (separate space [pipe;string ("Interp_ast.V_lit (Interp_ast.L_aux (Interp_ast.L_num n) _)");arrow])
                         (separate space [string "match";parens(string "natFromInteger n");string "with"] ^/^
                            (
                              ((separate_map (break 1))
                                 (fun (cid,number) ->
                                   (separate space)
                                     [pipe;string (string_of_int number);arrow;doc_id_lem_ctor cid]
                                 )
                                 (List.combine enums (nats ((List.length enums) - 1)))
                              ) ^/^ string "end"
                            )
                         )
                      )
                   )
                 ) ^/^

                  ((separate space) [pipe;string "Interp_ast.V_tuple [v]";arrow;fromInterpValueF;string "v"]) ^/^

                   let failmessage =
                     (string_lit
                        (concat [string "fromInterpValue";space;doc_id_lem_type id;colon;space;string "unexpected value. ";]))
                     ^^
                       (string " ^ Interp.debug_print_value v") in
                   ((separate space) [pipe;string "v";arrow;string "failwith";parens failmessage]) ^/^

                     string "end") in
         let toInterpValuePP =
           (prefix 2 1)
             (separate space [string "let";toInterpValueF;equals;string "function"])
             (
               ((separate_map (break 1))
                  (fun (cid,number) ->
                    (separate space)
                      [pipe;doc_id_lem_ctor cid;arrow;
                       string "Interp_ast.V_ctor";
                       parens (make_id false cid);
                       parens (string "Interp_ast.T_id " ^^ string_lit (doc_id id));
                       parens (string ("Interp_ast.C_Enum " ^ string_of_int number));
                       parens (string "toInterpValue ()")])
                  (List.combine enums (nats ((List.length enums) - 1)))) ^/^
                 string "end") in
         let fromToInterpValuePP =
           toInterpValuePP ^^ hardline ^^ hardline ^^
           fromInterpValuePP ^^ hardline ^^ hardline ^^
           ((prefix 2 1)
             (concat [string "instance ";parens (string "ToFromInterpValue " ^^ doc_id_lem_type id)])
             (concat [string "let toInterpValue = ";toInterpValueF;hardline;
                      string "let fromInterpValue = ";fromInterpValueF]))
           ^/^ string "end" in
         (typ_pp ^^ hardline,
          fromToInterpValuePP ^^ hardline))
  | TD_register(id,n1,n2,rs) ->
    match n1,n2 with
    | Nexp_aux(Nexp_constant i1,_),Nexp_aux(Nexp_constant i2,_) ->
       let doc_rid (r,id) = parens (separate comma_sp [string_lit (doc_id_lem id);
                                                       doc_range_lem r;]) in
       let doc_rids = group (separate_map (semi ^^ (break 1)) doc_rid rs) in
       (*let doc_rfield (_,id) =
         (doc_op equals)
           (string "let" ^^ space ^^ doc_id_lem id)
           (string "Register_field" ^^ space ^^ string_lit(doc_id_lem id)) in*)
       let dir_b = i1 < i2 in
       let dir = string (if dir_b then "true" else "false") in
       let size = if dir_b then i2-i1 +1 else i1-i2 + 1 in
       ((doc_op equals)
         (concat [string "let";space;string "build_";doc_id_lem id;space;string "regname"])
         (string "Register" ^^ space ^^
            align (separate space [string "regname"; doc_int size; doc_int i1; dir;
                                   break 0 ^^ brackets (align doc_rids)])),empty)
       (*^^ hardline ^^
         separate_map hardline doc_rfield rs *)

let doc_rec_lem (Rec_aux(r,_)) = match r with
  | Rec_nonrec -> space
  | Rec_rec -> space ^^ string "rec" ^^ space

let doc_tannot_opt_lem regtypes (Typ_annot_opt_aux(t,_)) = match t with
  | Typ_annot_opt_some(tq,typ) -> doc_typquant_lem tq (doc_typ_lem regtypes typ)

let doc_funcl_lem regtypes (FCL_aux(FCL_Funcl(id,pat,exp),_)) =
  group (prefix 3 1 ((doc_pat_lem regtypes false pat) ^^ space ^^ arrow)
                (doc_exp_lem regtypes false exp))

let get_id = function
  | [] -> failwith "FD_function with empty list"
  | (FCL_aux (FCL_Funcl (id,_,_),_))::_ -> id

module StringSet = Set.Make(String)

let rec doc_fundef_lem regtypes (FD_aux(FD_function(r, typa, efa, fcls),fannot)) =
  match fcls with
  | [] -> failwith "FD_function with empty function list"
  | [FCL_aux (FCL_Funcl(id,pat,exp),_)] ->
     (prefix 2 1)
       ((separate space)
          [(string "let") ^^ (doc_rec_lem r) ^^ (doc_id_lem id);
           (doc_pat_lem regtypes true pat);
           equals])
       (doc_exp_lem regtypes false exp)
  | _ ->
    let id = get_id fcls in
    (*    let sep = hardline ^^ pipe ^^ space in *)
    match id with
    | Id_aux (Id fname,idl)
      when fname = "execute" || fname = "initial_analysis" ->
      let (_,auxiliary_functions,clauses) = 
        List.fold_left 
          (fun (already_used_fnames,auxiliary_functions,clauses) funcl ->
            match funcl with
            | FCL_aux (FCL_Funcl (Id_aux (Id _,l),pat,exp),annot) ->
               let (P_aux (P_app (Id_aux (Id ctor,l),argspat),pannot)) = pat in
               let rec pick_name_not_clashing_with already_used candidate =
                 if StringSet.mem candidate already_used then
                   pick_name_not_clashing_with already_used (candidate ^ "'")
                 else candidate in
               let aux_fname = pick_name_not_clashing_with already_used_fnames (fname ^ "_" ^ ctor) in
               let already_used_fnames = StringSet.add aux_fname already_used_fnames in
               let fcl = FCL_aux (FCL_Funcl (Id_aux (Id aux_fname,l),
                                             P_aux (P_tup argspat,pannot),exp),annot) in
               let auxiliary_functions = 
                  auxiliary_functions ^^ hardline ^^ hardline ^^
                    doc_fundef_lem regtypes (FD_aux (FD_function(r,typa,efa,[fcl]),fannot)) in
               (* Bind complex patterns to names so that we can pass them to the
                  auxiliary function *)
               let name_pat idx (P_aux (p,a)) = match p with
                 | P_as (pat,_) -> P_aux (p,a) (* already named *)
                 | P_lit _ -> P_aux (p,a) (* no need to name a literal *)
                 | P_id _ -> P_aux (p,a) (* no need to name an identifier *)
                 | _ -> P_aux (P_as (P_aux (p,a), Id_aux (Id ("arg" ^ string_of_int idx),l)),a) in
               let named_argspat = List.mapi name_pat argspat in
               let named_pat = P_aux (P_app (Id_aux (Id ctor,l),named_argspat),pannot) in
               let doc_arg idx (P_aux (p,(l,a))) = match p with
                 | P_as (pat,id) -> doc_id_lem id
                 | P_lit lit -> doc_lit_lem false lit a
                 | P_id id -> doc_id_lem id
                 | _ -> string ("arg" ^ string_of_int idx) in
               let clauses =
                 clauses ^^ (break 1) ^^
                   (separate space
                      [pipe;doc_pat_lem regtypes false named_pat;arrow;
                       string aux_fname;
                       parens (separate comma (List.mapi doc_arg named_argspat))]) in
               (already_used_fnames,auxiliary_functions,clauses)
          ) (StringSet.empty,empty,empty) fcls in

      auxiliary_functions ^^ hardline ^^ hardline ^^
      (prefix 2 1)
        ((separate space) [string "let" ^^ doc_rec_lem r ^^ doc_id_lem id;equals;string "function"])
        (clauses ^/^ string "end")
    | _ ->
      let clauses =
        (separate_map (break 1))
          (fun fcl -> separate space [pipe;doc_funcl_lem regtypes fcl]) fcls in
      (prefix 2 1)
        ((separate space) [string "let" ^^ doc_rec_lem r ^^ doc_id_lem id;equals;string "function"])
        (clauses ^/^ string "end")
      


let doc_dec_lem (DEC_aux (reg,(l,annot))) =
  match reg with
  | DEC_reg(typ,id) ->
     (match annot with
     | Base((_,t),_,_,_,_,_) ->
       (match t.t with
        | Tapp("register", [TA_typ {t= Tapp("vector", [TA_nexp start; TA_nexp size; TA_ord order; TA_typ itemt])}])
        | Tapp("register", [TA_typ {t= Tabbrev(_,{t=Tapp("vector", [TA_nexp start; TA_nexp size; TA_ord order; TA_typ itemt])})}]) ->
          (match itemt.t,start.nexp,size.nexp with
           | Tid "bit", Nconst start, Nconst size ->
             let o = if order.order = Oinc then "true" else "false" in
             (doc_op equals)
             (string "let" ^^ space ^^ doc_id_lem id)
             (string "Register" ^^ space ^^
                align (separate space [string_lit(doc_id_lem id);
                                       doc_int (int_of_big_int size);
                                       doc_int (int_of_big_int start);
                                       string o;
                                       string "[]"]))
                ^/^ hardline
           | _ ->
              let (Id_aux (Id name,_)) = id in
              failwith ("can't deal with register " ^ name))
        | Tapp("register", [TA_typ {t=Tid idt}])
        | Tid idt
        | Tabbrev( {t= Tid idt}, _) ->
           separate space [string "let";doc_id_lem id;equals;
                           string "build_" ^^ string idt;string_lit (doc_id_lem id)] ^/^ hardline
        |_-> empty)
     | _ ->  empty)
  | DEC_alias(id,alspec) -> empty
  | DEC_typ_alias(typ,id,alspec) -> empty

let doc_spec_lem regtypes (VS_aux (valspec,annot)) =
  match valspec with
  | VS_extern_no_rename _
  | VS_extern_spec _ -> empty (* ignore these at the moment *)
  | VS_val_spec (typschm,id) -> empty
(* separate space [string "val"; doc_id_lem id; string ":";doc_typschm_lem regtypes typschm] ^/^ hardline *)


let rec doc_def_lem regtypes def = match def with
  | DEF_spec v_spec -> ((doc_spec_lem regtypes v_spec,empty),empty)
  | DEF_type t_def ->
     let (typdefs,fromtodefs) = doc_typdef_lem regtypes t_def in
     ((group typdefs ^/^ hardline,fromtodefs),empty)
  | DEF_reg_dec dec -> ((group (doc_dec_lem dec),empty),empty)

  | DEF_default df -> ((empty,empty),empty)
  | DEF_fundef f_def -> ((empty,empty),group (doc_fundef_lem regtypes f_def) ^/^ hardline)
  | DEF_val lbind -> ((empty,empty),group (doc_let_lem regtypes lbind) ^/^ hardline)
  | DEF_scattered sdef -> failwith "doc_def_lem: shoulnd't have DEF_scattered at this point"

  | DEF_kind _ -> ((empty,empty),empty)

  | DEF_comm (DC_comm s) -> ((empty,empty),comment (string s))
  | DEF_comm (DC_comm_struct d) ->
     let ((typdefs,tofromdefs),vdefs) = doc_def_lem regtypes d in
     ((empty,empty),comment (typdefs ^^ hardline ^^ tofromdefs ^^ hardline ^^ vdefs))


let doc_defs_lem regtypes (Defs defs) =
  let (typdefs,valdefs) = List.split (List.map (doc_def_lem regtypes) defs) in
  let (typdefs,tofromdefs) = List.split typdefs in
  (separate empty typdefs,separate empty tofromdefs, separate empty valdefs)

let find_regtypes (Defs defs) =
  List.fold_left
    (fun acc def ->
      match def with
      | DEF_type (TD_aux(TD_register (Id_aux (Id tname, _),_,_,_),_)) -> tname :: acc
      | _ -> acc
    ) [] defs


let typ_to_t env =
  Type_check.typ_to_t env false false

let pp_defs_lem
      (types_file,types_modules)
      (prompt_file,prompt_modules)
      (state_file,state_modules)
      (tofrom_file,tofrom_modules)
      d top_line =
  let pp_aux file modules defs = 
    (print file)
      (concat
         [string "(*" ^^ (string top_line) ^^ string "*)";hardline;
          (separate_map hardline)
            (fun lib -> separate space [string "open import";string lib]) modules;hardline;
          defs]);
  in
  

  let regtypes = find_regtypes d in
  let (typdefs,tofromdefs,valdefs) = doc_defs_lem regtypes d in

  pp_aux types_file types_modules typdefs;
  pp_aux prompt_file prompt_modules valdefs;
  pp_aux state_file state_modules valdefs;

  (print tofrom_file)
    (concat
       [string "(*" ^^ (string top_line) ^^ string "*)";hardline;
        (separate_map hardline) (fun lib -> separate space [string "open import";string lib]) tofrom_modules;hardline;
        (separate_map hardline) (fun lib -> separate space [string "     import";string lib]) ["Interp";"Interp_ast"];hardline;
        string "open import Deep_shallow_convert";
        hardline;tofromdefs])
