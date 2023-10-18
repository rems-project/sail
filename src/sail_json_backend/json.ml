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

open Libsail

open Ast
open Ast_defs
open Ast_util

let types = Hashtbl.create 997
let sigs = Hashtbl.create 997
let names = Hashtbl.create 997
let descriptions = Hashtbl.create 997
let operands = Hashtbl.create 997
let encodings = Hashtbl.create 997
let assembly = Hashtbl.create 997
let functions = Hashtbl.create 997
let op_functions = Hashtbl.create 997
let formats = Hashtbl.create 997
let extensions = Hashtbl.create 997

let string_of_arg = function
  | E_aux (E_id id, _) -> "\"" ^ string_of_id id ^ "\""
  | exp -> ("exp " ^ string_of_exp exp)

let rec string_list_of_mpat x = match x with
  | MP_aux (MP_lit ( l ), _) ->
      print_endline ("MP_lit " ^ string_of_lit l);
      [ string_of_lit l ]
  | MP_aux (MP_id ( i ), _) ->
      print_endline ("MP_id " ^ string_of_id i);
      [ string_of_id i ]
  | MP_aux (MP_app ( i, pl ), _) ->
      print_endline ("MP_app " ^ string_of_id i);
      begin match string_of_id i with
      | "spc" | "sep" -> []
      | _ -> let b = List.concat (List.map string_list_of_mpat pl) in
          begin
            print_endline ("<-- MP_app" ^ string_of_id i);
            [ (string_of_id i) ^ "(" ^ (String.concat "," b) ^ ")" ]
          end
      end
  | MP_aux (MP_vector_concat ( mpl ), _) ->
      print_endline "MP_vector_concat";
      List.concat (List.map string_list_of_mpat mpl)
  | MP_aux (MP_string_append ( pl ), _) ->
      print_endline "MP_string_append";
      List.concat (List.map string_list_of_mpat pl)
  | MP_aux (MP_typ ( mp, at ), _) ->
      print_endline "MP_typ";
      begin match at with
      | Typ_aux ( Typ_app (i, _), _ ) ->
            print_endline ("types-add " ^ (List.hd (string_list_of_mpat mp)) ^ ":" ^ (string_of_typ at));
            Hashtbl.add types (List.hd (string_list_of_mpat mp)) (string_of_typ at)
      | _ -> print_endline "Typ_other"
      end;
      string_list_of_mpat mp
  | MP_aux (MP_tuple ( mpl ), _) ->
      print_endline "MP_tuple";
      List.concat (List.map string_list_of_mpat mpl)
  | _ -> assert false

let parse_encdec_mpat mp pb format = match mp with
  | MP_aux (MP_app ( app_id, mpl ), _) ->
      print_endline ("MP_app " ^ string_of_id app_id);
      Hashtbl.add formats (string_of_id app_id) format;
      let operandl = List.concat (List.map string_list_of_mpat mpl) in begin
        List.iter print_endline operandl;
        if not (String.equal (List.hd operandl) "()") then
          Hashtbl.add operands (string_of_id app_id) operandl;
        print_endline "MCL_bidir (right part)";
        match pb with
        | MPat_aux ( MPat_pat (p), _ ) ->
            print_endline ("MPat_pat ");
            List.iter print_endline (string_list_of_mpat p);
            Hashtbl.add encodings (string_of_id app_id) (string_list_of_mpat p)
        | MPat_aux ( MPat_when (p, e), _ ) ->
            print_endline ("MPat_when ");
            List.iter print_endline (string_list_of_mpat p);
            Hashtbl.add encodings (string_of_id app_id) (string_list_of_mpat p)
      end;
      string_of_id app_id
  | _ -> assert false

let rec parse_exp e = match e with
  | E_aux (E_app (f, args), _) ->
      print_endline ("E_app \"" ^ string_of_id f ^ "\" [" ^ Util.string_of_list ", " string_of_arg args ^ "]")
  | _ -> print_endline ("parse_exp other" ^ string_of_exp e)

let rec find_extensions e = match e with
    E_aux (E_block (l), _) -> print_endline "E_block"; []
  | E_aux (E_id (i), _) -> print_endline "E_id"; []
  | E_aux (E_ref _, _) -> print_endline "E_ref"; []
  | E_aux (E_lit _, _) -> print_endline "E_lit"; []
  | E_aux (E_typ _, _) -> print_endline "E_type"; []
  | E_aux (E_app (i, el), _) ->
      print_endline("E_app " ^ (string_of_id i));
      if String.equal (string_of_id i) "extension" then match List.hd el with
          E_aux (E_lit (extension), _) -> [ string_of_lit extension ]
        | _ -> []
      else List.concat (List.map find_extensions el)
  | E_aux (E_app_infix _, _) -> print_endline "E_app_infix"; []
  | E_aux (E_tuple _, _) -> print_endline "E_tuple"; []
  | E_aux (E_if _, _) -> print_endline "E_if"; []
  | E_aux (E_loop _, _) -> print_endline "E_loop"; []
  | E_aux (E_for _, _) -> print_endline "E_for"; []
  | E_aux (E_vector _, _) -> print_endline "E_vector"; []
  | E_aux (E_vector_access _, _) -> print_endline "E_vector_access"; []
  | E_aux (E_vector_subrange _, _) -> print_endline "E_vector_subrange"; []
  | E_aux (E_vector_update _, _) -> print_endline "E_vector_update"; []
  | E_aux (E_vector_update_subrange _, _) -> print_endline "E_vector_update_subrange"; []
  | E_aux (E_vector_append _, _) -> print_endline "E_vector_append"; []
  | E_aux (E_list _, _) -> print_endline "E_list"; []
  | E_aux (E_cons _, _) -> print_endline "E_cons"; []
  | E_aux (E_struct _, _) -> print_endline "E_struct"; []
  | E_aux (E_struct_update _, _) -> print_endline "E_struct_update"; []
  | E_aux (E_field _, _) -> print_endline "E_field"; []
  | E_aux (E_match _, _) -> print_endline "E_match"; []
  | E_aux (E_let _, _) -> print_endline "E_let"; []
  | E_aux (E_assign _, _) -> print_endline "E_assign"; []
  | E_aux (E_sizeof _, _) -> print_endline "E_sizeof"; []
  | E_aux (E_constraint _, _) -> print_endline "E_constraint"; []
  | E_aux (E_exit _, _) -> print_endline "E_exit"; []
  | E_aux (E_throw _, _) -> print_endline "E_throw"; []
  | E_aux (E_try _, _) -> print_endline "E_try"; []
  | E_aux (E_return _, _) -> print_endline "E_return"; []
  | E_aux (E_assert _, _) -> print_endline "E_assert"; []
  | E_aux (E_var _, _) -> print_endline "E_var"; []
  | _ -> print_endline "E other"; []

let parse_encdec i mc format = match mc with
  | MCL_aux ( MCL_bidir ( pa, pb ), _ ) ->
      print_endline "MCL_bidir (left part)";
      begin match pa with
      | MPat_aux ( MPat_pat (p), _ ) ->
          let key = parse_encdec_mpat p pb format in
            print_endline ("MPat_pat ");
      | MPat_aux ( MPat_when (p, e), _ ) ->
          print_endline ("MPat_when ENCDEC " ^ (string_of_exp e));
          let key = parse_encdec_mpat p pb format in begin
            print_endline ("MPat_when ");
            List.iter print_endline (find_extensions e);
            Hashtbl.add extensions key (find_extensions e)
          end
      end
  | _ -> assert false

let add_assembly app_id p = 
  let x = string_list_of_mpat p in
    begin
      (* We only support "simple" assembly at the moment,
         where the quoted literal mnemonic is in the statement. *)
      if String.get (List.hd x) 0 = '"' then begin
        print_endline ("assembly.add " ^ string_of_id app_id ^ " : " ^ List.hd x);
        Hashtbl.add assembly (string_of_id app_id) x
      end
    end

let parse_assembly_mpat mp pb = match mp with
  | MP_aux (MP_app ( app_id, mpl ), _) ->
      print_endline ("MP_app " ^ string_of_id app_id);
      let operandl = List.concat (List.map string_list_of_mpat mpl) in
      begin
        List.iter print_endline operandl;
        if not (String.equal (List.hd operandl) "()") then
          Hashtbl.add operands (string_of_id app_id) operandl;
        print_endline "MCL_bidir (right part)";
        match pb with
        | MPat_aux ( MPat_pat (p), _ ) ->
            print_endline ("MPat_pat assembly");
            add_assembly app_id p
        | MPat_aux ( MPat_when (p, e), _ ) ->
            print_endline ("MPat_when assembly");
            add_assembly app_id p
      end
  | _ -> assert false

let parse_assembly i mc = match mc with
  | MCL_aux ( MCL_bidir ( pa, pb ), _ ) ->
      print_endline "MCL_bidir";
      begin match pa with
      | MPat_aux ( MPat_pat (p), _ ) ->
          print_endline ("MPat_pat ");
          parse_assembly_mpat p pb
      | MPat_aux ( MPat_when (p, e), _ ) ->
          print_endline ("MPat_when ");
          parse_assembly_mpat p pb
      end
  | _ -> assert false

let rec parse_mpat x = match x with
  | MP_aux (MP_lit ( l ), _) -> print_endline ("MP_lit " ^ string_of_lit l)
  | MP_aux (MP_id ( i ), _) -> print_endline ("MP_id " ^ string_of_id i)
  | MP_aux (MP_app ( i, pl ), _) ->
      print_endline ("MP_app " ^ (string_of_id i) ^ " -->");
      List.iter parse_mpat pl;
      print_endline ("<-- MP_app " ^ (string_of_id i))
  | MP_aux (MP_vector_concat ( mpl ), _) ->
      print_endline "MP_vector_concat";
      List.iter parse_mpat mpl
  | MP_aux (MP_string_append ( pl ), _) ->
      print_endline "MP_string_append";
      List.iter parse_mpat pl
  | MP_aux (MP_typ ( mp, at ), _) ->
      print_endline "MP_typ";
      parse_mpat mp
  | _ -> print_endline "mpat other"

let parse_MPat_aux p = match p with
  | MPat_aux ( MPat_pat (p), _ ) ->
      print_endline ("MPat_pat " ^ string_of_mpat p);
      parse_mpat p
  | MPat_aux ( MPat_when (p, e), _ ) ->
      print_endline ("MPat_when " ^ (string_of_mpat p) ^ " when " ^ (string_of_exp e));
      parse_mpat p;
      parse_exp e

let parse_mapcl i mc =
  print_endline ("mapcl " ^ string_of_id i);
  begin match mc with
  | MCL_aux (_, (annot, _)) ->
      begin match annot.doc_comment with
          None -> ()
        | Some s -> print_endline ("MAP DOC " ^ s)
      end;
      List.iter (fun attr ->
        match attr with
          (_, s0, s1) -> print_endline ("MAP ATTR " ^ s0 ^ ": " ^ s1)
      ) annot.attrs
  end;
  let format = match mc with
    | MCL_aux (_, (annot, _)) ->
        String.concat "-" (List.map (fun attr ->
          match attr with
            (_, "format", s1) -> s1
            | _ -> ""
        ) annot.attrs)
    in begin
      print_endline ("FORMAT " ^ format);
      match string_of_id i with
        "encdec" | "encdec_compressed" ->
          print_endline (string_of_id i);
          parse_encdec i mc format
      | "assembly" ->
          print_endline (string_of_id i);
          parse_assembly i mc
      | _ -> ();
    end;
  match mc with
  | MCL_aux ( MCL_bidir ( pa, pb ), _ ) ->
      parse_MPat_aux pa;
      parse_MPat_aux pb
  | _ -> print_endline "mapcl other"

let parse_type_union i ucl =
  print_endline ("type_union " ^ string_of_id i);
  begin match ucl with
  | Tu_aux (_, annot) ->
      begin match annot.doc_comment with
          None -> ()
        | Some s -> print_endline ("DOC " ^ s)
      end;
      List.iter (fun attr ->
        match attr with
          (_, s0, s1) -> print_endline ("ATTR " ^ s0 ^ ": " ^ s1)
      ) annot.attrs
  end;
  match ucl with
  | Tu_aux ( Tu_ty_id ( c, d ), annot ) ->
      print_string ("Tu_ty_id " ^ string_of_id d ^ "(");
      begin match c with
      | Typ_aux ( Typ_tuple ( x ), _ ) ->
          List.iter (fun x0 ->
              let type_name = string_of_typ x0 in
                let type_type = try Hashtbl.find types (string_of_typ x0)
                  with Not_found -> "None"
                in print_string (type_name ^ ":" ^ type_type ^ " ")
          ) x;
          let l = List.map string_of_typ x in
            Hashtbl.add sigs (string_of_id d) l;
          List.iter (fun attr ->
            match attr with
              (_, "name", s) -> Hashtbl.add names (string_of_id d) s
              | _ -> ()
          ) annot.attrs;
          begin match annot.doc_comment with
              None -> ()
            | Some s -> Hashtbl.add descriptions (string_of_id d) s
          end
      | Typ_aux ( Typ_id (i), _ ) ->
          Hashtbl.add sigs (string_of_id d) [string_of_id i]
      | Typ_aux ( Typ_app (i, _), _ ) ->
            print_endline (string_of_typ c);
            Hashtbl.add sigs (string_of_id d) [string_of_typ c]
      | _ -> print_endline "Tu_ty_id other"
      end;
      print_endline ")"

let parse_DEF_type def =
  print_endline "DEF_type";
  match def with
  | TD_aux (TD_abbrev (d, e, f), _) ->
    print_endline ( "TD_abbrev " ^ string_of_id d ^ ":" ^ string_of_typ_arg f);
    Hashtbl.add types (string_of_id d) (string_of_typ_arg f);
  | TD_aux ( TD_record (d, e, f, g), _) -> print_endline ( "TD_record " ^ string_of_id d )
  | TD_aux ( TD_variant (d, e, f, g), _) ->
      print_endline ( "TD_variant " ^ string_of_id d );
      List.iter (parse_type_union d) f
  | TD_aux ( TD_enum (d, e, f), _) -> print_endline ( "TD_enum " ^ string_of_id d )
  | TD_aux ( TD_bitfield (d, e, f), _) -> print_endline ( "TD_bitfield " ^ string_of_id d )

let parse_execute p e =
  let x = match p with
        P_aux ( P_app (i, pl), _ ) ->
          print_endline ("P_app " ^ string_of_id i);
          string_of_id i
      | _ -> raise (Failure "pat other")
    in begin
      print_endline "<- pat";
      print_endline "exp -> ";
      print_endline (string_of_exp e);
      print_endline "<- exp";
      Hashtbl.add functions x (string_of_exp e)
    end

let parse_funcl fcl =
  print_endline "funcl";
  match fcl with
  | FCL_aux ( FCL_funcl ( i, Pat_aux ( j, _ ) ), _ ) ->
      print_endline ("FCL_funcl " ^ string_of_id i);
      if (string_of_id i) = "execute" then begin
        match j with
        | Pat_exp ( p, e ) -> (* parse_exp e *)
            print_endline "Pat_exp";
            print_endline (string_of_pat p);
            print_endline "pat -> ";
            begin match p with
                P_aux ( P_app (x, pl), _ ) ->
                  print_endline ("P_app " ^ string_of_id x);
              | _ -> print_endline "pat other"
            end;
            print_endline "<- pat";
            print_endline "exp -> ";
            print_endline (string_of_exp e);
            print_endline "<- exp";
            parse_execute p e
        | Pat_when ( p, e, w ) ->
            print_endline "Pat_when";
            print_endline (string_of_pat p);
            print_endline (string_of_exp e);
            print_endline (string_of_exp w);
            parse_execute p e
      end

let json_of_operand op = "\"" ^ op ^ "\""

let json_of_key_operand key op t =
  "\n{\n" ^
  "  \"name\": \"" ^ op ^ "\", \"type\": \"" ^ t ^ "\"\n" ^
  "}"

let json_of_operands k =
  let ops = Hashtbl.find_opt operands k
  and types = Hashtbl.find_opt sigs k in
    match (ops, types) with
      (Some opslist, Some typeslist) ->
        let fk = json_of_key_operand k in
          String.concat ", " (List.map2 fk opslist typeslist)
    | (_, _) -> ""

let rec basetype t =
  match Hashtbl.find_opt types t with
    None -> t
  | Some bt -> basetype bt

let extract_func_arg s =
    List.hd (String.split_on_char ')' (List.hd (List.tl ((String.split_on_char '(' s)))))

let rec string_of_sizeof_field k f =
  print_endline ("string_of_sizeof_field " ^ k ^ ":" ^ f);
  if String.starts_with ~prefix:"0b" f then string_of_int (String.length f - 2)
  else if String.contains f '(' then
    if String.starts_with ~prefix:"bits(" f then
      extract_func_arg f
    else
      let op_func = List.hd (String.split_on_char '(' f) in
        let op_type = Hashtbl.find_opt op_functions op_func in match op_type with
            Some s -> s
          | None -> "0"
  else
    let opmap = List.combine (Hashtbl.find operands k) (Hashtbl.find sigs k) in
      begin
        match List.assoc_opt f opmap with
          Some t ->
            let bt = basetype t in
              if bt = "bool" then
                "1"
              else if String.starts_with ~prefix:"bits(" bt then
                extract_func_arg bt
              else begin
                print_endline ("unfamiliar base type " ^ bt);
                "72"
              end
        | None ->
            match Hashtbl.find_opt types f with
                Some t ->
                  string_of_sizeof_field k t
              | None ->
                  print_endline ("not found " ^ f);
                  "0"
      end

let json_of_field k f =
  "{ \"field\": \"" ^ f ^ "\", \"size\": " ^ string_of_sizeof_field k f ^ " }"

let json_of_fields k =
  match Hashtbl.find_opt encodings k with
    None -> ""
  | Some (fields) -> String.concat ", " (List.map (fun f -> json_of_field k f) fields)

let json_of_function k =
  match Hashtbl.find_opt functions k with
    None -> ""
  | Some (f) -> String.escaped f

let json_of_name k =
  match Hashtbl.find_opt names k with
    None -> "TBD"
  | Some (f) -> String.escaped f

let json_of_description k =
  match Hashtbl.find_opt descriptions k with
    None -> "TBD"
  | Some (f) -> String.escaped f

let json_of_format k =
  match Hashtbl.find_opt formats k with
    None -> "TBD"
  | Some (f) -> match f with
        "" -> "TBD"
      | s -> String.escaped s

let json_of_extensions k =
  match Hashtbl.find_opt extensions k with
    None -> ""
  | Some (l) -> String.concat "," l

let json_of_instruction k =
  let m = Hashtbl.find assembly k in
    "{\n" ^
    "  \"mnemonic\": " ^ List.hd m ^ ",\n" ^
    "  \"name\": \"" ^ (json_of_name k) ^ "\",\n" ^
    "  \"operands\": [ " ^ (json_of_operands k) ^ " ],\n" ^
    "  \"format\": \"" ^ (json_of_format k) ^ "\",\n" ^
    "  \"fields\": [ " ^ (json_of_fields k) ^ " ],\n" ^
    "  \"extensions\": [ " ^ (json_of_extensions k) ^ " ],\n" ^
    "  \"function\": \"" ^ (json_of_function k) ^ "\",\n" ^
    "  \"description\": \"" ^ (json_of_description k) ^ "\"\n" ^
    "}"

let rec parse_typ name t = match t with
    Typ_aux (Typ_bidir (tl, tr), _) ->
      print_endline "Typ_bidir";
      parse_typ name tl; parse_typ name tr
  | Typ_aux (Typ_app (id, args), _) -> print_endline (string_of_id id);
      print_endline (string_of_id id ^ "(" ^ (String.concat ", " (List.map string_of_typ_arg args)) ^ ")");
      begin match string_of_id id with
          "bitvector" ->
            print_endline (string_of_typ_arg (List.hd args));
            Hashtbl.add op_functions name (string_of_typ_arg (List.hd args))
        | _ -> print_endline "Typ_app other"
      end
  | _ -> print_endline "typ other"

let parse_typschm name ts = match ts with
    TypSchm_aux ( TypSchm_ts ( _, x ), _ ) ->
      parse_typ name x (* This compiles as if x is a 'typ' instead of 'atyp' (?) *)

let defs { defs; _ } =
  List.iter (fun def ->
    begin match def with
      DEF_aux (_, annot) ->
        begin match annot.doc_comment with
            None -> ()
          | Some s -> print_endline s;
        end;
        List.iter (fun attr ->
          match attr with
            (_, s0, s1) -> print_endline ("ATTR " ^ s0 ^ ": " ^ s1)
        ) annot.attrs
    end;
    match def with
      DEF_aux (DEF_type ( def ), _) -> parse_DEF_type def
    | DEF_aux (DEF_val ( vs ), _) ->
        print_endline "DEF_val";
        begin match vs with
          VS_aux ( VS_val_spec (ts, i, _), _) ->
            parse_typschm (string_of_id i) ts
        end
    | DEF_aux (DEF_fundef (FD_aux (FD_function (Rec_aux (_, _), Typ_annot_opt_aux(_, _), fl), _)), _) ->
        print_endline "DEF_fundef";
        List.iter parse_funcl fl
    | DEF_aux (DEF_mapdef (MD_aux (MD_mapping (i, _, ml), _)), _) ->
        print_endline "DEF_mapdef";
        List.iter (parse_mapcl i) ml
    | _ -> print_string ""
  ) defs;

  print_endline "TYPES";
  Hashtbl.iter (fun k v -> print_endline (k ^ ":" ^ v)) types;
  print_endline "SIGS";
  Hashtbl.iter (fun k v -> print_endline (k ^ ":" ^ Util.string_of_list ", " (fun x -> x) v)) sigs;
  print_endline "NAMES";
  Hashtbl.iter (fun k v -> print_endline (k ^ ":" ^ v)) names;
  print_endline "DESCRIPTIONS";
  Hashtbl.iter (fun k v -> print_endline (k ^ ":" ^ v)) descriptions;
  print_endline "OPERANDS";
  Hashtbl.iter (fun k v -> print_endline (k ^ ":" ^ Util.string_of_list ", " (fun x -> x) v)) operands;
  print_endline "ENCODINGS";
  Hashtbl.iter (fun k v -> print_endline (k ^ ":" ^ Util.string_of_list ", " (fun x -> x) v)) encodings;
  print_endline "ASSEMBLY";
  Hashtbl.iter (fun k v -> print_endline (k ^ ":" ^ Util.string_of_list ", " (fun x -> x) v)) assembly;
  print_endline "FUNCTIONS";
  Hashtbl.iter (fun k v -> print_endline (k ^ ":" ^ v)) functions;
  print_endline "OP_FUNCTIONS";
  Hashtbl.iter (fun k v -> print_endline (k ^ ":" ^ v)) op_functions;
  print_endline "EXENSIONS";
  Hashtbl.iter (fun k v -> print_endline (k ^ ":" ^ (String.concat "," v))) extensions;
  print_endline "FORMATS";
  Hashtbl.iter (fun k v -> print_endline (k ^ ":" ^ v)) formats;

  print_endline "{";
  print_endline "  \"instructions\": [";

  (* Join keys and mnemonics, then sort by mnemonic, then use the keys in that order to emit instructions *)
  let keys_sorted_by_mnemonic =
    let key_mnemonic_sorted =
      let key_mnemonic_map = Hashtbl.fold (fun k v init -> [k; List.hd v] :: init) assembly [] in
        List.sort (fun l r -> String.compare (List.hd (List.tl l)) (List.hd (List.tl r))) key_mnemonic_map in
          List.map List.hd key_mnemonic_sorted in
            print_endline (String.concat ",\n" (List.map json_of_instruction keys_sorted_by_mnemonic));

  print_endline "  ],";
  print_endline "  \"formats\": [";
  let format_list = Hashtbl.fold (fun k v accum -> (("\"" ^ v ^ "\"") :: accum)) formats [] in
    print_endline (String.concat ",\n" (List.fold_right (fun s accum -> if String.equal "\"\"" s then accum else (s :: accum)) (List.sort_uniq String.compare ("\"TBD\"" :: format_list)) []));
  print_endline "  ],";
  print_endline "  \"extensions\": [";
  let extension_list = Hashtbl.fold (fun k v accum -> v :: accum) extensions [] in
    print_endline (String.concat ",\n" (List.sort_uniq String.compare (List.concat extension_list)));
  print_endline "  ]";
  print_endline "}";
