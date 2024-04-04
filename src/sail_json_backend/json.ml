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

let debug_enabled =
  match Sys.getenv_opt "SAIL_DEBUG" with
  | Some value -> value = "1" || int_of_string_opt value = Some 1
  | None -> false

let types = Hashtbl.create 997
let sigs = Hashtbl.create 997
let names = Hashtbl.create 997
let descriptions = Hashtbl.create 997
let operands = Hashtbl.create 997
let encodings = Hashtbl.create 997
let assembly = Hashtbl.create 997
let assembly_clean = Hashtbl.create 997
let functions = Hashtbl.create 997
let op_functions = Hashtbl.create 997
let formats = Hashtbl.create 997
let extensions = Hashtbl.create 997
let mappings = Hashtbl.create 997

let debug_print ?(printer=prerr_endline) message =
  if debug_enabled then
    printer message
  else
    ()

let dequote qs =
  if String.starts_with ~prefix:"\"" qs && String.ends_with ~suffix:"\"" qs then
    List.hd (List.tl (String.split_on_char '"' qs))
  else
    qs

let string_of_arg = function
  | E_aux (E_id id, _) -> "\"" ^ string_of_id id ^ "\""
  | exp -> ("exp " ^ string_of_exp exp)

let rec string_list_of_mpat x = match x with
  | MP_aux (MP_lit ( l ), _) ->
      debug_print ("MP_lit " ^ string_of_lit l);
      [ dequote (string_of_lit l) ]
  | MP_aux (MP_id ( i ), _) ->
      debug_print ("MP_id " ^ string_of_id i);
      [ string_of_id i ]
  | MP_aux (MP_app ( i, pl ), _) ->
      debug_print ("MP_app " ^ string_of_id i);
      begin match string_of_id i with
      | "spc" -> [ string_of_id i ]
      | "sep" -> [ string_of_id i ]
      | _ -> let b = List.concat (List.map string_list_of_mpat pl) in
          begin
            debug_print ("<-- MP_app " ^ string_of_id i);
            [ (string_of_id i) ^ "(" ^ (String.concat "," b) ^ ")" ]
          end
      end
  | MP_aux (MP_vector_concat ( mpl ), _) ->
      debug_print "MP_vector_concat";
      List.concat (List.map string_list_of_mpat mpl)
  | MP_aux (MP_string_append ( pl ), _) ->
      debug_print "MP_string_append";
      List.concat (List.map string_list_of_mpat pl)
  | MP_aux (MP_typ ( mp, at ), _) ->
      debug_print "MP_typ";
      begin match at with
      | Typ_aux ( Typ_app (i, _), _ ) ->
            debug_print ("types-add " ^ (List.hd (string_list_of_mpat mp)) ^ ":" ^ (string_of_typ at));
            Hashtbl.add types (List.hd (string_list_of_mpat mp)) (string_of_typ at)
      | Typ_aux ( Typ_id i, _ ) ->
            debug_print ("types-add " ^ (List.hd (string_list_of_mpat mp)) ^ ":" ^ (string_of_id i));
            Hashtbl.add types (List.hd (string_list_of_mpat mp)) (string_of_id i)
      | _ -> debug_print "Typ_other"
      end;
      string_list_of_mpat mp
  | MP_aux (MP_tuple ( mpl ), _) ->
      debug_print "MP_tuple";
      List.concat (List.map string_list_of_mpat mpl)
  | _ -> assert false

let parse_encdec_mpat mp pb format = match mp with
  | MP_aux (MP_app ( app_id, mpl ), _) ->
      debug_print ("MP_app " ^ string_of_id app_id);
      Hashtbl.add formats (string_of_id app_id) format;
      let operandl = List.concat (List.map string_list_of_mpat mpl) in begin
        List.iter (debug_print) operandl;
        debug_print "MCL_bidir (right part)";
        match pb with
        | MPat_aux ( MPat_pat (p), _ ) ->
            debug_print ("MPat_pat ");
            List.iter (debug_print) (string_list_of_mpat p);
            Hashtbl.add encodings (string_of_id app_id) (string_list_of_mpat p)
        | MPat_aux ( MPat_when (p, e), _ ) ->
            debug_print ("MPat_when ");
            List.iter (debug_print) (string_list_of_mpat p);
            Hashtbl.add encodings (string_of_id app_id) (string_list_of_mpat p)
      end;
      string_of_id app_id
  | _ -> assert false

(* This looks for any "extension(string)", and does not, for example
   account for negation. This case should be pretty unlikely, however. *)
let rec find_extensions e = match e with
    E_aux (E_app (i, el), _) ->
      debug_print("E_app " ^ (string_of_id i));
      if String.equal (string_of_id i) "extension" then match List.hd el with
          E_aux (E_lit (extension), _) -> [ string_of_lit extension ]
        | _ -> []
      else List.concat (List.map find_extensions el)
  | _ -> debug_print "E other"; []

let parse_encdec i mc format = match mc with
  | MCL_aux ( MCL_bidir ( pa, pb ), _ ) ->
      debug_print "MCL_bidir (left part)";
      begin match pa with
      | MPat_aux ( MPat_pat (p), _ ) ->
          let key = parse_encdec_mpat p pb format in
            debug_print ("MPat_pat ");
      | MPat_aux ( MPat_when (p, e), _ ) ->
          debug_print ("MPat_when ENCDEC " ^ (string_of_exp e));
          let key = parse_encdec_mpat p pb format in begin
            debug_print ("MPat_when ");
            List.iter (debug_print) (find_extensions e);
            Hashtbl.add extensions key (find_extensions e)
          end
      end
  | _ -> assert false

let add_assembly app_id p = 
  let x = string_list_of_mpat p in
    begin
      debug_print ("assembly.add " ^ string_of_id app_id ^ " : " ^ List.hd x);
      Hashtbl.add assembly (string_of_id app_id) x
    end

let parse_assembly_mpat mp pb = match mp with
  | MP_aux (MP_app ( app_id, mpl ), _) ->
      debug_print ("MP_app " ^ string_of_id app_id);
      let operandl = List.concat (List.map string_list_of_mpat mpl) in
      begin
        List.iter (debug_print) operandl;
        debug_print "MCL_bidir (right part)";
        match pb with
        | MPat_aux ( MPat_pat (p), _ ) ->
            debug_print ("MPat_pat assembly");
            add_assembly app_id p
        | MPat_aux ( MPat_when (p, e), _ ) ->
            debug_print ("MPat_when assembly");
            add_assembly app_id p
      end
  | _ -> assert false

let parse_assembly i mc = match mc with
  | MCL_aux ( MCL_bidir ( pa, pb ), _ ) ->
      debug_print "MCL_bidir";
      begin match pa with
      | MPat_aux ( MPat_pat (p), _ ) ->
          debug_print ("MPat_pat ");
          parse_assembly_mpat p pb
      | MPat_aux ( MPat_when (p, e), _ ) ->
          debug_print ("MPat_when ");
          parse_assembly_mpat p pb
      end
  | _ -> assert false

let parse_mapcl i mc =
  debug_print ("mapcl " ^ string_of_id i);
  let format = match mc with MCL_aux (_, (annot, _)) ->
      String.concat "-" (List.map (fun attr ->
        match attr with
          (_, "format", s) -> s
          | _ -> ""
      ) annot.attrs)
    in begin
      match string_of_id i with
        "encdec" | "encdec_compressed" ->
          debug_print (string_of_id i);
          parse_encdec i mc format
      | "assembly" ->
          debug_print (string_of_id i);
          parse_assembly i mc
      | _ ->
          begin match mc with
            | MCL_aux (MCL_bidir (MPat_aux (MPat_pat mpl, _), MPat_aux (MPat_pat mpr, _)), _) ->
                debug_print ("MCL_bidir " ^ (string_of_id i));
                let sl = string_list_of_mpat mpl in
                  List.iter (fun s -> debug_print ("L: " ^ s)) sl;
                let sl = string_list_of_mpat mpr in
                  List.iter (fun s -> debug_print ("R: " ^ s)) sl;
                Hashtbl.add mappings (string_of_id i) ((string_list_of_mpat mpl), (string_list_of_mpat mpr))
            | _ -> debug_print "MCL other";
          end
    end

let parse_type_union i ucl =
  debug_print ("type_union " ^ string_of_id i);
  match ucl with
  | Tu_aux ( Tu_ty_id ( c, d ), annot ) ->
      debug_print ~printer:prerr_string ("Tu_ty_id " ^ string_of_id d ^ "(");
      begin match c with
      | Typ_aux ( Typ_tuple ( x ), _ ) ->
          List.iter (fun x0 ->
              let type_name = string_of_typ x0 in
                let type_type = try Hashtbl.find types (string_of_typ x0)
                  with Not_found -> "None"
                in 
                debug_print ~printer:prerr_string (type_name ^ ":" ^ type_type ^ " ")
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
          debug_print (string_of_typ c);
          Hashtbl.add sigs (string_of_id d) [string_of_typ c]
      | _ -> debug_print "Tu_ty_id other"
      end;
      debug_print ")"

let parse_DEF_type def =
  debug_print "DEF_type";
  match def with
  | TD_aux (TD_abbrev (d, e, f), _) ->
    debug_print ( "TD_abbrev " ^ string_of_id d ^ ":" ^ string_of_typ_arg f);
    Hashtbl.add types (string_of_id d) (string_of_typ_arg f);
  | TD_aux ( TD_variant (d, e, f, g), _) ->
      debug_print ( "TD_variant " ^ string_of_id d );
      List.iter (parse_type_union d) f
  | _ -> debug_print "TD other"

let rec string_list_of_pat p = match p with
    P_aux (P_lit l, _) ->
        debug_print ("P_lit " ^ (string_of_lit l));
        [ string_of_lit l ]
  | P_aux (P_id i, _) ->
        debug_print ("P_id " ^ (string_of_id i));
        [ string_of_id i ]
  | P_aux (P_tuple pl, _) ->
        debug_print "P_tuple ->";
        let l = List.concat (List.map string_list_of_pat pl) in
          debug_print "<- P_tuple";
          l
  | _ -> debug_print "pat other"; []

let extract_source_code l =
   match Reporting.simp_loc l with
   | Some(p1, p2) -> (Reporting.loc_range_to_src p1 p2)
   | None -> "Error - couldn't locate func"

let parse_funcl fcl = match fcl with
    FCL_aux ( FCL_funcl ( Id_aux (Id "execute", _), Pat_aux ( (
          Pat_exp ( P_aux ( P_app (i, pl), _ ) , e )
        | Pat_when ( P_aux ( P_app (i, pl), _ ) , e, _ )
      ), _ ) ), _ ) ->
      begin
        debug_print ("FCL_funcl execute " ^ string_of_id i);
        let operandl = (List.concat (List.map string_list_of_pat pl)) in
          if not (String.equal (List.hd operandl) "()") then
            Hashtbl.add operands (string_of_id i) operandl;
        Hashtbl.add functions (string_of_id i) (extract_source_code (Ast_util.exp_loc e))
      end
  | _ -> debug_print "FCL_funcl other"

let json_of_key_operand key op t =
  "\n{\n" ^
  "  \"name\": \"" ^ op ^ "\", \"type\": \"" ^ t ^ "\"\n" ^
  "}"

let json_of_mnemonic m = "\"" ^ m ^ "\""

(* For stripping the wrapper functions from the operand names
   reg_name(rd) -> rd
   Note that this is not ideal, as it would be far preferable for this parser
   to know nothing about specific function names in the Sail code.  :-/
*)

let identity_funcs = [
  "csr_name_map";
  "fence_bits";
  "frm_mnemonic";
  "hex_bits_2";
  "hex_bits_4";
  "hex_bits_5";
  "hex_bits_6";
  "hex_bits_7";
  "hex_bits_8";
  "hex_bits_10";
  "hex_bits_11";
  "hex_bits_12";
  "hex_bits_13";
  "hex_bits_16";
  "hex_bits_20";
  "hex_bits_21";
  "hex_bits_32";
  "reg_name";
  "creg_name";
  "freg_name";
  "freg_or_reg_name";
  "vreg_name";
  "maybe_vmask"
]

let defunction f n =
  if String.starts_with ~prefix:(n ^ "(") f then
    String.sub f (String.length n + 1) (String.length f - String.length n - 2)
  else
    f

let remove_identity_funcs op =
  List.fold_left (fun accum f ->
    let op = defunction accum f in
      if String.equal accum op then accum
      else op
  ) op identity_funcs

let json_of_operand k op =
  debug_print ("json_of_operand " ^ k ^ ":" ^ op);
  let opmap = List.combine (Hashtbl.find operands k) (Hashtbl.find sigs k) in
    let opplus = remove_identity_funcs op in
      let opname = List.hd (String.split_on_char ',' opplus) in
        match List.find_opt (fun (name, t) -> String.equal name opname) opmap with
            Some (name, t) -> "{ \"name\": \"" ^ name ^ "\", \"type\": \"" ^ t ^ "\" }"
          | None -> "{ \"name\": \"" ^ opname ^ "\", \"type\": \"unknown\" }"

let json_of_operands k ops =
  String.concat "," (
    List.map (fun op -> json_of_operand k op) (
      List.filter (
        fun s -> not (
          (String.equal s "(") ||
          (String.equal s ")") ||
          (String.equal s "spc") ||
          (String.equal s "sep")
        )
      )
      ops
    )
  )

let json_of_syntax k =
  let l = List.map (fun s ->
    if String.equal s "sep" then ","
    else if String.equal s "\"(\"" then "("
    else if String.equal s "\")\"" then ")"
    else (remove_identity_funcs s)) (List.tl (Hashtbl.find assembly_clean k)) in
      if List.length l > 0 then (String.concat "" l)
      else ""

let rec basetype t =
  match Hashtbl.find_opt types t with
    None -> t
  | Some bt -> basetype bt

let extract_func_arg s =
    List.hd (String.split_on_char ')' (List.hd (List.tl ((String.split_on_char '(' s)))))

let rec string_of_sizeof_field k f =
  debug_print ("string_of_sizeof_field " ^ k ^ ":" ^ f);

  if String.starts_with ~prefix:"0b" f then
    (* binary literal "0b..." *)
    string_of_int (String.length f - 2)

  else if String.contains f '(' then

    if String.starts_with ~prefix:"bits(" f then
      (* bits(n) *)
      extract_func_arg f

    else
      let op_func = List.hd (String.split_on_char '(' f) in
        let op_type = Hashtbl.find_opt op_functions op_func in match op_type with
            Some s -> s
          | None -> "0" (* TODO: needs work *)

  else begin
    (* match operand names to function signature types *)
    let opmap = List.combine (Hashtbl.find operands k) (Hashtbl.find sigs k) in
      begin
        (* find matching operand type *)
        match List.assoc_opt f opmap with
          Some t ->
            (* try to drill down to a base type *)
            let bt = basetype t in
              if bt = "bool" then
                "1"
              else if String.starts_with ~prefix:"bits(" bt then
                extract_func_arg bt
              else begin
                debug_print ("unfamiliar base type " ^ bt);
                "72" (* TODO: needs work *)
              end
        | None ->
            match Hashtbl.find_opt types f with
                Some t ->
                  string_of_sizeof_field k t
              | None ->
                  debug_print ("not found " ^ f);
                  "0" (* TODO: needs work *)
      end
  end

let json_of_field k f =
  "{ \"field\": \"" ^ f ^ "\", \"size\": " ^ string_of_sizeof_field k f ^ " }"

let json_of_fields k =
  match Hashtbl.find_opt encodings k with
    None -> ""
  | Some (fields) -> String.concat ", " (List.map (fun f -> json_of_field k f) fields)

let json_of_function k =
  let fspec = match Hashtbl.find_opt functions k with
      None -> ""
    | Some (f) -> String.escaped f
  in "\"" ^ fspec ^ "\""

let json_of_name k =
  let name = match Hashtbl.find_opt names k with
      None -> "TBD"
    | Some (f) -> String.escaped f
  in "\"" ^ name ^ "\""

let json_of_description k =
  let description = match Hashtbl.find_opt descriptions k with
      None -> "TBD"
    | Some (f) -> String.escaped f
  in "\"" ^ description ^ "\""

let json_of_format k =
  let format = match Hashtbl.find_opt formats k with
      None -> "TBD"
    | Some (f) -> match f with
          "" -> "TBD"
        | s -> String.escaped s
  in "\"" ^ format ^ "\""

let json_of_extensions k =
  match Hashtbl.find_opt extensions k with
    None -> ""
  | Some (l) -> String.concat "," l

let json_of_instruction k v =
    "{\n" ^
    "  \"mnemonic\": " ^ (json_of_mnemonic (List.hd v)) ^ ",\n" ^
    "  \"name\": " ^ (json_of_name k) ^ ",\n" ^
    "  \"operands\": [ " ^ (json_of_operands k (List.tl v)) ^ " ],\n" ^
    "  \"syntax\": " ^ "\"" ^ (json_of_syntax k) ^ "\",\n" ^
    "  \"format\": " ^ (json_of_format k) ^ ",\n" ^
    "  \"fields\": [ " ^ (json_of_fields k) ^ " ],\n" ^
    "  \"extensions\": [ " ^ (json_of_extensions k) ^ " ],\n" ^
    "  \"function\": " ^ (json_of_function k) ^ ",\n" ^
    "  \"description\": " ^ (json_of_description k) ^ "\n" ^
    "}"

let rec parse_typ name t = match t with
    Typ_aux (Typ_bidir (tl, tr), _) ->
      debug_print "Typ_bidir";
      parse_typ name tl; parse_typ name tr
  | Typ_aux (Typ_app (id, args), _) -> debug_print (string_of_id id);
      debug_print (string_of_id id ^ "(" ^ (String.concat ", " (List.map string_of_typ_arg args)) ^ ")");
      begin match string_of_id id with
          "bitvector" ->
            debug_print (string_of_typ_arg (List.hd args));
            Hashtbl.add op_functions name (string_of_typ_arg (List.hd args))
        | _ -> debug_print "Typ_app other"
      end
  | _ -> debug_print "typ other"

let explode_mnemonic heads tails =
  List.concat(
    List.map (fun tail ->
      List.map (fun head -> match head with
        (* presuming right side of mapping is a list of a single string *)
        l, r ->
          debug_print (List.hd l);
          ((dequote (List.hd r)) ^ (dequote (List.hd tail))) :: List.tl tail
      ) heads
    ) tails
  )

let rec explode_mnemonics asm =
  if List.length asm == 0 then [ [ "" ] ]
  else if String.equal (List.hd asm) "spc" then [ "" :: List.tl asm ]
  else
    let tails = explode_mnemonics (List.tl asm) in
      if String.ends_with ~suffix:")" (List.hd asm) then begin
        debug_print (extract_func_arg (List.hd asm));
        let heads = Hashtbl.find_all mappings (List.hd (String.split_on_char '(' (List.hd asm))) in
          let found = List.find_opt (fun head ->
                match head with
                    l, _ -> String.equal (List.hd l) (extract_func_arg (List.hd asm))
            ) heads in match found with
                None -> explode_mnemonic heads tails
              | Some head -> explode_mnemonic [ head ] tails
      end
      else
          explode_mnemonic [ ([""], [List.hd asm]) ] tails

let defs { defs; _ } =
  List.iter (fun def ->
    match def with
      DEF_aux (DEF_type ( def ), _) -> parse_DEF_type def
    | DEF_aux (DEF_val ( VS_aux ( VS_val_spec (TypSchm_aux ( TypSchm_ts ( _, t ), _ ), i, _), _) ), _) ->
        parse_typ (string_of_id i) t
    | DEF_aux (DEF_fundef (FD_aux (FD_function (_, _, fl), _)), _) ->
        debug_print "DEF_fundef";
        List.iter parse_funcl fl
    | DEF_aux (DEF_mapdef (MD_aux (MD_mapping (i, _, ml), _)), _) ->
        debug_print "DEF_mapdef";
        List.iter (parse_mapcl i) ml
    | _ -> debug_print ~printer:prerr_string ""
  ) defs;

  debug_print "TYPES";
  Hashtbl.iter (fun k v -> debug_print (k ^ ":" ^ v)) types;
  debug_print "SIGS";
  Hashtbl.iter (fun k v -> debug_print (k ^ ":" ^ Util.string_of_list ", " (fun x -> x) v)) sigs;
  debug_print "NAMES";
  Hashtbl.iter (fun k v -> debug_print (k ^ ":" ^ v)) names;
  debug_print "DESCRIPTIONS";
  Hashtbl.iter (fun k v -> debug_print (k ^ ":" ^ v)) descriptions;
  debug_print "OPERANDS";
  Hashtbl.iter (fun k v -> debug_print (k ^ ":" ^ Util.string_of_list ", " (fun x -> x) v)) operands;
  debug_print "ENCODINGS";
  Hashtbl.iter (fun k v -> debug_print (k ^ ":" ^ Util.string_of_list ", " (fun x -> x) v)) encodings;
  debug_print "ASSEMBLY";
  Hashtbl.iter (fun k v -> debug_print (k ^ ":" ^ Util.string_of_list ", " (fun x -> x) v)) assembly;
  debug_print "FUNCTIONS";
  Hashtbl.iter (fun k v -> debug_print (k ^ ":" ^ v)) functions;
  debug_print "OP_FUNCTIONS";
  Hashtbl.iter (fun k v -> debug_print (k ^ ":" ^ v)) op_functions;
  debug_print "EXENSIONS";
  Hashtbl.iter (fun k v -> debug_print (k ^ ":" ^ (String.concat "," v))) extensions;
  debug_print "FORMATS";
  Hashtbl.iter (fun k v -> debug_print (k ^ ":" ^ v)) formats;
  debug_print "MAPPINGS";
  Hashtbl.iter (fun k v ->
    match v with (l, r) ->
      debug_print (k ^ ": " ^ (String.concat "," l) ^ " <-> " ^ (String.concat "," r))) mappings;

  Hashtbl.iter (fun k v ->
    let asms = explode_mnemonics v in
      List.iter (fun asm ->
        Hashtbl.add assembly_clean k (List.filter (fun s -> not (String.equal s "opt_spc(())")) asm)
      ) asms;
  ) assembly;

  debug_print "ASSEMBLY_CLEAN";
  Hashtbl.iter (fun k v -> debug_print (k ^ ":" ^ Util.string_of_list ", " (fun x -> x) v)) assembly_clean;

  print_endline "{";
  print_endline "  \"instructions\": [";

  (* Join keys and mnemonics, then sort by mnemonic, then use the keys in that order to emit instructions *)
  let key_mnemonic_sorted =
    let key_mnemonic_map = Hashtbl.fold (fun k v init -> [k; List.hd v] :: init) assembly_clean [] in
      List.sort (fun l r -> String.compare (List.hd (List.tl l)) (List.hd (List.tl r))) key_mnemonic_map in
        print_endline (String.concat ",\n" (List.map (fun a -> json_of_instruction (List.hd a) (List.tl a)) key_mnemonic_sorted));

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
