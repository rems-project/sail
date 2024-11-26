(**************************************************************************)
(*  Sail to SystemVerilog                                                 *)
(*                                                                        *)
(*  Copyright (c) 2023                                                    *)
(*    Alasdair Armstrong                                                  *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  SPDX-License-Identifier: BSD-2-Clause                                 *)
(**************************************************************************)

open Libsail

open Ast_util
open Jib
open Jib_util
open Printf
open Sv_ir

module StringSet = Set.Make (String)

let required_width n =
  let rec required_width' n =
    if Big_int.equal n Big_int.zero then 1 else 1 + required_width' (Big_int.shift_right n 1)
  in
  required_width' (Big_int.abs n)

let nf s = s
let pf fmt = sprintf fmt

let sail_bits width =
  let index_top = required_width (Big_int.of_int (width - 1)) in
  [
    nf "typedef struct packed {";
    pf "    logic [%d:0] size;" index_top;
    pf "    logic [%d:0] bits;" (width - 1);
    nf "} sail_bits;";
    "";
    pf "localparam SAIL_BITS_WIDTH = %d;" width;
    pf "localparam SAIL_INDEX_WIDTH = %d;" (index_top + 1);
    "";
    pf "function automatic logic [%d:0] sail_bits_size(sail_bits bv); return bv.size; endfunction" index_top;
    pf "function automatic logic [%d:0] sail_bits_value(sail_bits bv); return bv.bits; endfunction" (width - 1);
  ]

let sail_int width = [pf "typedef logic [%d:0] sail_int;" (width - 1)]

let output_primop buf lines =
  List.iter
    (fun line ->
      Buffer.add_string buf line;
      Buffer.add_char buf '\n'
    )
    lines;
  Buffer.add_char buf '\n'

module type S = sig
  val generate_module : at:Parse_ast.l -> string -> (cval list -> ctyp -> string) option

  val get_generated_library_defs : unit -> sv_def list

  val string_of_fbits : int -> string

  val hex_str : ctyp -> string

  val hex_str_upper : ctyp -> string

  val dec_str : ctyp -> string

  val is_empty : ctyp -> string

  val hd : ctyp -> string

  val tl : ctyp -> string

  val fvector_store : int -> ctyp -> string

  val eq_list : (cval -> cval -> Smt_exp.smt_exp Smt_gen.check_writer) -> ctyp -> ctyp -> string Smt_gen.check_writer
end

module Make
    (Config : sig
      val max_unknown_bitvector_width : int
      val max_unknown_integer_width : int
    end)
    () : S = struct
  let generated_library_defs = ref (StringSet.empty, [])

  let register_library_def name def =
    let names, _ = !generated_library_defs in
    if StringSet.mem name names then name
    else (
      let source = mk_def (def ()) in
      let names, defs = !generated_library_defs in
      generated_library_defs := (StringSet.add name names, source :: defs);
      name
    )

  let register_monadic_library_def name def =
    let open Smt_gen in
    mk_check_writer (fun l ->
        run
          (let names, _ = !generated_library_defs in
           if StringSet.mem name names then return name
           else
             let* source = fmap mk_def (def ()) in
             let names, defs = !generated_library_defs in
             generated_library_defs := (StringSet.add name names, source :: defs);
             return name
          )
          l
    )

  let get_generated_library_defs () = List.rev (snd !generated_library_defs)

  let primop_name s = Jib_util.name (mk_id s)

  let fvector_store len elem_ctyp =
    let name = sprintf "sail_array_store_%d_%s" len (Util.zencode_string (string_of_ctyp elem_ctyp)) in
    register_library_def name (fun () ->
        let arr_ctyp = CT_fvector (len, elem_ctyp) in
        let ix_width = required_width (Big_int.of_int (len - 1)) - 1 in
        let r = primop_name "r" in
        let arr = primop_name "arr" in
        let i = primop_name "i" in
        let x = primop_name "x" in
        SVD_fundef
          {
            function_name = SVN_string name;
            return_type = Some (CT_fvector (len, elem_ctyp));
            params = [(mk_id "arr", arr_ctyp); (mk_id "i", CT_fbits ix_width); (mk_id "x", elem_ctyp)];
            body =
              mk_statement
                (SVS_block
                   ([
                      SVS_var (r, arr_ctyp, Some (Var arr));
                      SVS_assign (SVP_index (SVP_id r, Var i), Var x);
                      SVS_return (Var r);
                    ]
                   |> List.map mk_statement
                   )
                );
          }
    )

  let print_fbits width =
    let name = sprintf "sail_print_fixed_bits_%d" width in
    register_library_def name (fun () ->
        let b = primop_name "b" in
        let s = primop_name "s" in
        let in_str = primop_name "in_str" in
        let out_str = primop_name "out_str" in
        let always_comb =
          (* If the width is a multiple of four, format as hexadecimal.
             We take care to ensure the formatting is identical to other
             Sail backends. *)
          let zeros = Jib_util.name (mk_id "zeros") in
          let bstr = Jib_util.name (mk_id "bstr") in
          if width mod 4 = 0 then (
            let zeros_init = String.make (width / 4) '0' in
            [
              SVS_var (zeros, CT_string, None);
              SVS_var (bstr, CT_string, None);
              svs_raw "bstr.hextoa(b)" ~inputs:[b] ~outputs:[bstr];
              svs_raw (sprintf "zeros = \"%s\"" zeros_init) ~outputs:[zeros];
              svs_raw
                (sprintf
                   "out_str = {in_str, s, $sformatf(\"0x%%s\", zeros.substr(0, %d - bstr.len()), bstr.toupper()), \
                    \"\\n\"}"
                   ((width / 4) - 1)
                )
                ~inputs:[in_str; s; zeros; bstr] ~outputs:[out_str];
              SVS_assign (SVP_id Jib_util.return, Unit);
            ]
            |> List.map mk_statement
          )
          else (
            let zeros_init = String.make width '0' in
            [
              SVS_var (zeros, CT_string, None);
              SVS_var (bstr, CT_string, None);
              svs_raw "bstr.bintoa(b)" ~inputs:[b] ~outputs:[bstr];
              svs_raw (sprintf "zeros = \"%s\"" zeros_init) ~outputs:[zeros];
              svs_raw
                (sprintf "out_str = {in_str, s, $sformatf(\"0b%%s\", zeros.substr(0, %d - bstr.len())), bstr, \"\\n\"}"
                   (width - 1)
                )
                ~inputs:[in_str; s; bstr; zeros] ~outputs:[out_str];
              SVS_assign (SVP_id Jib_util.return, Unit);
            ]
            |> List.map mk_statement
          )
        in
        SVD_module
          {
            name = SVN_string name;
            recursive = false;
            input_ports = [mk_port s CT_string; mk_port b (CT_fbits width); mk_port in_str CT_string];
            output_ports = [mk_port Jib_util.return CT_unit; mk_port out_str CT_string];
            defs = [mk_def (SVD_always_comb (mk_statement (SVS_block always_comb)))];
          }
    )

  let print_lbits () =
    let width = Config.max_unknown_bitvector_width in
    register_library_def "sail_print_bits" (fun () ->
        let b = primop_name "b" in
        let s = primop_name "s" in
        let in_str = primop_name "in_str" in
        let out_str = primop_name "out_str" in
        let zeros = primop_name "zeros" in
        let binstr = primop_name "binstr" in
        let hexstr = primop_name "hexstr" in
        let tempstr n = primop_name ("tempstr" ^ string_of_int n) in
        let defs =
          List.init width (fun n -> SVD_var (tempstr n, CT_string))
          @ [
              SVD_var (zeros, CT_string);
              SVD_var (hexstr, CT_string);
              SVD_var (binstr, CT_string);
              SVD_always_comb
                (mk_statement
                   (SVS_block
                      (List.map mk_statement
                         [
                           svs_raw (sprintf "zeros = \"%s\"" (String.make width '0')) ~outputs:[zeros];
                           svs_raw (sprintf "hexstr.hextoa(b.bits)") ~inputs:[b] ~outputs:[hexstr];
                           svs_raw (sprintf "binstr.bintoa(b.bits)") ~inputs:[b] ~outputs:[binstr];
                           svs_raw
                             (sprintf "%s = {in_str, s}" (string_of_name ~zencode:false (tempstr 0)))
                             ~inputs:[in_str; s]
                             ~outputs:[tempstr 0];
                         ]
                      )
                   )
                );
            ]
          @ (List.init (width - 1) (fun n ->
                 if (n + 1) mod 4 == 0 then
                   svs_raw
                     (sprintf
                        "if (b.size == %d) %s = {%s, $sformatf(\"0x%%s\", zeros.substr(0, %d - hexstr.len()), \
                         hexstr.toupper()), \"\\n\"}; else %s = %s"
                        (n + 1)
                        (string_of_name ~zencode:false (tempstr (n + 1)))
                        (string_of_name ~zencode:false (tempstr n))
                        (((n + 1) / 4) - 1)
                        (string_of_name ~zencode:false (tempstr (n + 1)))
                        (string_of_name ~zencode:false (tempstr n))
                     )
                     ~inputs:[b; zeros; hexstr; tempstr n]
                     ~outputs:[tempstr (n + 1)]
                 else
                   svs_raw
                     (sprintf
                        "if (b.size == %d) %s = {%s, $sformatf(\"0b%%s\", zeros.substr(0, %d - binstr.len()), binstr), \
                         \"\\n\"}; else %s = %s"
                        (n + 1)
                        (string_of_name ~zencode:false (tempstr (n + 1)))
                        (string_of_name ~zencode:false (tempstr n))
                        n
                        (string_of_name ~zencode:false (tempstr (n + 1)))
                        (string_of_name ~zencode:false (tempstr n))
                     )
                     ~inputs:[b; zeros; binstr; tempstr n]
                     ~outputs:[tempstr (n + 1)]
             )
            |> List.map (fun s -> SVD_always_comb (mk_statement s))
            )
          @ [
              SVD_always_comb
                (mk_statement
                   (svs_raw
                      (sprintf "out_str = %s" (string_of_name ~zencode:false (tempstr (width - 1))))
                      ~inputs:[tempstr (width - 1)]
                      ~outputs:[out_str]
                   )
                );
            ]
        in
        SVD_module
          {
            name = SVN_string "sail_print_bits";
            recursive = false;
            input_ports = [mk_port s CT_string; mk_port b CT_lbits; mk_port in_str CT_string];
            output_ports = [mk_port Jib_util.return CT_unit; mk_port out_str CT_string];
            defs = List.map mk_def defs;
          }
    )

  let string_of_fbits width =
    let function_name = pf "sail_string_of_bits_%d" width in
    register_library_def function_name (fun () ->
        let b = primop_name "b" in
        let bstr = primop_name "bstr" in
        let zeros = primop_name "zeros" in
        let vars = [SVS_var (bstr, CT_string, None); SVS_var (zeros, CT_string, None)] in
        let body =
          if width mod 4 = 0 then
            [
              svs_raw "bstr.hextoa(b)" ~inputs:[b] ~outputs:[bstr];
              svs_raw (pf "zeros = \"%s\"" (String.make (width / 4) '0')) ~outputs:[zeros];
              svs_raw
                (pf "return {\"0x\", zeros.substr(0, %d - bstr.len()), bstr.toupper()}" ((width / 4) - 1))
                ~inputs:[zeros; bstr];
            ]
          else
            [
              svs_raw "bstr.bintoa(b)" ~inputs:[b] ~outputs:[bstr];
              svs_raw (pf "zeros = \"%s\"" (String.make width '0')) ~outputs:[zeros];
              svs_raw (pf "return {\"0b\", zeros.substr(0, %d - bstr.len()), bstr}" (width - 1)) ~inputs:[zeros; bstr];
            ]
        in
        SVD_fundef
          {
            function_name = SVN_string function_name;
            return_type = Some CT_string;
            params = [(mk_id "b", CT_fbits width)];
            body = mk_statement (SVS_block (List.map mk_statement (vars @ body)));
          }
    )

  let print_int () =
    let name = "sail_print_int" in
    register_library_def name (fun () ->
        let i = primop_name "i" in
        let s = primop_name "s" in
        let in_str = primop_name "in_str" in
        let out_str = primop_name "out_str" in
        let always_comb =
          svs_raw "out_str = {in_str, s, $sformatf(\"%0d\", signed'(i)), \"\\n\"}" ~inputs:[in_str; s; i]
            ~outputs:[out_str]
        in
        SVD_module
          {
            name = SVN_string name;
            recursive = false;
            input_ports = [mk_port s CT_string; mk_port i CT_lint; mk_port in_str CT_string];
            output_ports = [mk_port Jib_util.return CT_unit; mk_port out_str CT_string];
            defs = [mk_def (SVD_always_comb (mk_statement always_comb))];
          }
    )

  let hex_str ctyp =
    let name = sprintf "sail_hex_str_%s" (Util.zencode_string (string_of_ctyp ctyp)) in
    register_library_def name (fun () ->
        let i = primop_name "i" in
        let s = primop_name "s" in
        let n = primop_name "is_negative" in
        let p = primop_name "prefix" in
        SVD_fundef
          {
            function_name = SVN_string name;
            return_type = Some CT_string;
            params = [(mk_id "i", ctyp)];
            body =
              mk_statement
                (SVS_block
                   (List.map mk_statement
                      [
                        SVS_var (s, CT_string, None);
                        SVS_var (n, CT_bool, None);
                        SVS_var (p, CT_string, None);
                        svs_raw "is_negative = signed'(i) < 0" ~inputs:[i] ~outputs:[n];
                        svs_raw "s.hextoa(is_negative ? (-i) : i)" ~inputs:[i; n] ~outputs:[s];
                        svs_raw "prefix = is_negative ? \"-0x\" : \"0x\"" ~inputs:[n] ~outputs:[p];
                        SVS_return (Fn ("str.++", [Var p; Var s]));
                      ]
                   )
                );
          }
    )

  let hex_str_upper ctyp =
    let name = sprintf "sail_hex_str_upper_%s" (Util.zencode_string (string_of_ctyp ctyp)) in
    register_library_def name (fun () ->
        let i = primop_name "i" in
        let s = primop_name "s" in
        let n = primop_name "is_negative" in
        let p = primop_name "prefix" in
        SVD_fundef
          {
            function_name = SVN_string name;
            return_type = Some CT_string;
            params = [(mk_id "i", ctyp)];
            body =
              mk_statement
                (SVS_block
                   (List.map mk_statement
                      [
                        SVS_var (s, CT_string, None);
                        SVS_var (n, CT_bool, None);
                        SVS_var (p, CT_string, None);
                        svs_raw "is_negative = signed'(i) < 0" ~inputs:[i] ~outputs:[n];
                        svs_raw "s.hextoa(is_negative ? (-i) : i)" ~inputs:[i; n] ~outputs:[s];
                        svs_raw "s = s.toupper()" ~inputs:[s] ~outputs:[s];
                        svs_raw "prefix = is_negative ? \"-0x\" : \"0x\"" ~inputs:[n] ~outputs:[p];
                        SVS_return (Fn ("str.++", [Var p; Var s]));
                      ]
                   )
                );
          }
    )

  let dec_str ctyp =
    let name = sprintf "sail_dec_str_%s" (Util.zencode_string (string_of_ctyp ctyp)) in
    register_library_def name (fun () ->
        let i = primop_name "i" in
        let s = primop_name "s" in
        SVD_fundef
          {
            function_name = SVN_string name;
            return_type = Some CT_string;
            params = [(mk_id "i", ctyp)];
            body =
              mk_statement
                (SVS_block
                   (List.map mk_statement
                      [SVS_var (s, CT_string, None); svs_raw "s.itoa(i)" ~inputs:[i] ~outputs:[s]; SVS_return (Var s)]
                   )
                );
          }
    )

  let is_empty ctyp =
    let name = sprintf "sail_is_empty_%s" (Util.zencode_string (string_of_ctyp ctyp)) in
    register_library_def name (fun () ->
        let t = primop_name "t" in
        let xs = primop_name "xs" in
        SVD_fundef
          {
            function_name = SVN_string name;
            return_type = Some CT_bool;
            params = [(mk_id "xs", CT_list ctyp)];
            body =
              mk_statement
                (SVS_block
                   (List.map mk_statement
                      [
                        SVS_var (t, CT_bool, None);
                        svs_raw "t = (xs.size() == 0)" ~inputs:[xs] ~outputs:[t];
                        SVS_return (Var t);
                      ]
                   )
                );
          }
    )

  let hd ctyp =
    let name = sprintf "sail_hd_%s" (Util.zencode_string (string_of_ctyp ctyp)) in
    register_library_def name (fun () ->
        let x = primop_name "x" in
        let xs = primop_name "xs" in
        SVD_fundef
          {
            function_name = SVN_string name;
            return_type = Some ctyp;
            params = [(mk_id "xs", CT_list ctyp)];
            body =
              mk_statement
                (SVS_block
                   (List.map mk_statement
                      [SVS_var (x, ctyp, None); svs_raw "x = xs[0]" ~inputs:[xs] ~outputs:[x]; SVS_return (Var x)]
                   )
                );
          }
    )

  let tl ctyp =
    let name = sprintf "sail_tl_%s" (Util.zencode_string (string_of_ctyp ctyp)) in
    register_library_def name (fun () ->
        let xs = primop_name "xs" in
        let ys = primop_name "ys" in
        SVD_fundef
          {
            function_name = SVN_string name;
            return_type = Some (CT_list ctyp);
            params = [(mk_id "xs", CT_list ctyp)];
            body =
              mk_statement
                (SVS_block
                   (List.map mk_statement
                      [
                        SVS_var (ys, CT_list ctyp, None);
                        svs_raw "xs = (xs.size() > 1) ? xs[1:$] : ys" ~inputs:[xs; ys] ~outputs:[xs];
                        SVS_return (Var xs);
                      ]
                   )
                );
          }
    )

  let eq_list eq_elem ctyp1 ctyp2 =
    let open Smt_gen in
    let t1 = Util.zencode_string (string_of_ctyp ctyp1) in
    let t2 = Util.zencode_string (string_of_ctyp ctyp2) in
    let name = sprintf "sail_eq_list_%s_and_%s" t1 t2 in
    register_monadic_library_def name (fun () ->
        let i = primop_name "i" in
        let len = primop_name "len" in
        let r = primop_name "r" in
        let x = primop_name "x" in
        let xs = primop_name "xs" in
        let y = primop_name "y" in
        let ys = primop_name "ys" in
        let* body_cmp = eq_elem (V_id (x, ctyp1)) (V_id (y, ctyp2)) in
        let loop =
          SVS_for
            ( {
                for_var = (i, CT_fint 32, Smt_exp.bvzero 32);
                for_cond = Fn ("bvslt", [Var i; Var len]);
                for_modifier = SVF_increment i;
              },
              mk_statement
                (SVS_block
                   (List.map mk_statement
                      [
                        SVS_var (x, ctyp1, None);
                        SVS_var (y, ctyp2, None);
                        svs_raw "x = xs[i]" ~inputs:[xs; i] ~outputs:[x];
                        svs_raw "y = ys[i]" ~inputs:[ys; i] ~outputs:[y];
                        SVS_assign (SVP_id r, Fn ("and", [Var r; body_cmp]));
                      ]
                   )
                )
            )
        in
        return
          (SVD_fundef
             {
               function_name = SVN_string name;
               return_type = Some CT_bool;
               params = [(mk_id "xs", CT_list ctyp1); (mk_id "ys", CT_list ctyp2)];
               body =
                 mk_statement
                   (SVS_block
                      (List.map mk_statement
                         [
                           SVS_var (r, CT_bool, Some (Bool_lit true));
                           SVS_var (len, CT_fint 32, None);
                           svs_raw "len = xs.size()" ~inputs:[xs] ~outputs:[len];
                           svs_raw "if (ys.size() != len) return 0" ~inputs:[ys; len];
                           loop;
                           SVS_return (Var r);
                         ]
                      )
                   );
             }
          )
    )

  let unary_module l gen =
    Some
      (fun args ret_ctyp ->
        match (args, ret_ctyp) with
        | [v], ret_ctyp -> gen v ret_ctyp
        | _ -> Reporting.unreachable l __POS__ "Incorrect arity given to unary module generator"
      )

  let binary_module l gen =
    Some
      (fun args ret_ctyp ->
        match (args, ret_ctyp) with
        | [v1; v2], ret_ctyp -> gen v1 v2 ret_ctyp
        | _ -> Reporting.unreachable l __POS__ "Incorrect arity given to binary module generator"
      )

  let ternary_module l gen =
    Some
      (fun args ret_ctyp ->
        match (args, ret_ctyp) with
        | [v1; v2; v3], ret_ctyp -> gen v1 v2 v3 ret_ctyp
        | _ -> Reporting.unreachable l __POS__ "Incorrect arity given to binary module generator"
      )

  let generate_module ~at:l = function
    | "print_bits" ->
        ternary_module l (fun _ v2 _ _ ->
            match cval_ctyp v2 with
            | CT_fbits width -> print_fbits width
            | CT_lbits -> print_lbits ()
            | _ -> Reporting.unreachable l __POS__ "Invalid types given to print_bits generator"
        )
    | "print_int" ->
        ternary_module l (fun _ v2 _ _ ->
            match cval_ctyp v2 with
            | CT_lint -> print_int ()
            | ctyp ->
                Reporting.unreachable l __POS__ ("Invalid types given to print_int generator: " ^ string_of_ctyp ctyp)
        )
    | _ -> None
end

let basic_defs bv_width int_width =
  let buf = Buffer.create 4096 in
  output_primop buf (sail_bits bv_width);
  output_primop buf (sail_int int_width);
  Buffer.contents buf
