(**************************************************************************)
(*  Sail to verilog                                                       *)
(*                                                                        *)
(*  Copyright (c) 2023                                                    *)
(*    Alasdair Armstrong                                                  *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
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

module Big_int = Nat_big_num

module StringSet = Set.Make (String)

open Printf

let required_width n =
  let rec required_width' n =
    if Big_int.equal n Big_int.zero then 1 else 1 + required_width' (Big_int.shift_right n 1)
  in
  required_width' (Big_int.abs n)

let nf s = s
let pf fmt = sprintf fmt

let generated_primops = ref (StringSet.empty, [])

let register_primop name def =
  let names, _ = !generated_primops in
  if StringSet.mem name names then name
  else (
    let source = def () in
    let names, defs = !generated_primops in
    generated_primops := (StringSet.add name names, source :: defs);
    name
  )

let get_generated_primops () = List.rev (snd !generated_primops)

let sail_bits width =
  let index_top = required_width (Big_int.of_int (width - 1)) - 1 in
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

let print_lbits width =
  let zeros = String.make (width / 4) '0' in
  let header =
    [
      nf "function automatic sail_unit sail_print_bits(string prefix, sail_bits bv);";
      nf "    string bstr;";
      nf "    string zeros;";
      pf "    zeros = \"%s\";" zeros;
    ]
  in
  let body =
    List.init (width - 1) (fun n ->
        if (n + 1) mod 4 == 0 then
          [
            pf "    if (bv.size == %d) begin" (n + 1);
            nf "        bstr.hextoa(bv.bits);";
            pf "        $display(\"%%s0x%%s%%s\", prefix, zeros.substr(0, %d - bstr.len()), bstr.toupper());"
              (((n + 1) / 4) - 1);
            nf "    end";
          ]
        else
          [
            pf "    if (bv.size == %d) begin" (n + 1);
            pf "        $display(\"%%s0b%%b\", prefix, bv.bits[%d:0]);" n;
            nf "    end";
          ]
    )
    |> List.concat
  in
  let footer = "endfunction" in
  header @ body @ [footer]

let string_of_bits width =
  let zeros = String.make (width - 1) '0' in
  let header =
    [
      nf "function automatic string sail_string_of_bits(sail_bits bv);";
      nf "    string bstr;";
      nf "    string zeros;";
      pf "    zeros = \"%s\";" zeros;
    ]
  in
  let body =
    List.init (width - 1) (fun n ->
        if (n + 1) mod 4 == 0 then
          [
            pf "    if (bv.size == %d) begin" (n + 1);
            nf "        bstr.hextoa(bv.bits);";
            pf "        return {\"0x\", zeros.substr(0, %d - bstr.len()), bstr.toupper()};" (((n + 1) / 4) - 1);
            nf "    end";
          ]
        else
          [
            pf "    if (bv.size == %d) begin" (n + 1);
            nf "        bstr.bintoa(bv.bits);";
            pf "        return {\"0b\", zeros.substr(0, %d - bstr.len()), bstr};" n;
            nf "    end";
          ]
    )
    |> List.concat
  in
  let footer = "endfunction" in
  header @ body @ [footer]

let print_lbits_stub width =
  [
    nf "function automatic sail_unit sail_print_bits(sail_unit prefix, sail_bits bv);";
    nf "    return SAIL_UNIT;";
    nf "endfunction";
  ]

let string_of_bits_stub width =
  [nf "function automatic sail_unit sail_string_of_bits(sail_bits bv);"; nf "    return SAIL_UNIT;"; nf "endfunction"]

let dec_str width =
  [
    pf "function automatic string sail_dec_str(logic [%d:0] i);" (width - 1);
    nf "    string s;";
    nf "    s.itoa(i);";
    nf "    return s;";
    nf "endfunction";
  ]

let dec_str_stub width =
  [
    pf "function automatic sail_unit sail_dec_str(logic [%d:0] i);" (width - 1);
    nf "    return SAIL_UNIT;";
    nf "endfunction";
  ]

let hex_str width =
  [
    pf "function automatic string sail_hex_str(logic [%d:0] i);" (width - 1);
    nf "    string s;";
    nf "    s.hextoa(i);";
    nf "    return {\"0x\", s};";
    nf "endfunction";
  ]

let hex_str_stub width =
  [
    pf "function automatic sail_unit sail_hex_str(logic [%d:0] i);" (width - 1);
    nf "    return SAIL_UNIT;";
    nf "endfunction";
  ]

let hex_str_upper width =
  [
    pf "function automatic string sail_hex_str_upper(logic [%d:0] i);" (width - 1);
    nf "    string s;";
    nf "    s.hextoa(i);";
    nf "    return {\"0x\", s.toupper()};";
    nf "endfunction";
  ]

let hex_str_upper_stub width =
  [
    pf "function automatic sail_unit sail_hex_str_upper(logic [%d:0] i);" (width - 1);
    nf "    return SAIL_UNIT;";
    nf "endfunction";
  ]

let print_int width =
  [
    pf "function automatic sail_unit sail_print_int(string prefix, logic [%d:0] i);" (width - 1);
    nf "    $display(\"%s%0d\", prefix, signed'(i));";
    nf "endfunction";
  ]

let print_int_stub width =
  [
    pf "function automatic sail_unit sail_print_int(sail_unit prefix, logic [%d:0] i);" (width - 1);
    nf "    return SAIL_UNIT;";
    nf "endfunction";
  ]

let get_cycle_count width =
  [
    pf "function automatic logic [%d:0] sail_get_cycle_count(sail_unit u);" (width - 1);
    nf "    return sail_cycle_count_var;";
    nf "endfunction";
  ]

let cycle_count () =
  [
    "function automatic sail_unit sail_cycle_count(sail_unit u);";
    "    sail_cycle_count_var = sail_cycle_count_var + 1;";
    "    return SAIL_UNIT;";
    "endfunction";
  ]

let output_primop buf lines =
  List.iter
    (fun line ->
      Buffer.add_string buf line;
      Buffer.add_char buf '\n'
    )
    lines;
  Buffer.add_char buf '\n'

let common_primops bv_width int_width =
  let buf = Buffer.create 4096 in
  output_primop buf (sail_bits bv_width);
  output_primop buf (sail_int int_width);
  output_primop buf (print_lbits bv_width);
  output_primop buf (string_of_bits bv_width);
  output_primop buf (print_int int_width);
  output_primop buf (dec_str int_width);
  output_primop buf (hex_str int_width);
  output_primop buf (hex_str_upper int_width);
  Buffer.add_string buf (pf "logic [%d:0] sail_cycle_count_var;\n\n" (int_width - 1));
  output_primop buf (get_cycle_count int_width);
  output_primop buf (cycle_count ());
  Buffer.contents buf

let common_primops_stubs bv_width int_width =
  let buf = Buffer.create 4096 in
  output_primop buf (sail_bits bv_width);
  output_primop buf (sail_int int_width);
  output_primop buf (print_lbits_stub bv_width);
  output_primop buf (string_of_bits_stub bv_width);
  output_primop buf (print_int_stub int_width);
  output_primop buf (dec_str_stub int_width);
  output_primop buf (hex_str_stub int_width);
  output_primop buf (hex_str_upper_stub int_width);
  Buffer.add_string buf (pf "logic [%d:0] sail_cycle_count_var;\n\n" (int_width - 1));
  output_primop buf (get_cycle_count int_width);
  output_primop buf (cycle_count ());
  Buffer.contents buf

let print_fbits width =
  let name = pf "sail_print_fixed_bits_%d" width in
  register_primop name (fun () ->
      let display =
        if width mod 4 = 0 then (
          let zeros = String.make (width / 4) '0' in
          [
            nf "    string bstr;";
            nf "    string zeros;";
            nf "    bstr.hextoa(b);";
            pf "    zeros = \"%s\";" zeros;
            pf "    $display(\"%%s0x%%s\", s, zeros.substr(0, %d - bstr.len()), bstr.toupper());" ((width / 4) - 1);
          ]
        )
        else ["    $display(\"%s0b%b\", s, b);"]
      in
      [pf "function automatic sail_unit %s(string s, logic [%d:0] b);" name (width - 1)]
      @ display
      @ ["    return SAIL_UNIT;"; "endfunction"]
  )

let string_of_fbits width =
  let name = pf "sail_string_of_bits_%d" width in
  register_primop name (fun () ->
      let header = ["    string bstr;"; "    string zeros;"] in
      let display =
        if width mod 4 = 0 then (
          let zeros = String.make (width / 4) '0' in
          [
            nf "    bstr.hextoa(b);";
            pf "    zeros = \"%s\";" zeros;
            pf "    return {\"0x\", zeros.substr(0, %d - bstr.len()), bstr.toupper()};" ((width / 4) - 1);
          ]
        )
        else (
          let zeros = String.make (width - 1) '0' in
          [
            nf "    bstr.bintoa(b);";
            pf "    zeros = \"%s\";" zeros;
            pf "    return {\"0b\", zeros.substr(0, %d - bstr.len()), bstr};" (width - 1);
          ]
        )
      in
      [pf "function automatic string %s(logic [%d:0] b);" name (width - 1)] @ header @ display @ ["endfunction"]
  )

let print_fbits_stub width =
  let name = pf "sail_print_fixed_bits_%d" width in
  register_primop name (fun () ->
      [
        pf "function automatic sail_unit %s(sail_unit prefix, logic [%d:0] bv);" name (width - 1);
        nf "    return SAIL_UNIT;";
        nf "endfunction";
      ]
  )

let string_of_fbits_stub width =
  let name = pf "sail_string_of_bits_%d" width in
  register_primop name (fun () ->
      [
        pf "function automatic sail_unit %s(logic [%d:0] bv);" name (width - 1);
        nf "    return SAIL_UNIT;";
        nf "endfunction";
      ]
  )

let dec_str_fint width =
  let name = pf "sail_dec_str_%d" width in
  register_primop name (fun () ->
      [
        pf "function automatic string %s(logic [%d:0] i);" name (width - 1);
        nf "    string s;";
        nf "    s.itoa(i);";
        nf "    return s;";
        nf "endfunction";
      ]
  )

let dec_str_fint_stub width =
  let name = pf "sail_dec_str_%d" width in
  register_primop name (fun () ->
      [
        pf "function automatic sail_unit %s(logic [%d:0] i);" name (width - 1);
        nf "    return SAIL_UNIT;";
        nf "endfunction";
      ]
  )

let hex_str_fint width =
  let name = pf "sail_hex_str_%d" width in
  register_primop name (fun () ->
      [
        pf "function automatic string %s(logic [%d:0] i);" name (width - 1);
        nf "    string s;";
        nf "    s.hextoa(i);";
        nf "    return {\"0x\", s};";
        nf "endfunction";
      ]
  )

let hex_str_fint_stub width =
  let name = pf "sail_hex_str_%d" width in
  register_primop name (fun () ->
      [
        pf "function automatic sail_unit %s(logic [%d:0] i);" name (width - 1);
        nf "    return SAIL_UNIT;";
        nf "endfunction";
      ]
  )

let hex_str_upper_fint width =
  let name = pf "sail_hex_str_upper_%d" width in
  register_primop name (fun () ->
      [
        pf "function automatic string %s(logic [%d:0] i);" name (width - 1);
        nf "    string s;";
        nf "    s.hextoa(i);";
        nf "    return {\"0x\", s.toupper()};";
        nf "endfunction";
      ]
  )

let hex_str_upper_fint_stub width =
  let name = pf "sail_hex_str_upper_%d" width in
  register_primop name (fun () ->
      [
        pf "function automatic sail_unit %s(logic [%d:0] i);" name (width - 1);
        nf "    return SAIL_UNIT;";
        nf "endfunction";
      ]
  )

let rec count_leading_zeros width =
  let name = pf "sail_clz_%d" width in
  register_primop name (fun () ->
      if width == 1 then
        [
          pf "function automatic logic [%d:0] %s(logic [%d:0] bv);" (width - 1) name (width - 1);
          nf "    return ~bv[0];";
          nf "endfunction";
        ]
      else (
        let lower_width = width / 2 in
        let upper_width = lower_width + (width mod 2) in
        let upper = pf "bv[%d:%d]" (width - 1) (width - upper_width) in
        let lower = pf "bv[%d:0]" (lower_width - 1) in
        let clz_upper = count_leading_zeros upper_width in
        let clz_lower = count_leading_zeros lower_width in
        [
          pf "function automatic logic [%d:0] %s(logic [%d:0] bv);" (width - 1) name (width - 1);
          pf "    if (%s == 0) begin" upper;
          pf "        return %d'd%d + %d'(%s(%s));" width upper_width width clz_lower lower;
          nf "    end else begin";
          pf "        return %d'(%s(%s));" width clz_upper upper;
          nf "    end;";
          nf "endfunction";
        ]
      )
  )

let popcount width =
  (* Cound maybe use $countones? *)
  let name = pf "sail_popcount_%d" width in
  register_primop name (fun () ->
      let bits = List.init (width - 1) (fun n -> pf "%d'(bv[%d])" width (n + 1)) in
      let sum = List.fold_left (fun sum bit -> pf "%s + %s" sum bit) (pf "%d'(bv[0])" width) bits in
      [
        pf "function automatic logic [%d:0] %s(logic [%d:0] bv);" (width - 1) name (width - 1);
        pf "    return %s;" sum;
        nf "endfunction";
      ]
  )

let wrap_type (ty, ix_opt) str = match ix_opt with None -> ty ^ " " ^ str | Some ix -> ty ^ " " ^ str ^ " " ^ ix

let array_type (ty, ix_opt) ix = match ix_opt with None -> (ty, Some ix) | Some inner_ix -> (ty, Some (inner_ix ^ ix))

let fvector_store len elem_ty key =
  let name = pf "sail_array_store_%d_%s" len key in
  register_primop name (fun () ->
      let ret_ty_name = pf "ret_array_store_%d_%s" len key in
      let outer_ix = pf "[%d:0]" (len - 1) in
      let ix_ty = pf "logic [%d:0]" (required_width (Big_int.of_int (len - 1)) - 2) in
      [
        pf "typedef %s%s;" (wrap_type elem_ty ret_ty_name) outer_ix;
        "";
        pf "function automatic %s %s(%s, %s i, %s);" ret_ty_name name
          (wrap_type (array_type elem_ty outer_ix) "arr")
          ix_ty (wrap_type elem_ty "x");
        pf "    %s r;" ret_ty_name;
        nf "    r = arr;";
        nf "    r[i] = x;";
        nf "    return r;";
        nf "endfunction";
      ]
  )

let is_empty elem_ty key =
  let name = pf "sail_is_empty_%s" key in
  register_primop name (fun () ->
      [
        pf "function automatic bit %s(%s[$]);" name (wrap_type elem_ty "xs");
        nf "    return xs.size() == 0;";
        nf "endfunction";
      ]
  )

let hd elem_ty key =
  let name = pf "sail_hd_%s" key in
  register_primop name (fun () ->
      let ret_ty_name = pf "ret_hd_%s" key in
      [
        pf "typedef %s;" (wrap_type elem_ty ret_ty_name);
        "";
        pf "function automatic %s %s(%s[$]);" ret_ty_name name (wrap_type elem_ty "xs");
        pf "    %s;" (wrap_type elem_ty "r");
        nf "    r = xs[0];";
        nf "    return r;";
        nf "endfunction";
      ]
  )

let tl elem_ty key =
  let name = pf "sail_tl_%s" key in
  register_primop name (fun () ->
      let ret_ty_name = pf "ret_tl_%s" key in
      [
        pf "typedef %s[$];" (wrap_type elem_ty ret_ty_name);
        "";
        pf "function automatic %s %s(%s[$]);" ret_ty_name name (wrap_type elem_ty "xs");
        pf "    %s r;" ret_ty_name;
        nf "    r = xs;";
        nf "    r.pop_front();";
        nf "    return r;";
        nf "endfunction";
      ]
  )
