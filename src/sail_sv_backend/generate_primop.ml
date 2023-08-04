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
  let names, defs = !generated_primops in
  if StringSet.mem name names then name
  else (
    generated_primops := (StringSet.add name names, def () :: defs);
    name
  )

let get_generated_primops () = List.rev (snd !generated_primops)

let sail_bits width =
  [
    nf "typedef struct packed {";
    pf "    logic [%d:0] size;" (required_width (Big_int.of_int (width - 1)) - 1);
    pf "    logic [%d:0] bits;" (width - 1);
    nf "} sail_bits;";
  ]

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

let print_int width =
  [
    pf "function automatic sail_unit sail_print_int(string prefix, logic [%d:0] i);" (width - 1);
    nf "    $display(\"%s%0d\", prefix, signed'(i));";
    nf "endfunction";
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
  output_primop buf (print_lbits bv_width);
  output_primop buf (print_int int_width);
  Buffer.contents buf

let print_fbits width =
  let name = pf "sail_print_fixed_bits_%d" width in
  register_primop name (fun () ->
      let display =
        if width mod 4 = 0 then (
          let zeros = String.make (width / 4) '0' in
          [
            "    string bstr;";
            "    string zeros;";
            "    bstr.hextoa(b);";
            pf "    zeros = \"%s\";" zeros;
            pf "    $display(\"%%s0x%%s\", s, zeros.substr(0, %d - bstr.len()), bstr.toupper());" ((width / 4) - 1);
          ]
        )
        else ["    $display(\"%s0b%0b\", s, b);"]
      in
      [pf "function automatic sail_unit %s(string s, logic [%d:0] b);" name (width - 1)]
      @ display
      @ ["    return SAIL_UNIT;"; "endfunction"]
  )
