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
(*    Louis-Emile Ploix                                                     *)
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
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

open Libsail

module StringSet = Set.Make (String)

(** We use some words in the compilation process, so treat them as
    Systemverilog reserveds even though they are not. *)
let sv_used_words = ["padding"] |> StringSet.of_list

(** Systemverilog has a lot of keywords, this list is from the
    SystemVerilog LRM 1800-2017, Table B.1. Fortunately, there are no
    keywords begining with the letter z, so our z-encoding scheme
    works to avoid any clashes. *)
let sv_reserved_words =
  [
    "accept_on";
    "alias";
    "always";
    "always_comb";
    "always_ff";
    "always_latch";
    "and";
    "assert";
    "assign";
    "assume";
    "automatic";
    "before";
    "begin";
    "bind";
    "bins";
    "binsof";
    "bit";
    "break";
    "buf";
    "bufif0";
    "bufif1";
    "byte";
    "case";
    "casex";
    "casez";
    "cell";
    "chandle";
    "checker";
    "class";
    "clocking";
    "cmos";
    "config";
    "const";
    "constraint";
    "context";
    "continue";
    "cover";
    "covergroup";
    "coverpoint";
    "cross";
    "deassign";
    "default";
    "defparam";
    "design";
    "disable";
    "dist";
    "do";
    "edge";
    "else";
    "end";
    "endcase";
    "endchecker";
    "endclass";
    "endclocking";
    "endconfig";
    "endfunction";
    "endgenerate";
    "endgroup";
    "endinterface";
    "endmodule";
    "endpackage";
    "endprimitive";
    "endprogram";
    "endproperty";
    "endspecify";
    "endsequence";
    "endtable";
    "endtask";
    "enum";
    "event";
    "eventually";
    "expect";
    "export";
    "extends";
    "extern";
    "final";
    "first_match";
    "for";
    "force";
    "foreach";
    "forever";
    "fork";
    "forkjoin";
    "function";
    "generate";
    "genvar";
    "global";
    "highz0";
    "highz1";
    "if";
    "iff";
    "ifnone";
    "ignore_bins";
    "illegal_bins";
    "implements";
    "implies";
    "import";
    "incdir";
    "include";
    "initial";
    "inout";
    "input";
    "inside";
    "instance";
    "int";
    "integer";
    "interconnect";
    "interface";
    "intersect";
    "join";
    "join_any";
    "join_none";
    "large";
    "let";
    "liblist";
    "library";
    "local";
    "localparam";
    "logic";
    "longint";
    "macromodule";
    "matches";
    "medium";
    "modport";
    "module";
    "nand";
    "negedge";
    "nettype";
    "new";
    "nexttime";
    "nmos";
    "nor";
    "noshowcancelled";
    "not";
    "notif0";
    "notif1";
    "null";
    "or";
    "output";
    "package";
    "packed";
    "parameter";
    "pmos";
    "posedge";
    "primitive";
    "priority";
    "program";
    "property";
    "protected";
    "pull0";
    "pull1";
    "pulldown";
    "pullup";
    "pulsestyle_ondetect";
    "pulsestyle_onevent";
    "pure";
    "rand";
    "randc";
    "randcase";
    "randsequence";
    "rcmos";
    "real";
    "realtime";
    "ref";
    "reg";
    "reject_on";
    "release";
    "repeat";
    "restrict";
    "return";
    "rnmos";
    "rpmos";
    "rtran";
    "rtranif0";
    "rtranif1";
    "s_always";
    "s_eventually";
    "s_nexttime";
    "s_until";
    "s_until_with";
    "scalared";
    "sequence";
    "shortint";
    "shortreal";
    "showcancelled";
    "signed";
    "small";
    "soft";
    "solve";
    "specify";
    "specparam";
    "static";
    "string";
    "strong";
    "strong0";
    "strong1";
    "struct";
    "super";
    "supply0";
    "supply1";
    "sync_accept_on";
    "sync_reject_on";
    "table";
    "tagged";
    "task";
    "this";
    "throughout";
    "time";
    "timeprecision";
    "timeunit";
    "tran";
    "tranif0";
    "tranif1";
    "tri";
    "tri0";
    "tri1";
    "triand";
    "trior";
    "trireg";
    "type";
    "typedef";
    "union";
    "unique";
    "unique0";
    "unsigned";
    "until";
    "until_with";
    "untyped";
    "use";
    "uwire";
    "var";
    "vectored";
    "virtual";
    "void";
    "wait";
    "wait_order";
    "wand";
    "weak";
    "weak0";
    "weak1";
    "while";
    "wildcard";
    "wire";
    "with";
    "within";
    "wor";
    "xnor";
    "xor";
  ]
  |> StringSet.of_list
