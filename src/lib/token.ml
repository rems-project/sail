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
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

type token =
  | And
  | As
  | Assert
  | At
  | Attribute of string
  | BOOL
  | Backwards
  | Bar
  | Bidir
  | Bin of string
  | Bitfield
  | Bitone
  | Bitzero
  | By
  | Caret
  | Cast
  | Catch
  | Clause
  | Colon of string
  | ColonColon
  | Comma
  | Config
  | Configuration
  | Constant
  | Constraint
  | Dec
  | Default
  | Do
  | DocBlock of string
  | DocLine of string
  | Dot
  | DotDot
  | Downto
  | Effect
  | Else
  | End
  | Enum
  | Eof
  | Eq of string
  | EqGt of string
  | Exit
  | False
  | Fixity of Parse_ast.fixity_token
  | Forall
  | Foreach
  | Forwards
  | From
  | Function_
  | Hex of string
  | INT
  | Id of string
  | If_
  | Impl
  | Impure
  | In
  | Inc
  | Instantiation
  | InternalAssume
  | InternalPLet
  | InternalReturn
  | Lcurly
  | LcurlyBar
  | Let_
  | Lparen
  | Lsquare
  | LsquareBar
  | Mapping
  | Match
  | Minus
  | MinusGt
  | Monadic
  | MultilineString of string list
  | Mutual
  | NAT
  | Newtype
  | Num of Nat_big_num.num
  | ORDER
  | Op
  | OpId of string
  | Outcome
  | Overload
  | Pragma of (string * string)
  | Private
  | Pure
  | Rcurly
  | RcurlyBar
  | Real of string
  | Ref
  | Register
  | Repeat
  | Return
  | Rparen
  | Rsquare
  | RsquareBar
  | Scattered
  | Semi
  | Sizeof
  | Star
  | String of string
  | Struct
  | StructuredPragma of string
  | TYPE
  | TerminationMeasure
  | Then
  | Throw
  | To
  | True
  | Try
  | TwoCaret
  | TyVar of string
  | Typedef
  | Undefined
  | Under
  | Union
  | Unit of string
  | Until
  | Val
  | Var
  | When
  | While
  | With

module Highlight = struct
  type t =
    | H_id
    | H_keyword
    | H_kind
    | H_comment
    | H_string
    | H_pragma
    | H_internal
    | H_operator
    | H_literal
    | H_ty_var
    | H_bracket
    | H_punctuation

  let to_class = function
    | H_id -> "sail-id"
    | H_keyword -> "sail-keyword"
    | H_kind -> "sail-kind"
    | H_comment -> "sail-comment"
    | H_string -> "sail-string"
    | H_pragma -> "sail-pragma"
    | H_internal -> "sail-internal"
    | H_operator -> "sail-operator"
    | H_literal -> "sail-literal"
    | H_ty_var -> "sail-ty-var"
    | H_bracket -> "sail-bracket"
    | H_punctuation -> "sail-punctuation"

  let classify = function
    | Eof -> None
    | Id _ -> Some H_id
    | INT | NAT | BOOL | TYPE | ORDER -> Some H_kind
    | String _ | MultilineString _ -> Some H_string
    | DocLine _ | DocBlock _ -> Some H_comment
    | And | As | Assert | By | Match | Clause | Dec | Op | Default | Effect | End | Enum | Else | Exit | Cast | Forall
    | Foreach | Function_ | Mapping | Overload | Throw | Try | Catch | If_ | In | Inc | Var | Ref | Pure | Impure
    | Monadic | Register | Return | Scattered | Sizeof | Constraint | Constant | Struct | Then | Typedef | Union
    | Newtype | With | Val | Outcome | Instantiation | Impl | Private | Repeat | Until | While | Do | Mutual | Config
    | Configuration | TerminationMeasure | Forwards | Backwards | Let_ | Bitfield | When | To | Downto | From ->
        Some H_keyword
    | StructuredPragma _ | Pragma _ | Attribute _ | Fixity _ -> Some H_pragma
    | InternalPLet | InternalReturn | InternalAssume -> Some H_internal
    | OpId _ | Star | ColonColon | Bar | Caret | Minus -> Some H_operator
    | Hex _ | Bin _ | Undefined | True | False | Bitzero | Bitone | Num _ | Real _ -> Some H_literal
    | TyVar _ -> Some H_ty_var
    | Lcurly | Rcurly | LcurlyBar | RcurlyBar | Lsquare | Rsquare | LsquareBar | RsquareBar | Lparen | Rparen ->
        Some H_bracket
    | Under | Colon _ | Dot | DotDot | EqGt _ | At | Unit _ | Bidir | Semi | Comma | Eq _ | TwoCaret | MinusGt ->
        Some H_punctuation
end
