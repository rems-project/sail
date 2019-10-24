open PPrintEngine
open PPrintCombinators
open Msp_ast
open Msp_ast.SyntaxVCT
open Msp_ast.Location
       
       
(*let int_of_nat (Arith.Nat n) = Big_int.int_of_big_int n
let int_of_int (Arith.Int_of_integer n) = Big_int.int_of_big_int n
 *)

let int_of_nat (Arith.Nat n) = Z.to_int n
let int_of_int (Arith.Int_of_integer n) = Z.to_int n


let str_num n = Pervasives.string_of_int (int_of_nat n)
let str_int n = Pervasives.string_of_int (Z.to_int n)

let cis s = Msp_ast.Stringa.implode s

let pp_pos (Pos_ext (f1,l1,b1,c1,_)) = f1 ^ ":" ^ (Pervasives.string_of_int (Z.to_int l1)) ^ ":" ^ (Pervasives.string_of_int (Z.to_int c1-  Z.to_int b1))


let pp_loc x = match x with
| Loc_unknown -> string "unknown"
| Loc_range(pos1,pos2) -> string "(" ^^ string "range" ^^ string " " ^^ string (pp_pos pos1) ^^ string " " ^^ string (pp_pos pos2) ^^ string ")"

let pp_raw_loc x = match x with
| Loc_unknown -> string "Loc_unknown"
| Loc_range(pos1,pos2) -> string "Loc_range" ^^ string "(" ^^  string "\"" ^^ string (pp_pos pos1) ^^ string "\"" ^^ string "," ^^  string "\"" ^^ string (pp_pos pos2) ^^ string "\"" ^^ string ")"

                                                                                                                                                                                                 
let pp_l = pp_loc
let pp_raw_l = pp_raw_loc

(* conversions 
string id -- string (cis id)
sring ctor0 --> string (cis ctor0)
field0

problems with bracketing in product types 

use (function (k0,(b0,c0))

prj
field
string_val
real_val

Numbers
  num


*)
