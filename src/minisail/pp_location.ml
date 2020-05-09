open PPrintEngine
open PPrintCombinators
open Minisailplus_pp
open Msp_ast.Location
       
let pp_pos (Pos_ext (f1,l1,b1,c1,_)) = f1 ^ ":" ^ (Pervasives.string_of_int (Z.to_int l1)) ^ ":" ^ (Pervasives.string_of_int (Z.to_int c1-  Z.to_int b1))

       
let pp_loc x = match x with
| Loc_unknown -> string "unknown"
| Loc_range(pos1,pos2) -> string "(" ^^ string "range" ^^ string " " ^^ string (pp_pos pos1) ^^ string " " ^^ string (pp_pos pos2) ^^ string ")"

