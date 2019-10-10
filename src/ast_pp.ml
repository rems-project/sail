open Parse_ast
       
let rec pp_l fmt l =  match l with
  | Unknown -> Format.pp_print_text fmt "?"
  | Unique (_,l) -> pp_l fmt l
  | Generated l -> pp_l fmt l
  | Documented (_,l) -> pp_l fmt l
  | Range (p1,p2) -> Format.fprintf fmt "%s %d:%d - %d:%d"
       p1.pos_fname p1.pos_lnum (p1.pos_cnum - p1.pos_bol) p2.pos_lnum (p2.pos_cnum - p2.pos_bol)

let pp_value _ _ = ()                          
                          
