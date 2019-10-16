open PPrintEngine
open PPrintCombinators
open Minisailplus_pp
open Minisailplus_ast.Location
open Smt2
       
let pp_pos (Pos_ext (f1,l1,b1,c1,_)) = f1 ^ ":" ^ (Pervasives.string_of_int (Z.to_int l1)) ^ ":" ^ (Pervasives.string_of_int (Z.to_int c1-  Z.to_int b1))

       
let pp_loc x = match x with
| Loc_unknown -> string "unknown"
| Loc_range(pos1,pos2) -> string "(" ^^ string "range" ^^ string " " ^^ string (pp_pos pos1) ^^ string " " ^^ string (pp_pos pos2) ^^ string ")"


let pp_fail r = match r with
  | Minisailplus_ast.Monad.VarUnknown (loc,VNamed s) -> string ("var unknown ") ^^ (pp_loc loc) ^^ string " " ^^ (string s)
  | OperandTypesWrongLeft _ -> string "Ops wrong"
  | OperandTypesWrongRight _ -> string "Ops wrong"
  | CheckFail (loc,g,s,t1,t2) ->
     pp_g g [] C_true;
     string ("check fail: ") ^^ (pp_loc loc) ^^  (string s) ^^ 
       string "\nActual: " ^^ (Minisailplus_pp.pp_tp t1) ^^
       string "\nExpected: " ^^ (Minisailplus_pp.pp_tp t2)
  | IfCondType (loc,_) -> string "ifcond"
  | IfThenBranchType loc -> string "ifthen"
  | IfElseBranchType loc -> string "ifeslse"
  | NotSatisfiable ->  string "not satis"
  | FunctionUnknown (_,VNamed f) -> string "Function " ^^ (string ( f)) ^^ (string " unknown ")
  | VectorElementsDiffType -> string "vector"
  | UnknownConstructor (loc,_) ->  string "unknown ctor"
  | NotImplemented (loc,s) -> string ("Not implemented ") ^^ (pp_loc loc) ^^ string (" " ^ s)
  | TypeError (loc,s) -> string ("Type error") ^^ (pp_loc loc) ^^ string( " " ^ s)
  | UnknownErrorLoc loc -> string ("Unknown Error ") ^^ (pp_loc loc)
  | FunctionArgWrongType (loc,t1,t2) -> string ("FunctionArgWrongType ") ^^ (pp_loc loc) ^^
                                        string "\nActual: " ^^ (pp_tp t1) ^^
                                        string "\nExpected:" ^^ (pp_tp t2) 
  | ScopeError (loc, g , x) -> (pp_g g [] C_true); string "Error: Scope Error (l=" ^^ (pp_loc loc) ^^ string ") variable=" ^^ (pp_xp x) ^^ string "\n" 
