(* Code for doing local rewrites of AST *)

open Minisailplus_ast
open Minisailplus_ast.SyntaxVCT
open Minisailplus_ast.SyntaxPED

type 'a walker = {
    visit_def : (def -> 'a * def) option;
    visit_b   : (bp -> 'a * bp ) option;
}

let initWalker = { visit_def = None; visit_b = None }

let rec b_walk w b =
  let b = match (w.visit_b) with
      Some f -> let (_,b) = f b in b
    | None -> b in
  match b with
  | B_tuple bs -> B_tuple (List.map (b_walk w) bs)
  | B_record (bs) -> B_record (List.map (fun (s,b) -> (s,b_walk w b)) bs)
  | B_union (s,ts) -> B_union (s,List.map (fun (s,t) -> (s,t_walk w t)) ts)
  | B_vec (o,b) -> B_vec (o, b_walk w b)
  | b -> b
and t_walk w (T_refined_type (z, b, c)) =
  (T_refined_type ( z , b_walk w b, c))

let s_walk w s = s

let f_walk w (A_function (x , b , c ,t)) = 
     A_function (x , b_walk w b, c , t_walk w t)

let def_walk w def =
  let def = match (w.visit_def) with
      Some f -> let (_,def) = f def in def
    | None -> def in
  match def with
  | DEFp_typedef (l,id,ks,t) -> DEFp_typedef (l,id, ks,t_walk w t)
  | DEFp_fundef (l, f , funcls) ->
     let f = f_walk w f in
     let s = List.map (fun (FCLp_funcl (l,id,s)) -> (FCLp_funcl (l,id,s_walk w s))) funcls in 
     DEFp_fundef (l,f, s)
  | DEFp_spec (loc, id, f) -> DEFp_spec(loc, id, f_walk w f)
  | def -> def



