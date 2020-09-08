open PPrintEngine
open PPrintCombinators
open Sail_pp
open Type_check

let getEnv tan   = match Type_check.destruct_tannot tan with
    Some (env,_,_) -> Some env
  | _ -> None

let getEnvE (Ast.E_aux (_, (_,tan))) = getEnv tan
       
let getType tan = match Type_check.destruct_tannot tan with
    Some (_,typ,_) -> Some typ
  | _ -> None

let getTypeE (Ast.E_aux (_, (_,tan))) = getType tan

let getTypeL (Ast.LEXP_aux (_, (_,tan))) = getType tan
                                                                            
       
let lookup_local_id tan x = match getEnv tan with
    Some env -> (match Type_check.Env.lookup_id x env with
                  Local (_,t) -> Some t
                 | _ -> None)
  | None -> None

let lookup_local_id_env env x = match Type_check.Env.lookup_id x env with
                  Local (_,t) -> Some t
                 | _ -> None

let rec lookup_field fields ((Ast.Id_aux (Ast.Id fid1, _)) as fid) = match fields with
    [] -> None
  | ( (typ , Ast.Id_aux (Ast.Id fid2, _))::fields) ->
     Printf.eprintf "lookup_field %s ?= %s\n" fid1 fid2;
     if fid1 = fid2 then Some typ
     else lookup_field fields fid


let lookup_record_field_env env x y =
 Printf.eprintf "lookup_record_field_env \n";
 let ( tcq , fields ) = Type_check.Env.get_record x env in
 lookup_field fields y

  
let lookup_record_field tan x y =
 Printf.eprintf "lookup_record_field \n";
  match getEnv tan with
    Some env -> lookup_record_field_env env x y
  | None -> None

let lookup_fun_env env ((Ast.Id_aux ((Ast.Id x), _)) as fid) =
  Printf.eprintf "lookup_fun_env %s\n" x;
  match Env.get_val_spec fid env with
    ( _ , Typ_aux (Typ_fn (in_typs, ret_typ , _), _)) -> Some (in_typs, ret_typ)
  | _ -> None
       
let lookup_fun tan fid = match getEnv tan with
    Some env -> lookup_fun_env env fid
  | None -> None

          
let print_type typ =
  PPrintEngine.ToChannel.compact stderr ((pp_typ typ) ^^ string "\n");
  true

(* FIXME - Just pull these out of Ast ? *)
let equal_order (Ast.Ord_aux (o1,_)) (Ast.Ord_aux (o2, _)) = (o1 = o2)
  
let add_constraint  = Type_check.Env.add_constraint

let trace s = Printf.eprintf "%s\n" s
