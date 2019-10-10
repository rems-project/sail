(*open Util2*)
open PPrintEngine
open PPrintCombinators
open Minisailplus_pp
open Convert_pp
       
module MAST = Minisailplus_ast.SyntaxVCT
module Ctx = Minisailplus_ast.Contexts

type solver = {
    command : string;
    header : string;
    footer : string;
    negative_literals : bool;
    uninterpret_power : bool
  }

let cvc4_solver = {
    command = "cvc4 -L smtlib2 --tlimit=2000";
    header = "(set-logic QF_AUFDTLIA)\n";
    footer = "";
    negative_literals = false;
    uninterpret_power = true
  }

let z3_solver = {
    command = "z3 -t:1000 -T:10";
    (* Using push and pop is much faster, I believe because
       incremental mode uses a different solver. *)
    header = "(push)\n" ; (*"(set-logic QF_AUFLIA)\n(push)\n";*)
    footer = "(pop)\n";
    negative_literals = true;
    uninterpret_power = false;
  }

               
type smt_result = Unknown  | Unsat 

let opt_solver = ref z3_solver

let set_solver = function
  | "z3" -> opt_solver := z3_solver
  | "cvc4" -> opt_solver := cvc4_solver
                     
let convert_isa_string ( x : Minisailplus_ast.Stringa.char list) :string =  (Minisailplus_ast.Stringa.implode x)

let pp_ge e = match e with
    Ctx.GEPair (b,c) -> (pp_bp b) ^^ string " " ^^ (pp_cp c)
  | GETyp t -> pp_tp t

let pp_g (Minisailplus_ast.Contexts.Gamma_ext (_,g1,g2,_,_,_,scope,_,_,_)) xbc c =
  let g = g1@g2 in
  PPrintEngine.ToChannel.compact stderr ( string "Evars" ^^  (separate (string " ") (List.map
           (fun (MAST.VNamed x, e) ->
             (string x ^^ string " , " ^^ (pp_ge e)  ^^ string "\n" )) xbc)) ^^ 
                                            string "G=\n" ^^ (separate (string "\n") (List.map (fun (MAST.VNamed x , e) ->
                                                                                          string x ^^  string " : " ^^ (pp_ge e)) g)) ^^
                                              string "\nC=" ^^ (pp_cp c) ^^ string "\nVariables in scope:\n" ^^ 
                                                (separate (string " ") (List.map (fun (MAST.VNamed x) -> string x) scope)) ^^
                                                  string "\n"
    )
                                 
                               
let traceG (s : string) g xbc c =
  if !Tracing.opt_verbosity > 0 then 
    (*    let s = convert_isa_string s in *)
    let _ = pp_g g xbc c in
    true
  else
    true
 

                               
let rec satisfiable (label : string) loc ( str_list : string list ) ( def : bool ) =
(*  let label = convert_isa_string label in
  let str_list = List.map convert_isa_string str_list in *)
  let z3_file = Util_ms.string_of_list "\n" (fun x -> x) str_list in
  let z3_file = !opt_solver.header ^ "\n" ^ z3_file ^ "\n" ^ !opt_solver.footer in
  Printf.eprintf "CALLZ3\n";
  if !Tracing.opt_verbosity > 1 then 
    (prerr_endline (Printf.sprintf "Label: %s" label);
     PPrintEngine.ToChannel.compact stderr (string "Location: " ^^ (pp_loc loc));
     prerr_endline (Printf.sprintf "SMTLIB2 constraints are: \n%s%!" z3_file)); 

  let rec input_lines chan = function
    | 0 -> ""
    | n ->
       begin
         try 
           let l = input_line chan in
           let ls = input_lines chan (n - 1) in
           l ^ ls
         with | End_of_file -> ""
       end
  in

  let split_sexp (s : string ) : (string*string) list = []
(*    match Sexplib.Sexp.of_string s with
      List vs -> List.map (fun (Sexplib.Sexp.List [Atom x ; Atom v]) -> (x,v) ) vs*)
  in
  
  let get_values [(_,result)] = []
(*    if ((String.sub result 0 3 = "sat") && (String.length result > 5)) then
      split_sexp (String.sub result 3 (String.length result - 3))
    else []*)
  in

  begin
    let (input_file, tmp_chan) = Filename.open_temp_file "constraint_" ".smt2" in
    output_string tmp_chan z3_file;
    close_out tmp_chan;
    let z3_chan = Unix.open_process_in ( !opt_solver.command ^ " "  ^ input_file) in
    let problems = [ input_file ] in
    let z3_output = List.combine problems [input_lines z3_chan 20] in
    let _ = Unix.close_process_in z3_chan in
    let _ = 
      if !Tracing.opt_verbosity > 1 then 
        let _ = List.iter (fun (_, result) -> Printf.eprintf "Z3 Result: %s\n" result) z3_output in
        let vals = get_values z3_output in
        let _ = List.iter (fun (x,y) -> Printf.eprintf "Val %s=%s\n" x y) vals in ()
      else
        () in

    let _ = Sys.remove input_file in
    try
      let (problem, _) = List.find (fun (_, result) -> result = "unsat") z3_output in false
    with
    | Not_found ->
       z3_output
       |> List.filter (fun (_, result) -> result = "unknown")
       |> List.map fst
       |> (fun unsolved -> true )
  end

  
let trace2 s es g =
  if !Tracing.opt_verbosity > 0 then (
    Printf.eprintf "Trace: %s\n" (convert_isa_string s);
    List.iter (fun e ->   PPrintEngine.ToChannel.compact stderr (Minisailplus_pp.pp_ep e)) es;
    PPrintEngine.ToChannel.compact stderr
                           (string "G=\n" ^^ (separate (string " ") (List.map
                                                                       (fun (MAST.VNamed x , (b,c)) ->
                                                                         string x ^^ (pp_raw_bp b) ^^ string " " ^^ (pp_raw_cp c)) g)));

    true)
  else
    true
