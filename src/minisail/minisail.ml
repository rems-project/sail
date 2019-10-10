open Convert_ast
open Minisailplus_pp
open PPrintEngine
open PPrintCombinators


let opt_dmsp_check = ref None

let check_ast vrb sail_ast =
  let ms_ast = convert_ast sail_ast in
  if vrb > 0 then 
    PPrintEngine.ToChannel.compact stderr ((string "MS AST=") ^^ (pp_progp ms_ast) ^^ (string "\n"))
  else ()

