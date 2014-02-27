open Printf ;;
open Interp ;;
open Interp_ast ;;
open Interp_lib ;;
open Run_interp ;;

let rec foldli f acc ?(i=0) = function
  | [] -> acc
  | x::xs -> foldli f (f i acc x) ~i:(i+1) xs
;;

(* POWER is big-endian *)
let little_endian = false ;;

let binary file =
  let ic = open_in_bin file in
  let rec read acc =
    match try Some (input_byte ic) with End_of_file -> None
    with
    | Some b -> read ((V_lit (L_aux (L_num (Big_int.big_int_of_int b), Unknown))) :: acc)
    | None -> close_in ic; acc in
  let bytes = read [] in
  List.rev_map ((if little_endian then to_vec_inc else to_vec_dec) 8) bytes
;;

let init_mem bytes =
  foldli
    (fun i m b -> Mem.add (Id_aux (Id "MEM", Unknown), Big_int.big_int_of_int i) b m)
    Mem.empty bytes
;;

let run () =
  let file = Sys.argv.(1) in
  let bytes = binary file in
  eprintf "bytes read\n";
  let mem = init_mem bytes in
  eprintf "memory initialized\n";
  let r = Run_interp.run ~mem (file, Power.defs) in
  eprintf "%s\n" (if r then "SUCCESS" else "FAILURE")
;;

run () ;;
