open Printf ;;
(*open Interp ;;*)
open Interp_ast ;;
(*open Interp_lib ;;*)
open Interp_interface ;;
open Interp_inter_imp ;;
open Run_interp_model ;;

let startaddr = ref "0" ;;
let mainaddr  = ref "0" ;;
let sections = ref [] ;;
let file = ref "" ;;

let rec foldli f acc ?(i=0) = function
  | [] -> acc
  | x::xs -> foldli f (f i acc x) ~i:(i+1) xs
;;

let big_endian = true ;;

let hex_to_big_int s = Big_int.big_int_of_int64 (Int64.of_string s) ;;

let big_int_to_vec for_mem b size =
  fst (extern_value
	 (make_mode true false)
	 for_mem
	 ((if big_endian then Interp_lib.to_vec_inc else Interp_lib.to_vec_dec)
	     (Interp.V_tuple [(Interp.V_lit (L_aux (L_num size, Unknown))); 
			      (Interp.V_lit (L_aux (L_num b, Unknown)))])))
;;

let mem = ref Mem.empty ;;

let add_mem byte addr =
  assert(byte >= 0 && byte < 256);
  (*Printf.printf "adder is %s, byte is %s\n" (Big_int.string_of_big_int addr) (string_of_int byte);*)
  let addr = big_int_to_vec true addr (Big_int.big_int_of_int 64) in
  (*Printf.printf "adder is %s byte is %s\n" (val_to_string addr) (string_of_int byte);*)
  match addr with
    | Bytevector addr -> mem := Mem.add addr byte !mem
;;

let add_section s =
  match Str.split (Str.regexp ",") s with
  | [name;offset;size;addr] ->
      begin try
        sections := (
          int_of_string offset,
          int_of_string size,
          hex_to_big_int addr) ::
            !sections
      with Failure msg -> raise (Arg.Bad (msg ^ ": " ^ s))
      end
  | _ -> raise (Arg.Bad ("Wrong section format: "^s))
;;

let load_section ic (offset,size,addr) =
  seek_in ic offset;
  for i = 0 to size - 1 do
    add_mem (input_byte ic) (Big_int.add_int_big_int i addr);
  done
;;

(* use zero as a sentinel --- it might prevent a minimal loop from
 * working in principle, but won't happen in practice *)
let lr_init_value = Big_int.zero_big_int

let init_reg () =
  let init name value size =
    (* fix index - this is necessary for CR, indexed from 32 *)
(*    let offset = function
      V_vector(_, inc, v) ->
        V_vector(Big_int.big_int_of_int (64 - size), inc, v)
     | _ -> assert false in*)
    name, (*offset*) (big_int_to_vec false value (Big_int.big_int_of_int size)) in
  List.fold_left (fun r (k,v) -> Reg.add k v r) Reg.empty [
    (* XXX execute main() directly until we can handle the init phase *)
    init "CIA" (hex_to_big_int !mainaddr) 64;
    init "GPR1" Big_int.zero_big_int 64;
    init "GPR31" Big_int.zero_big_int 64;
    init "CTR" Big_int.zero_big_int 64;
    init "CR" Big_int.zero_big_int 32;
    init "LR" lr_init_value 64;
    "mode64bit", Bitvector [true];
  ]
;;

let eager_eval = ref true

let args = [
  ("--file", Arg.Set_string file, "filename binary code to load in memory");
  ("--data", Arg.String add_section, "name,offset,size,addr add a data section");
  ("--code", Arg.String add_section, "name,offset,size,addr add a code section");
  ("--startaddr", Arg.Set_string startaddr, "addr initial address (UNUSED)");
  ("--mainaddr", Arg.Set_string mainaddr, "addr address of the main section (entry point; default: 0)");
  ("--quiet", Arg.Clear Run_interp.debug, " do not display interpreter actions");
  ("--interactive", Arg.Clear eager_eval , " interactive execution");
] ;;

let time_it action arg =
  let start_time = Sys.time () in
  ignore (action arg);
  let finish_time = Sys.time () in
  finish_time -. start_time
;;

let get_reg reg name =
  let reg_content = Reg.find name reg in reg_content
;;

let eq_zero = function
  | Bitvector bools -> List.for_all (not) bools
;;

let rec fde_loop count main_func parameters mem reg ?mode prog =
  debugf "\n**** instruction %d  ****\n" count;
  match Run_interp_model.run ~main_func ~parameters ~mem ~reg ~eager_eval:!eager_eval ?mode prog with
  | false, _, _ -> eprintf "FAILURE\n"; exit 1
  | true, mode, (reg, mem) ->
      if eq_zero (get_reg reg "CIA") then
        eprintf "\nSUCCESS: returned with value %s\n"
          (Run_interp_model.val_to_string (get_reg reg "GPR3"))
      else
        fde_loop (count+1) main_func parameters mem reg ~mode:mode prog
;;

let run () =
  Arg.parse args (fun _ -> raise (Arg.Bad "anonymous parameter")) "" ;
  if !file = "" then begin
    Arg.usage args "";
    exit 1;
  end;
  if !eager_eval then Run_interp.debug := true;
  let ic = open_in_bin !file in
  if !sections = [] then begin
    sections := [(0, in_channel_length ic, Big_int.zero_big_int)];
  end;
  let total_size = List.fold_left (fun n (_,s,_) -> n+s) 0 !sections in
  eprintf "Loading binary into memory (%d bytes)... %!" total_size;
  let t = time_it (List.iter (load_section ic)) !sections in
  eprintf "done. (%f seconds)\n%!" t;
  close_in ic;
  let reg = init_reg () in
  (* entry point: unit -> unit fde *)
  let funk_name = "fde" in
  let args = [] in
  let name = Filename.basename !file in
  let t =time_it (fun () -> fde_loop 0 funk_name args !mem reg (name, Power.defs)) () in
  eprintf "Execution time: %f seconds\n" t
;;

run () ;;
