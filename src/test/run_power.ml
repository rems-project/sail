open Printf ;;
open Big_int ;;
open Interp_ast ;;
open Interp_interface ;;
open Interp_inter_imp ;;
open Run_interp_model ;;

open Sail_interface ;;

let startaddr = ref [] ;;
let mainaddr  = ref "0" ;;
let sections = ref [] ;;
let file = ref "" ;;
let print_bytes = ref false ;;
let bytes_file = ref "bytes_out.lem";;
let test_format = ref false ;;
let test_file = ref "test.txt";;
let test_memory_addr = ref (0,[]) ;;

let rec foldli f acc ?(i=0) = function
  | [] -> acc
  | x::xs -> foldli f (f i acc x) ~i:(i+1) xs
;;

let big_endian = true ;;

let hex_to_big_int s = big_int_of_int64 (Int64.of_string s) ;;

let big_int_to_vec for_mem b size =
  fst (extern_value
	 (make_mode true false)
	 for_mem
	 None
	 ((if big_endian then Interp_lib.to_vec_inc else Interp_lib.to_vec_dec)
	     (Interp.V_tuple [(Interp.V_lit (L_aux (L_num size, Unknown))); 
			      (Interp.V_lit (L_aux (L_num b, Unknown)))])))
;;

let mem = ref Mem.empty ;;
let reg = ref (Reg.add "dummy" Unknown0 Reg.empty) ;;

let add_mem byte addr =
  assert(byte >= 0 && byte < 256);
  (*Printf.printf "adder is %s, byte is %s\n" (string_of_big_int addr) (string_of_int byte);*)
  let addr = big_int_to_vec true addr (big_int_of_int 64) in
  (*Printf.printf "adder is %s byte is %s\n" (Printing_functions.val_to_string addr) (string_of_int byte);*)
  match addr with
    | Bytevector addr -> (*List.iter (fun i -> Printf.printf "%i " i) addr; Printf.printf "\n";*)
      mem := Mem.add addr byte !mem
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
    add_mem (input_byte ic) (add_int_big_int i addr);
  done
;;

let load_memory (bits,addr) =
  let rec loop bits addr = 
    if (Bitstring.bitstring_length bits = 0)
    then ()
    else let (Error.Success(bitsnum,rest)) = Ml_bindings.read_unsigned_char Endianness.default_endianness bits in
	 add_mem (Uint32.to_int bitsnum) (big_int_of_int addr);
	 loop rest (1 + addr)
  in loop bits addr

let rec read_mem mem loc length = 
  if length = 0  
  then []
  else 
    let location = big_int_to_vec true loc (big_int_of_int 64) in
    match location with
      | Bytevector location ->
	(Mem.find location mem)::(read_mem mem (add_big_int loc unit_big_int) (length - 1))

let get_reg reg name =
  let reg_content = Reg.find name reg in reg_content

(* use zero as a sentinel --- it might prevent a minimal loop from
 * working in principle, but won't happen in practice *)
let lr_init_value = zero_big_int

let init_reg () =
  let init name value size =
    (* fix index - this is necessary for CR, indexed from 32 *)
    let offset = function
      | Bitvector(bits,inc,fst) ->
        Bitvector(bits,inc,big_int_of_int (64 - size))
     | _ -> assert false in
    name, offset (big_int_to_vec false value (big_int_of_int size)) in
  List.fold_left (fun r (k,v) -> Reg.add k v r) Reg.empty (
    (* Special registers *)
    [
      init "CR" zero_big_int 32;
      init "CTR" zero_big_int 64;
      init "LR" lr_init_value 64;
      init "XER" zero_big_int 64;
      init "VRSAVE" zero_big_int 32;
      init "FPSCR" zero_big_int 64;
      init "VSCR" zero_big_int 32;
      init "SPRG4" zero_big_int 64;
      init "SPRG5" zero_big_int 64;
      init "SPRG6" zero_big_int 64;
      init "SPRG7" zero_big_int 64;
    ] @
    (* Commonly read before written general purpose register *)
      [init "GPR0" zero_big_int 64;
       init "GPR1" zero_big_int 64;
       init "GPR2" zero_big_int 64;
       init "GPR3" zero_big_int 64;
       init "GPR31" zero_big_int 64;]
      (*Conditionally include all general purpose registers *)
    @ (if !test_format
      then [ 
	init "GPR4" zero_big_int 64;
	init "GPR5" zero_big_int 64;
	init "GPR6" zero_big_int 64;
	init "GPR7" zero_big_int 64;
	init "GPR8" zero_big_int 64;
	init "GPR9" zero_big_int 64;
	init "GPR10" zero_big_int 64;
	init "GPR11" zero_big_int 64;
	init "GPR12" zero_big_int 64;
	init "GPR13" zero_big_int 64;
	init "GPR14" zero_big_int 64;
	init "GPR15" zero_big_int 64;
	init "GPR16" zero_big_int 64;
	init "GPR17" zero_big_int 64;
	init "GPR18" zero_big_int 64;
	init "GPR19" zero_big_int 64;
	init "GPR20" zero_big_int 64;
	init "GPR21" zero_big_int 64;
	init "GPR22" zero_big_int 64;
	init "GPR23" zero_big_int 64;
	init "GPR24" zero_big_int 64;
	init "GPR25" zero_big_int 64;
	init "GPR26" zero_big_int 64;
	init "GPR27" zero_big_int 64;
	init "GPR28" zero_big_int 64;
	init "GPR29" zero_big_int 64;
	init "GPR30" zero_big_int 64;]
      else [])
      @
      (if !test_format
       then [
	 init "VR0" zero_big_int 128;
	 init "VR1" zero_big_int 128;
	 init "VR2" zero_big_int 128;
	 init "VR3" zero_big_int 128;
	 init "VR4" zero_big_int 128;
	 init "VR5" zero_big_int 128;
	 init "VR6" zero_big_int 128;
	 init "VR7" zero_big_int 128;
	 init "VR8" zero_big_int 128;
	 init "VR9" zero_big_int 128;
	 init "VR10" zero_big_int 128;
	 init "VR11" zero_big_int 128;
	 init "VR12" zero_big_int 128;
	 init "VR13" zero_big_int 128;
	 init "VR14" zero_big_int 128;
	 init "VR15" zero_big_int 128;
	 init "VR16" zero_big_int 128;
	 init "VR17" zero_big_int 128;
	 init "VR18" zero_big_int 128;
	 init "VR19" zero_big_int 128;
	 init "VR20" zero_big_int 128;
	 init "VR21" zero_big_int 128;
	 init "VR22" zero_big_int 128;
	 init "VR23" zero_big_int 128;
	 init "VR24" zero_big_int 128;
	 init "VR25" zero_big_int 128;
	 init "VR26" zero_big_int 128;
	 init "VR27" zero_big_int 128;
	 init "VR28" zero_big_int 128;
	 init "VR29" zero_big_int 128;
	 init "VR30" zero_big_int 128;
    	 init "VR31" zero_big_int 128;]
       else [])
      @
      (*Not really registers*)
     [(* Currint Instruciton Address, manually set *)
       init "CIA" (hex_to_big_int !mainaddr) 64;
       init "NIA" zero_big_int 64;
       "mode64bit", Bitvector([true],true,zero_big_int);
     ])
;;

let lem_print_memory m =
  let format_addr a = "[" ^ (List.fold_right (fun i r -> "(" ^ (string_of_int i) ^ ": word8);" ^ r) a "") ^ "]" in
  let preamble = "open import Pervasives\ntype word8 = nat\n" in
  let start_addr = "let start_adder_address = " ^ format_addr !startaddr ^ ";;\n" in
  let start_list_def = "let instruction_byte_list = [" in
  let list_elements = 
    Mem.fold (fun key byte rest -> 
      rest ^ "(" ^ (format_addr key) ^ ", (" ^ (string_of_int byte) ^ ":word8) );\n") m "" in
  let close_list_def = "];;" in
  let (temp_file_name, o) = Filename.open_temp_file "ll_temp" "" in
  let o' = Format.formatter_of_out_channel o in
  Format.fprintf o' "%s" (preamble ^ start_addr ^ start_list_def ^ list_elements ^ close_list_def);
  let _ = close_out o in
  Sys.rename temp_file_name !bytes_file 

let print_test_results final_reg final_mem = 
  let tilde = String.make 90 '~' in
  let preamble = "\t\t"^"Value before test" ^ "\t\t\t" ^ "Value after test\n" ^ tilde ^ "\n" in
  let format_register reg_name = 
    let original_reg = get_reg !reg reg_name in
    let final_reg = get_reg final_reg reg_name in
    reg_name ^ ";\t\t" ^ Printing_functions.val_to_hex_string original_reg ^ ";\t\t\t" ^ Printing_functions.val_to_hex_string final_reg ^ "\n"
  in
  let rec numbered_reg base_name curr_index stop_index =
    if curr_index > stop_index
    then ""
    else (format_register (base_name ^ (string_of_int curr_index))) ^ (numbered_reg base_name (curr_index +1) stop_index)
  in
  let special_reg = List.fold_right (fun r rs -> (format_register r) ^ rs) ["CR";"CTR";"LR";"XER"] "" in
  let gpr_reg = numbered_reg "GPR" 0 31 in
  let vr_reg = numbered_reg "VR" 0 31 in
  let reg_contents = special_reg ^ gpr_reg ^ (format_register "VRSAVE") ^ vr_reg ^ (format_register "VSCR") in
  let rec memory_crawl curr_index curr_address = 
    if curr_index >= 100
    then ""
    else let mem_orig = Bytevector(read_mem !mem curr_address 8) in
	 let mem_end = Bytevector(read_mem final_mem curr_address 8) in
	"MEM_" ^ (string_of_int curr_index) ^ ";\t\t" ^ Printing_functions.val_to_hex_string mem_orig ^ 
	  ";\t\t\t" ^ Printing_functions.val_to_hex_string mem_end ^ "\n" ^ 
	  (memory_crawl (curr_index + 1) (add_big_int curr_address unit_big_int))
  in
  let mem_contents = memory_crawl 0 (big_int_of_int (fst (!test_memory_addr))) in
  let footer = tilde ^ "\n" in
  let (temp_file_name, o) = Filename.open_temp_file "tt_temp" "" in
  let o' = Format.formatter_of_out_channel o in
  Format.fprintf o' "%s" (preamble ^ reg_contents ^footer ^ mem_contents);
  let _ = close_out o in
  Sys.rename temp_file_name !test_file

let eager_eval = ref true

let args = [
  ("--file", Arg.Set_string file, "filename binary code to load in memory");
  ("--data", Arg.String add_section, "name,offset,size,addr add a data section");
  ("--code", Arg.String add_section, "name,offset,size,addr add a code section");
  ("--mainaddr", Arg.Set_string mainaddr, "addr address of the main section (entry point; default: 0)");
  ("--quiet", Arg.Clear Run_interp_model.debug, "do not display interpreter actions");
  ("--interactive", Arg.Clear eager_eval , "interactive execution");
  ("--test", Arg.Set test_format , "format output for single instruction tests, save in file");
  ("--test_file", Arg.Set_string test_file , "specify the name for a file generated by --test");
  ("--dump", Arg.Set print_bytes , "do not run, just generate a lem file of a list of bytes");
  ("--dump_file", Arg.Set_string bytes_file, "specify the name for a file generated by --dump");
] ;;

let time_it action arg =
  let start_time = Sys.time () in
  ignore (action arg);
  let finish_time = Sys.time () in
  finish_time -. start_time
;;

let eq_zero = function
  | Bitvector(bools,_,_) -> List.for_all (not) bools
;;

let rec fde_loop count main_func parameters mem reg ?mode track_dependencies prog =
  debugf "\n**** instruction %d  ****\n" count;
  match Run_interp_model.run ~main_func ~parameters ~mem ~reg ~eager_eval:!eager_eval ~track_dependencies:(ref track_dependencies) ?mode prog with
  | false, _,_, _ -> eprintf "FAILURE\n"; exit 1
  | true, mode, track_dependencies, (my_reg, my_mem) ->
      if eq_zero (get_reg my_reg "CIA") then
        (if not(!test_format) 
	 then eprintf "\nSUCCESS: returned with value %s\n"
          (Printing_functions.val_to_string (get_reg my_reg "GPR3"))
	 else print_test_results my_reg my_mem)	    
      else
        fde_loop (count+1) main_func parameters my_mem my_reg ~mode:mode track_dependencies prog
;;

let run () =
  Arg.parse args (fun _ -> raise (Arg.Bad "anonymous parameter")) "" ;
  if !file = "" then begin
    Arg.usage args "";
    exit 1;
  end;
  if !eager_eval then Run_interp_model.debug := true;
  if !test_format then Run_interp_model.debug := false;
  let (((locations,start_address),_),(symbol_map)) = populate_and_obtain_symbol_to_address_mapping !file in
  let total_size = (List.length locations) in
  if not(!test_format)
  then eprintf "Loading binary into memory (%d sections)... %!" total_size;
  let t = time_it (List.iter load_memory) locations in
  if not(!test_format)
  then eprintf "done. (%f seconds)\n%!" t;
  let addr = read_mem !mem (big_int_of_int start_address) 8 in
  let _ = begin
    startaddr := addr;
    mainaddr := "0x" ^ (List.fold_left (^) "" (List.map (Printf.sprintf "%02x") addr));
  end in
  if not(!test_format) then
    Printf.printf "start address: %s\n" !mainaddr;
  let my_reg = init_reg () in
  reg := my_reg;
  if !test_format 
  then if List.mem_assoc "TEST_MEM" symbol_map
    then test_memory_addr := 
      let num = (List.assoc "TEST_MEM" symbol_map) in
      match big_int_to_vec true (big_int_of_int num) (big_int_of_int 64) with
	| Bytevector location -> (num,location);
    else ();
  (* entry point: unit -> unit fde *)
  let funk_name = "fde" in
  let parms = [] in
  let name = Filename.basename !file in
  if !print_bytes 
  then lem_print_memory !mem
  else let t =time_it (fun () -> fde_loop 0 funk_name parms !mem !reg false (name, Power.defs)) () in
       if not(!test_format) then eprintf "Execution time: %f seconds\n" t
;;

run () ;;
