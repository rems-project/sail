open Printf ;;
open Interp ;;
open Interp_ast ;;
open Interp_lib ;;
open Run_interp ;;

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

let big_int_to_vec b size =
  (if big_endian then to_vec_inc else to_vec_dec)
  size
  (V_lit (L_aux (L_num b, Unknown)))
;;

let mem = ref Mem.empty ;;

let add_mem byte addr =
  assert(byte >= 0 && byte < 256);
  let vector = big_int_to_vec (Big_int.big_int_of_int byte) 8 in
  let key = Id_aux (Id "MEM", Unknown), addr in
  mem := Mem.add key vector !mem
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
    let offset = function
      V_vector(_, inc, v) ->
        V_vector(Big_int.big_int_of_int (64 - size), inc, v)
     | _ -> assert false in
    Id_aux(Id name, Unknown), offset (big_int_to_vec value size) in
  List.fold_left (fun r (k,v) -> Reg.add k v r) Reg.empty [
    (* XXX execute main() directly until we can handle the init phase *)
    init "CIA" (hex_to_big_int !mainaddr) 64;
    init "GPR1" Big_int.zero_big_int 64;
    init "GPR31" Big_int.zero_big_int 64;
    init "CTR" Big_int.zero_big_int 64;
    init "CR" Big_int.zero_big_int 32;
    init "LR" lr_init_value 64;
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
  let reg_content = Reg.find (Id_aux(Id name, Unknown)) reg in
  match to_num true reg_content with
  | V_lit(L_aux(L_num n, Unknown)) -> n
  |  _ -> assert false
;;

let rec fde_loop count entry mem reg prog =
  debugf "\n**** cycle %d  ****\n" count;
  match Run_interp.run ~entry ~mem ~reg ~eager_eval:!eager_eval prog with
  | false, _ -> eprintf "FAILURE\n"; exit 1
  | true, (reg, mem) ->
      if Big_int.eq_big_int (get_reg reg "CIA") lr_init_value then
        eprintf "\nSUCCESS: returned with value %s\n"
          (Big_int.string_of_big_int (get_reg reg "GPR3"))
      else
        fde_loop (count+1) entry mem reg prog
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
  (* entry point: unit -> unit cycle *)
  let entry = E_aux(E_app(Id_aux((Id "cycle"),Unknown),
    [E_aux(E_lit (L_aux(L_unit,Unknown)),(Unknown,None))]),(Unknown,None)) in
  let name = Filename.basename !file in
  let t =time_it (fun () -> fde_loop 0 entry !mem reg (name, Power.defs)) () in
  eprintf "Execution time: %f seconds\n" t
;;

run () ;;
