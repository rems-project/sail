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

let little_endian = false ;;

let hex_to_big_int s = Big_int.big_int_of_int64 (Int64.of_string s) ;;

(* XXX POWER is big-endian - cheating until we have Kathy's switch *)
let flip_vec (V_vector (i, inc, l)) = V_vector (i, not inc, l)

let big_int_to_vec b size =
  flip_vec (
  (if little_endian then to_vec_inc else to_vec_dec) 
  size
  (V_lit (L_aux (L_num b, Unknown)))
  )
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

let init_reg () =
  List.fold_left (fun r (k,v) -> Reg.add k v r) Reg.empty [
    Id_aux(Id "CIA", Unknown), big_int_to_vec (hex_to_big_int !startaddr) 64 ;
  ]
;;

let args = [
  ("--file", Arg.Set_string file, "filename binary code to load in memory");
  ("--data", Arg.String add_section, "name,offset,size,addr add a data section");
  ("--code", Arg.String add_section, "name,offset,size,addr add a code section");
  ("--startaddr", Arg.Set_string startaddr, "addr initial address");
  ("--mainaddr", Arg.Set_string mainaddr, "addr address of the main section");
] ;;

let time_it action arg =
  let start_time = Sys.time () in
  ignore (action arg);
  let finish_time = Sys.time () in
  finish_time -. start_time
;;

let run () =
  Arg.parse args (fun _ -> raise (Arg.Bad "anonymous parameter")) "" ;
  if !file = "" then begin
    Arg.usage args "";
    exit 1;
  end;
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
  let r = Run_interp.run ~mem:!mem ~reg (!file, Power.defs) in
  eprintf "%s\n" (if r then "SUCCESS" else "FAILURE")
;;

run () ;;
