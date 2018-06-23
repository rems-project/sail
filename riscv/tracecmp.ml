(* Simple trace comparison checker *)

type csr_read = {
  csrr : string;
  rdval : int64
}

type csr_write = {
  csrw : string;
  wrval : int64;
  inval : int64
}

type reg_write = {
  reg : int;
  rval : int64
}

type inst = {
  count : int;
  priv : char;
  pc : int64;
  inst: int32
}

type tick = {
  time : int64
}

type line =
  | L_none
  | L_inst of inst
  | L_reg_write of reg_write
  | L_csr_read of csr_read
  | L_csr_write of csr_write
  | L_tick of tick

let inst_count = ref 0

(* csr reads
   CSR mscratch -> 0x0000000000000000
 *)

let parse_csr_read l =
  try Scanf.sscanf l " CSR %s -> 0x%Lx" (fun csrr rdval -> L_csr_read { csrr; rdval })
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

let sprint_csr_read r =
  Printf.sprintf "CSR %s -> 0x%Lx" r.csrr r.rdval

(* csr writes
   CSR mstatus <- 0x0000000a00020800 (input: 0x0000000a00020800)
 *)

let parse_csr_write l =
  try Scanf.sscanf l " CSR %s <- 0x%Lx (input: 0x%Lx)"
                  (fun csrw wrval inval -> L_csr_write { csrw; wrval; inval })
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

let sprint_csr_write r =
  Printf.sprintf "CSR %s <- 0x%Lx (input: 0x%Lx)" r.csrw r.wrval r.inval

(* reg writes
   x16 <- 0x0000000000000000
 *)

let parse_reg_write l =
  try Scanf.sscanf l " x%u <- 0x%Lx"
                  (fun reg rval -> L_reg_write { reg; rval })
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

let sprint_reg_write r =
  Printf.sprintf "x%u <- 0x%Lx" r.reg r.rval

(* instructions *)

let sprint_inst r =
  Printf.sprintf "[%u] [%c]: 0x%Lx (0x%lx)" r.count r.priv r.pc r.inst

(* sail instruction line:
  [13000] [M]: 0x0000000080000E4A (0x0107971B) slli  a4, a5, 0b10000
 *)

let parse_sail_inst l =
  try Scanf.sscanf l " [%u] [%c]: 0x%Lx (0x%lx) %s"
                   (fun count  priv  pc inst _ ->
                    inst_count := count;
                    L_inst { count; priv; pc; inst })
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

(* spike instruction line:
  [2] core   0 [M]: 0x0000000000001008 (0xf1402573) csrr    a0, mhartid
 *)

let parse_spike_inst l =
  try Scanf.sscanf l " [%u] core   0 [%c]: 0x%Lx (0x%lx) %s"
                   (fun count  priv  pc inst _ ->
                    inst_count := count;
                    L_inst { count; priv; pc; inst })
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

(* clock tick
   clint::tick mtime <- 0x1
 *)

let parse_tick l =
  try Scanf.sscanf l " clint::tick mtime <- 0x%Lx"
                   (fun time -> L_tick { time })
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

let sprint_tick t =
  Printf.sprintf "clint::tick mtime <- 0x%Lx" t.time

(* scanners *)

let popt p l = function
  | L_none -> p l
  | res -> res

let parse_line l =
  parse_csr_read l |> popt parse_csr_write l
  |> popt parse_reg_write l |> popt parse_tick l

let parse_sail_line l =
  parse_line l |> popt parse_sail_inst l

let parse_spike_line l =
  parse_line l |> popt parse_spike_inst l

(* printer *)
let sprint_line = function
  | L_none -> "<not-parsed>"
  | L_inst i -> sprint_inst i
  | L_reg_write r -> Printf.sprintf "<%d> %s" !inst_count (sprint_reg_write r)
  | L_csr_read  r -> Printf.sprintf "<%d> %s" !inst_count (sprint_csr_read r)
  | L_csr_write r -> Printf.sprintf "<%d> %s" !inst_count (sprint_csr_write r)
  | L_tick t      -> Printf.sprintf "<%d> %s" !inst_count (sprint_tick t)

(* file processing *)

let rec get_line ch parse =
  let line = try  Some (input_line ch)
             with End_of_file -> None in
  match line with
    | Some l -> (match parse l with
                   | L_none -> get_line ch parse
                   | r -> r
                )
    | None -> L_none

let rec print_lines ch parse =
  match (get_line ch parse) with
    | L_none -> ()
    | l      -> (print_endline (sprint_line l);
                 print_lines ch parse)


let rec compare_traces k l cnt =
  let kro = get_line k parse_spike_line in
  let lro = get_line l parse_sail_line in
  match kro, lro with
    | L_none, L_none ->
          print_endline (Printf.sprintf "Matched %d instructions" cnt)
    | L_none, lr ->
          print_endline  "Spike: not reached";
          print_endline ("Sail:  " ^ sprint_line lr);
          exit 1
    | kr, L_none ->
          print_endline ("Spike: " ^ sprint_line kr);
          print_endline  "Sail:  not reached";
          exit 1
    | kr, lr ->
          if kr <> lr
          then ( print_endline ("Spike: " ^ sprint_line kr);
                 print_endline ("Sail:  " ^ sprint_line lr);
                 exit 1 )
          else compare_traces k l (cnt + 1)

let spike_log  = ref (None : string option)
let sail_log   = ref (None : string option)
let uncompress = ref false

let in_file f =
  if !uncompress
  then Unix.open_process_in ("gunzip -c " ^ f)
  else open_in f

let options =
  Arg.align ([( "-z",
                Arg.Set uncompress,
                " uncompress trace files");
              ( "-k",
                Arg.String (fun f -> spike_log := Some f),
                " spike trace log");
              ( "-l",
                Arg.String (fun f -> sail_log := Some f),
                " sail trace log")])
let usage = "usage: tracecmp [options]\n"

let _ =
  Arg.parse options (fun s -> print_endline usage; exit 0)
            usage;
  match !spike_log, !sail_log with
    | None, None     -> (print_endline usage; exit 0)
    | Some l, None   -> print_lines (in_file l) parse_spike_line
    | None, Some l   -> print_lines (in_file l) parse_sail_line
    | Some k, Some l -> compare_traces (in_file k) (in_file l) 0

