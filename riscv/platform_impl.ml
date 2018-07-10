(* FIXME: copyright header *)

(* int->byte converters in little-endian order *)

let uint32_to_bytes u = let open Int32 in
 List.map to_int
  [ logand u 0xffl;
    logand (shift_right u 8) 0xffl;
    logand (shift_right u 16) 0xffl;
    logand (shift_right u 24) 0xffl;
  ]

let uint64_to_bytes u = let open Int64 in
 List.map to_int
  [ logand u 0xffL;
    logand (shift_right u 8) 0xffL;
    logand (shift_right u 16) 0xffL;
    logand (shift_right u 24) 0xffL;
    logand (shift_right u 32) 0xffL;
    logand (shift_right u 40) 0xffL;
    logand (shift_right u 48) 0xffL;
    logand (shift_right u 56) 0xffL;
  ]

(* reset vector for the rom *)

let reset_vec_size = 8l;;

let reset_vec_int start_pc = [
  0x297l;                                                 (* auipc  t0, 0x0      *)
  (let open Int32 in
   add 0x28593l (shift_left (mul reset_vec_size 4l) 20)); (* addi   a1, t0, ofs(dtb) *)
  0xf1402573l;                                            (* csrr   a0, mhartid  *)
  0x0182b283l;                                            (* ld     t0, 24(t0)   *)
  0x28067l;                                               (* jr     t0           *)
  0x0l;
  (let open Int64 in to_int32 (logand start_pc 0xffffffffL));
  (let open Int64 in to_int32 (shift_right_logical start_pc 32));
]

(* address map *)

let dram_base  = 0x80000000L;;  (* Spike::DRAM_BASE *)
let dram_size  = Int64.(shift_left 2048L 20)
let clint_base = 0x02000000L;;  (* Spike::CLINT_BASE *)
let clint_size = 0x000c0000L;;  (* Spike::CLINT_SIZE *)
let rom_base   = 0x00001000L;;  (* Spike::DEFAULT_RSTVEC *)

type mem_region = {
    addr : Int64.t;
    size : Int64.t
}

(* dts from spike *)
let spike_dts isa_spec cpu_hz insns_per_rtc_tick mems =
    "/dts-v1/;\n"
  ^ "\n"
  ^ "/ {\n"
  ^ "  #address-cells = <2>;\n"
  ^ "  #size-cells = <2>;\n"
  ^ "  compatible = \"ucbbar,spike-bare-dev\";\n"
  ^ "  model = \"ucbbar,spike-bare\";\n"
  ^ "  cpus {\n"
  ^ "    #address-cells = <1>;\n"
  ^ "    #size-cells = <0>;\n"
  ^ "    timebase-frequency = <" ^ string_of_int (cpu_hz/insns_per_rtc_tick) ^ ">;\n"
  ^ "    CPU0: cpu@0 {\n"
  ^ "      device_type = \"cpu\";\n"
  ^ "      reg = <0>;\n"
  ^ "      status = \"okay\";\n"
  ^ "      compatible = \"riscv\";\n"
  ^ "      riscv,isa = \"" ^ isa_spec ^ "\";\n"
  ^ "      mmu-type = \"riscv,sv39\";\n"
  ^ "      clock-frequency = <" ^ string_of_int cpu_hz ^ ">;\n"
  ^ "      CPU0_intc: interrupt-controller {\n"
  ^ "        #interrupt-cells = <1>;\n"
  ^ "        interrupt-controller;\n"
  ^ "        compatible = \"riscv,cpu-intc\";\n"
  ^ "      };\n"
  ^ "    };\n"
  ^ "  };\n"
  ^ (List.fold_left (^) ""
       (List.map (fun m ->
         "  memory@" ^ Printf.sprintf "%Lx" m.addr ^ " {\n"
         ^ "    device_type = \"memory\";\n"
         ^ "    reg = <0x" ^ Printf.sprintf "%Lx" Int64.(shift_right_logical m.addr 32) ^ " 0x" ^ Printf.sprintf "%Lx" Int64.(logand m.addr 0xffffffffL)
         ^           " 0x" ^ Printf.sprintf "%Lx" Int64.(shift_right_logical m.size 32) ^ " 0x" ^ Printf.sprintf "%Lx" Int64.(logand m.size 0xffffffffL) ^ ">;\n"
         ^ "  };\n") mems))
  ^ "  soc {\n"
  ^ "    #address-cells = <2>;\n"
  ^ "    #size-cells = <2>;\n"
  ^ "    compatible = \"ucbbar,spike-bare-soc\", \"simple-bus\";\n"
  ^ "    ranges;\n"
  ^ "    clint@" ^ Printf.sprintf "%Lx" clint_base ^ " {\n"
  ^ "      compatible = \"riscv,clint0\";\n"
  ^ "      interrupts-extended = <&CPU0_intc 3 &CPU0_intc 7 >;\n"
  ^ "      reg = <0x" ^ Printf.sprintf "%Lx" Int64.(shift_right_logical clint_base 32) ^ " 0x" ^ Printf.sprintf "%Lx" Int64.(logand clint_base 0xffffffffL)
  ^             " 0x" ^ Printf.sprintf "%Lx" Int64.(shift_right_logical clint_size 32) ^ " 0x" ^ Printf.sprintf "%Lx" Int64.(logand clint_size 0xffffffffL) ^ ">;\n"
  ^ "    };\n"
  ^ "  };\n"
  ^ "  htif {\n"
  ^ "    compatible = \"ucb,htif0\";\n"
  ^ "  };\n"
  ^ "};\n"

let cpu_hz = 1000000000;;
let insns_per_tick = 100;;

let mems = [ { addr = dram_base;
               size = dram_size } ];;
let dts = spike_dts "rv64imac" cpu_hz insns_per_tick mems;;

let bytes_to_string bytes =
  String.init (List.length bytes) (fun i -> Char.chr (List.nth bytes i))

let dtc_path = ref "/usr/bin/dtc"

let set_dtc path =
  try let st = Unix.stat path in
      if st.Unix.st_kind = Unix.S_REG && st.Unix.st_perm != 0
      then dtc_path := path
      else ( Printf.eprintf "%s doesn't seem like a valid executable.\n%!" path;
             exit 1)
  with Unix.Unix_error (e, _, _) ->
    ( Printf.eprintf "Error accessing %s: %s\n%!" path (Unix.error_message e);
      exit 1)

let make_dtb dts = (* Call the dtc compiler, assumed to be at /usr/bin/dtc *)
  try
    let cmd = Printf.sprintf "%s -I dts" !dtc_path in
    let (cfrom, cto, cerr) =
      Unix.open_process_full cmd [||]
    in (
      output_string cto dts;
      (* print_endline " sent dts to dtc ..."; *)
      close_out cto;
      (* simple and stupid for now *)
      let rec accum_bytes cin acc =
        match (
          try  Some (input_byte cin)
          with End_of_file -> None
        ) with
          | Some b -> accum_bytes cin (b :: acc)
          | None   -> List.rev acc
      in
      (* let _ = print_endline " accumulating dtb ..." in *)
      let dtb  = accum_bytes cfrom [] in
      (* let _ = print_endline " accumulating emsg ..." in *)
      let emsg = bytes_to_string (accum_bytes cerr []) in
      match Unix.close_process_full (cfrom, cto, cerr) with
        | Unix.WEXITED 0 -> dtb
        | _ -> (Printf.printf "%s\n%!" ("Error executing dtc: " ^ emsg);
                exit 1)
    )
  with Unix.Unix_error (e, fn, _) ->
    (Printf.printf "%s\n" ("Error executing dtc: " ^ fn ^ ": " ^ Unix.error_message e);
     exit 1)

(* Terminal I/O *)

let term_write char =
  ignore (Unix.write_substring Unix.stdout (String.make 1 char) 0 1)

let rec term_read () =
  let buf = Bytes.make 1 '\000' in
  let nbytes = Unix.read Unix.stdin buf 0 1 in
  (* todo: handle nbytes == 0 *)
  Bytes.get buf 0

(* Platform diagnostics *)

let show_bytes s =
  output_string stdout s

let dump_dts () = show_bytes dts
let dump_dtb () = show_bytes (bytes_to_string (make_dtb dts))

(*
let save_string_to_file s fname =
  let out = open_out fname in
  output_string out s;
  close_out out;;

 *)
