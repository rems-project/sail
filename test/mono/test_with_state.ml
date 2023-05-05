module P = Sail2_prompt_monad

let rec run regs m =
  match m with
  | P.Done _ -> 0
  | P.Read_reg (r, k) -> run regs (k (Option.get (Out_types.get_regval r regs)))
  | P.Write_reg (r, v, k) -> run (Option.get (Out_types.set_regval r v regs)) k
  | P.Fail s ->
      prerr_endline ("Fail: " ^ s);
      exit 1
  | _ ->
      prerr_endline "Unexpected outcome";
      exit 1
;;
run Out.initial_regstate (Out.run ())
