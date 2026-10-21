open Sail2_state_monad

let rec liftState ra m =
  let open Sail2_prompt_monad in
  match m with
  | Done a -> returnS a
  | Read_mem (rk, a, sz, k) -> bindS (read_mem_bytesS rk a sz) (fun v -> liftState ra (k v))
  | Read_memt (rk, a, sz, k) -> bindS (read_memt_bytesS rk a sz) (fun v -> liftState ra (k v))
  | Write_mem (wk, a, sz, v, k) -> bindS (write_mem_bytesS wk a sz v) (fun v -> liftState ra (k v))
  | Write_memt (wk, a, sz, v, t, k) -> bindS (write_memt_bytesS wk a sz v t) (fun v -> liftState ra (k v))
  | Read_reg (r, k) -> bindS (read_regvalS ra r) (fun v -> liftState ra (k v))
  | Excl_res k -> bindS (excl_resultS ()) (fun v -> liftState ra (k v))
  (*  | (Choose _ k)               -> bindS (chooseS universal)             (fun v -> liftState ra (k v))*)
  (* Unconstrained choice of a regval isn't useful for execution,
     because we don't know what the actual expected type is.  Instead
     we override the undefined_* functions in Lem. *)
  | Choose (_, k) -> failS "Can't do Choose at all right now"
  | Write_reg (r, v, k) -> seqS (write_regvalS ra r v) (liftState ra k)
  | Write_ea (_, _, _, k) -> liftState ra k
  | Footprint k -> liftState ra k
  | Barrier (_, k) -> liftState ra k
  | Print (_, k) -> liftState ra k (* TODO *)
  | Fail descr -> failS descr
  | Exception e -> throwS e
;;

match Pset.elements (liftState MODULENAME_types.register_accessors (MODULENAME.main ()) (init_state REGSTATE)) with
| [(Value _, _)] -> exit 0
| [(Ex (Failure s), _)] ->
    prerr_endline ("Assertion failed: " ^ s);
    exit 1
| _ ->
    prerr_endline "Unexpected outcome";
    exit 1
