open Sail2_values
open Sail2_state_monad

let from_bit = function B0 -> false | B1 -> true | BU -> false

let from_bits bs = Lem.wordFromBitlist (List.map from_bit bs)

let to_bits bv = List.map bitU_of_bool (Lem.bitlistFromWord bv)

let from_addr bs = FROMADDR

let rec liftState ra m =
  let open Sail2_concurrency_interface_v2 in
  match m with
  | Done a -> returnS a
  | Fail s -> failS s
  | Exception e -> throwS e
  | Choose _ -> failwith "unconstrained choice"
  | Read_reg (r, k) -> bindS (read_regvalS ra r) (fun v -> liftState ra (k v))
  | Write_reg (r, v, k) -> seqS (write_regvalS ra r v) (liftState ra k)
  (* The state monad only does single tags so we assume that here, but this is just for testing, anyway.
     Note that the Sail vectors of bytes are big-endian, so we need a reversal. *)
  | Mem_read (req, k) ->
      bindS
        (read_memt_bytesS req.mem_request_access_kind (from_addr req.mem_request_address) (Z.to_int req.mem_request_size)
        )
        (fun (v, t) -> liftState ra (k (Ok (List.rev_map from_bits v, [from_bit t]))))
  | Mem_write (req, v, tags, k) ->
      bindS
        (write_memt_bytesS req.mem_request_access_kind (from_addr req.mem_request_address)
           (Z.to_int req.mem_request_size) (List.rev_map to_bits v)
           (match tags with h :: _ -> bitU_of_bool h | [] -> B0)
        )
        (fun v -> liftState ra (k (Ok ())))
  | Mem_write_address_announce (_req, k) -> liftState ra k
  | Barrier_request (_req, k) -> liftState ra k
  | Cache_op_request (_req, k) -> liftState ra k
  | TLB_op_request (_req, k) -> liftState ra k
  | Take_exception (_exn, k) -> liftState ra k
  | Return_exception k -> liftState ra k
  | Translation_start (_ts, k) -> liftState ra k
  | Translation_end (_te, k) -> liftState ra k
;;

match Pset.elements (liftState MODULENAME_types.register_accessors (MODULENAME.main ()) (init_state REGSTATE)) with
| [(Value _, _)] -> exit 0
| [(Ex (Failure s), _)] ->
    prerr_endline ("Assertion failed: " ^ s);
    exit 1
| _ ->
    prerr_endline "Unexpected outcome";
    exit 1
