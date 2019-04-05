open Anf
open Ast
open Ast_util
open Jib
open Jib_util
open Smtlib

let zencode_upper_id id = Util.zencode_upper_string (string_of_id id)
let zencode_id id = Util.zencode_string (string_of_id id)
let zencode_name id = string_of_name ~deref_current_exception:false ~zencode:true id

let lbits_index = ref 8

let lbits_size () = Util.power 2 !lbits_index

let lint_size = ref 64

let smt_unit = mk_enum "Unit" ["Unit"]
let smt_lbits = mk_record "Bits" [("size", Bitvec !lbits_index); ("bits", Bitvec (lbits_size ()))]

let rec required_width n =
  if Big_int.equal n Big_int.zero then
    1
  else
    1 + required_width (Big_int.shift_right n 1)

let rec smt_ctyp = function
  | CT_constant n -> Bitvec (required_width n)
  | CT_fint n -> Bitvec n
  | CT_lint -> Bitvec !lint_size
  | CT_unit -> smt_unit
  | CT_bit -> Bitvec 1
  | CT_fbits (n, _) -> Bitvec n
  | CT_sbits (n, _) -> smt_lbits
  | CT_lbits _ -> smt_lbits
  | CT_bool -> Bool
  | CT_enum (id, elems) ->
     mk_enum (zencode_upper_id id) (List.map zencode_id elems)
  | CT_struct (id, fields) ->
     mk_record (zencode_upper_id id) (List.map (fun (id, ctyp) -> (zencode_id id, smt_ctyp ctyp)) fields)
  | CT_variant (id, ctors) ->
     mk_variant (zencode_upper_id id) (List.map (fun (id, ctyp) -> (zencode_id id, smt_ctyp ctyp)) ctors)
  | CT_tup ctyps -> Tuple (List.map smt_ctyp ctyps)
  | CT_vector (_, ctyp) -> Array (Bitvec 8, smt_ctyp ctyp)
  | CT_string -> Bitvec 64
  | ctyp -> failwith ("Unhandled ctyp: " ^ string_of_ctyp ctyp)

let bvint sz x =
  if sz mod 4 = 0 then
    let hex = Printf.sprintf "%X" x in
    let padding = String.make (sz / 4 - String.length hex) '0' in
    Hex (padding ^ hex)
  else
    failwith "Bad len"

let smt_value vl ctyp =
  let open Value2 in
  match vl, ctyp with
  | V_bits bs, _ ->
     begin match Sail2_values.hexstring_of_bits bs with
     | Some s -> Hex (Xstring.implode s)
     | None -> Bin (Xstring.implode (List.map Sail2_values.bitU_char bs))
     end
  | V_bool b, _ -> Bool_lit b
  | V_int n, CT_constant m -> bvint (required_width n) (Big_int.to_int n)
  | V_int n, CT_fint sz -> bvint sz (Big_int.to_int n)
  | V_bit Sail2_values.B0, CT_bit -> Bin "0"
  | V_bit Sail2_values.B1, CT_bit -> Bin "1"
  | V_unit, _ -> Var "unit"

  | vl, _ -> failwith ("Bad literal " ^ string_of_value vl)

let zencode_ctor ctor_id unifiers =
  match unifiers with
  | [] ->
     zencode_id ctor_id
  | _ ->
     Util.zencode_string (string_of_id ctor_id ^ "_" ^ Util.string_of_list "_" string_of_ctyp unifiers)

let rec smt_cval env cval =
  match cval with
  | F_lit vl, ctyp -> smt_value vl ctyp
  | frag, _ -> smt_fragment env frag

and smt_fragment env frag =
  match frag with
  | F_id (Name (id, _) as ssa_id) ->
     begin match Type_check.Env.lookup_id id env with
     | Enum _ -> Var (zencode_id id)
     | _ -> Var (zencode_name ssa_id)
     end
  | F_id ssa_id -> Var (zencode_name ssa_id)
  | F_op (frag1, "!=", frag2) ->
     Fn ("not", [Fn ("=", [smt_fragment env frag1; smt_fragment env frag2])])
  | F_unary ("!", frag) ->
     Fn ("not", [smt_cval env (frag, CT_bool)])
  | F_ctor_kind (union, ctor_id, unifiers, _) ->
     Fn ("not", [Tester (zencode_ctor ctor_id unifiers, smt_fragment env union)])
  | F_ctor_unwrap (ctor_id, unifiers, union) ->
     Fn ("un" ^ zencode_ctor ctor_id unifiers, [smt_fragment env union])
  | F_field (union, field) ->
     Fn ("un" ^ field, [smt_fragment env union])
  | F_tuple_member (frag, len, n) ->
     Fn (Printf.sprintf "tup_%d_%d" len n, [smt_fragment env frag])
  | frag -> failwith ("Unrecognised fragment " ^ string_of_fragment ~zencode:false frag)

let builtin_zeros env cval = function
  | CT_fbits (n, _) -> bvzero n
  | CT_lbits _ -> Fn ("Bits", [extract (!lbits_index - 1) 0 (smt_cval env cval); bvzero (lbits_size ())])
  | _ -> failwith "Cannot compile zeros"

let builtin_zero_extend env vbits vlen ret_ctyp =
  match cval_ctyp vbits, ret_ctyp with
  | CT_fbits (n, _), CT_fbits (m, _) when n = m ->
     smt_cval env vbits
  | CT_fbits (n, _), CT_fbits (m, _) ->
     let bv = smt_cval env vbits in
     Fn ("concat", [bvzero (m - n); bv])
  | _ -> failwith "Cannot compile zero_extend"

let builtin_sign_extend env vbits vlen ret_ctyp =
  match cval_ctyp vbits, ret_ctyp with
  | CT_fbits (n, _), CT_fbits (m, _) when n = m ->
     smt_cval env vbits
  | CT_fbits (n, _), CT_fbits (m, _) ->
     let bv = smt_cval env vbits in
     let top_bit_one = Fn ("=", [Extract (n - 1, n - 1, bv); Bin "1"]) in
     Ite (top_bit_one, Fn ("concat", [bvones (m - n); bv]), Fn ("concat", [bvzero (m - n); bv]))
  | _ -> failwith "Cannot compile zero_extend"

let int_size = function
  | CT_constant n -> required_width n
  | CT_fint sz -> sz
  | CT_lint -> lbits_size ()
  | _ -> failwith "Argument to int_size must be an integer"

(* [bvzeint esz cval] (BitVector Zero Extend INTeger), takes a cval
   which must be an integer type (either CT_fint, or CT_lint), and
   produces a bitvector which is either zero extended or truncated to
   exactly esz bits. *)
let bvzeint env esz cval =
  let sz = int_size (cval_ctyp cval) in
  match fst cval with
  | F_lit (V_int n) ->
     bvint esz (Big_int.to_int n)
  | _ ->
     let smt = smt_cval env cval in
     if esz = sz then
       smt
     else if esz > sz then
       Fn ("concat", [bvzero (esz - sz); smt])
     else
       Extract (esz - 1, 0, smt)

let builtin_shift shiftop env vbits vshift ret_ctyp =
  match cval_ctyp vbits with
  | CT_fbits (n, _) ->
     let bv = smt_cval env vbits in
     let len = bvzeint env n vshift in
     Fn (shiftop, [bv; len])

  | CT_lbits _ ->
     let bv = smt_cval env vbits in
     let shift = bvzeint env (lbits_size ()) vshift in
     Fn ("Bits", [Fn ("len", [bv]); Fn (shiftop, [Fn ("contents", [bv]); shift])])

  | _ -> failwith ("Cannot compile shift: " ^ shiftop)

let builtin_or_bits env v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2 with
  | CT_fbits (n, _), CT_fbits (m, _) ->
     assert (n = m);
     let smt1 = smt_cval env v1 in
     let smt2 = smt_cval env v2 in
     bvor smt1 smt2

  | CT_lbits _, CT_lbits _ ->
     let smt1 = smt_cval env v1 in
     let smt2 = smt_cval env v2 in
     Fn ("Bits", [Fn ("len", [smt1]); bvor (Fn ("contents", [smt1])) (Fn ("contents", [smt2]))])

  | _ -> failwith "Cannot compile or_bits"

let builtin_append env v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | CT_fbits (n, _), CT_fbits (m, _), CT_fbits (o, _) ->
     assert (n + m = o);
     let smt1 = smt_cval env v1 in
     let smt2 = smt_cval env v2 in
     Fn ("concat", [smt1; smt2])

  | CT_fbits (n, _), CT_lbits _, CT_lbits _ ->
     let smt1 = smt_cval env v1 in
     let smt2 = smt_cval env v2 in
     let x = Fn ("concat", [bvzero (lbits_size () - n); smt1]) in
     let shift = Fn ("concat", [bvzero (lbits_size () - !lbits_index); Fn ("len", [smt2])]) in
     Fn ("Bits", [bvadd (bvint !lbits_index n) (Fn ("len", [smt2])); bvor (bvshl x shift) (Fn ("contents", [smt2]))])

  | CT_lbits _, CT_lbits _, CT_lbits _ ->
     let smt1 = smt_cval env v1 in
     let smt2 = smt_cval env v2 in
     let x = Fn ("contents", [smt1]) in
     let shift = Fn ("concat", [bvzero (lbits_size () - !lbits_index); Fn ("len", [smt2])]) in
     Fn ("Bits", [bvadd (Fn ("len", [smt1])) (Fn ("len", [smt2])); bvor (bvshl x shift) (Fn ("contents", [smt2]))])

  | _ -> failwith "Cannot compile append"

let builtin_length env v ret_ctyp =
  match cval_ctyp v, ret_ctyp with
  | CT_lbits _, CT_fint m ->
     let sz = !lbits_index in
     let len = Fn ("len", [smt_cval env v]) in
     if m = sz then
       len
     else if m > sz then
       Fn ("concat", [bvzero (m - sz); len])
     else
       Extract (m - 1, 0, len)

  | _, _ -> failwith "Cannot compile length"

let builtin_vector_subrange env vec i j ret_ctyp =
  match cval_ctyp vec, cval_ctyp i, cval_ctyp j with
  | CT_fbits (n, _), CT_constant i, CT_constant j ->
     Extract (Big_int.to_int i, Big_int.to_int j, smt_cval env vec)

  | _ -> failwith "Cannot compile vector subrange"

let builtin_vector_access env vec i ret_ctyp =
  match cval_ctyp vec, cval_ctyp i, ret_ctyp with
  | CT_fbits (n, _), CT_constant i, CT_bit ->
     Extract (Big_int.to_int i, Big_int.to_int i, smt_cval env vec)

  | _ -> failwith "Cannot compile vector subrange"

let builtin_unsigned env v ret_ctyp =
  match cval_ctyp v, ret_ctyp with
  | CT_fbits (n, _), CT_fint m ->
     let smt = smt_cval env v in
     Fn ("concat", [bvzero (m - n); smt])

  | _ -> failwith "Cannot compile unsigned"

let builtin_eq_int env v1 v2 =
  match cval_ctyp v1, cval_ctyp v2 with
  | CT_fint m, CT_constant c ->
     Fn ("=", [smt_cval env v1; bvint m (Big_int.to_int c)])

  | _ -> failwith "Cannot compile eq_int"

let builtin_add_bits env v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | CT_fbits (n, _), CT_fbits (m, _), CT_fbits (o, _) ->
     assert (n = m && m = o);
     Fn ("bvadd", [smt_cval env v1; smt_cval env v2])

  | _ -> failwith "Cannot compile add_bits"

let smt_primop env name args ret_ctyp =
  match name, args, ret_ctyp with
  | "eq_bits", [v1; v2], _ ->
     let smt1 = smt_cval env v1 in
     let smt2 = smt_cval env v2 in
     Fn ("=", [smt1; smt2])
  | "eq_bit", [v1; v2], _ ->
     let smt1 = smt_cval env v1 in
     let smt2 = smt_cval env v2 in
     Fn ("=", [smt1; smt2])

  | "not", [v], _ -> Fn ("not", [smt_cval env v])

  | "zeros", [v1], _ -> builtin_zeros env v1 ret_ctyp
  | "zero_extend", [v1; v2], _ -> builtin_zero_extend env v1 v2 ret_ctyp
  | "sign_extend", [v1; v2], _ -> builtin_sign_extend env v1 v2 ret_ctyp
  | "shiftl", [v1; v2], _ -> builtin_shift "bvshl" env v1 v2 ret_ctyp
  | "shiftr", [v1; v2], _ -> builtin_shift "bvlshr" env v1 v2 ret_ctyp
  | "or_bits", [v1; v2], _ -> builtin_or_bits env v1 v2 ret_ctyp
  | "add_bits", [v1; v2], _ -> builtin_add_bits env v1 v2 ret_ctyp
  | "append", [v1; v2], _ -> builtin_append env v1 v2 ret_ctyp
  | "length", [v], ret_ctyp -> builtin_length env v ret_ctyp
  | "vector_access", [v1; v2], ret_ctyp -> builtin_vector_access env v1 v2 ret_ctyp
  | "vector_subrange", [v1; v2; v3], ret_ctyp -> builtin_vector_subrange env v1 v2 v3 ret_ctyp
  | "sail_unsigned", [v], ret_ctyp -> builtin_unsigned env v ret_ctyp
  | "eq_int", [v1; v2], _ -> builtin_eq_int env v1 v2

  | _ -> failwith ("Bad primop " ^ name ^ " " ^ Util.string_of_list ", " string_of_ctyp (List.map snd args) ^ " -> " ^ string_of_ctyp ret_ctyp)

let rec smt_conversion from_ctyp to_ctyp x =
  match from_ctyp, to_ctyp with
  | _, _ when ctyp_equal from_ctyp to_ctyp -> x
  | _, _ -> failwith "Bad conversion"

let define_const id ctyp exp = Define_const (zencode_name id, smt_ctyp ctyp, exp)
let declare_const id ctyp = Declare_const (zencode_name id, smt_ctyp ctyp)

let smt_ctype_def = function
  | CTD_enum (id, elems) ->
     [declare_datatypes (mk_enum (zencode_upper_id id) (List.map zencode_id elems))]

  | CTD_struct (id, fields) ->
     [declare_datatypes
       (mk_record (zencode_upper_id id)
          (List.map (fun (field, ctyp) -> zencode_id field, smt_ctyp ctyp) fields))]

  | CTD_variant (id, ctors) ->
     [declare_datatypes
       (mk_variant (zencode_upper_id id)
         (List.map (fun (ctor, ctyp) -> zencode_id ctor, smt_ctyp ctyp) ctors))]

let rec generate_ctype_defs = function
  | CDEF_type ctd :: cdefs -> smt_ctype_def ctd :: generate_ctype_defs cdefs
  | _ :: cdefs -> generate_ctype_defs cdefs
  | [] -> []

let rec generate_reg_decs inits = function
  | CDEF_reg_dec (id, ctyp, _) :: cdefs when not (NameMap.mem (Name (id, 0)) inits)->
     Declare_const (zencode_name (Name (id, 0)), smt_ctyp ctyp)
     :: generate_reg_decs inits cdefs
  | _ :: cdefs -> generate_reg_decs inits cdefs
  | [] -> []

(**************************************************************************)
(* 2. Converting sail types to Jib types for SMT                          *)
(**************************************************************************)

let max_int n = Big_int.pred (Big_int.pow_int_positive 2 (n - 1))
let min_int n = Big_int.negate (Big_int.pow_int_positive 2 (n - 1))

(** Convert a sail type into a C-type. This function can be quite
   slow, because it uses ctx.local_env and SMT to analyse the Sail
   types and attempts to fit them into the smallest possible C
   types, provided ctx.optimize_smt is true (default) **)
let rec ctyp_of_typ ctx typ =
  let open Ast in
  let open Type_check in
  let open Jib_compile in
  let Typ_aux (typ_aux, l) as typ = Env.expand_synonyms ctx.tc_env typ in
  match typ_aux with
  | Typ_id id when string_of_id id = "bit"    -> CT_bit
  | Typ_id id when string_of_id id = "bool"   -> CT_bool
  | Typ_id id when string_of_id id = "int"    -> CT_lint
  | Typ_id id when string_of_id id = "nat"    -> CT_lint
  | Typ_id id when string_of_id id = "unit"   -> CT_unit
  | Typ_id id when string_of_id id = "string" -> CT_string
  | Typ_id id when string_of_id id = "real"   -> CT_real

  | Typ_app (id, _) when string_of_id id = "atom_bool" -> CT_bool

  | Typ_app (id, args) when string_of_id id = "itself" ->
     ctyp_of_typ ctx (Typ_aux (Typ_app (mk_id "atom", args), l))
  | Typ_app (id, _) when string_of_id id = "range" || string_of_id id = "atom" || string_of_id id = "implicit" ->
     begin match destruct_range Env.empty typ with
     | None -> assert false (* Checked if range type in guard *)
     | Some (kids, constr, n, m) ->
        let ctx = { ctx with local_env = add_existential Parse_ast.Unknown (List.map (mk_kopt K_int) kids) constr ctx.local_env } in
        match nexp_simp n, nexp_simp m with
        | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
             when n = m ->
           CT_constant n
        | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
             when Big_int.less_equal (min_int 64) n && Big_int.less_equal m (max_int 64) ->
           CT_fint 64
        | n, m ->
           if prove __POS__ ctx.local_env (nc_lteq (nconstant (min_int 64)) n) && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_int 64))) then
             CT_fint 64
           else
             CT_lint
     end

  | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "list" ->
     CT_list (ctyp_of_typ ctx typ)

  (* When converting a sail bitvector type into C, we have three options in order of efficiency:
     - If the length is obviously static and smaller than 64, use the fixed bits type (aka uint64_t), fbits.
     - If the length is less than 64, then use a small bits type, sbits.
     - If the length may be larger than 64, use a large bits type lbits. *)
  | Typ_app (id, [A_aux (A_nexp n, _);
                  A_aux (A_order ord, _);
                  A_aux (A_typ (Typ_aux (Typ_id vtyp_id, _)), _)])
       when string_of_id id = "vector" && string_of_id vtyp_id = "bit" ->
     let direction = match ord with Ord_aux (Ord_dec, _) -> true | Ord_aux (Ord_inc, _) -> false | _ -> assert false in
     begin match nexp_simp n with
     | Nexp_aux (Nexp_constant n, _) -> CT_fbits (Big_int.to_int n, direction)
     | _ -> CT_lbits direction
     end

  | Typ_app (id, [A_aux (A_nexp n, _);
                  A_aux (A_order ord, _);
                  A_aux (A_typ typ, _)])
       when string_of_id id = "vector" ->
     let direction = match ord with Ord_aux (Ord_dec, _) -> true | Ord_aux (Ord_inc, _) -> false | _ -> assert false in
     CT_vector (direction, ctyp_of_typ ctx typ)

  | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "register" ->
     CT_ref (ctyp_of_typ ctx typ)

  | Typ_id id | Typ_app (id, _) when Bindings.mem id ctx.records  -> CT_struct (id, Bindings.find id ctx.records |> Bindings.bindings)
  | Typ_id id | Typ_app (id, _) when Bindings.mem id ctx.variants -> CT_variant (id, Bindings.find id ctx.variants |> Bindings.bindings)
  | Typ_id id when Bindings.mem id ctx.enums -> CT_enum (id, Bindings.find id ctx.enums |> IdSet.elements)

  | Typ_tup typs -> CT_tup (List.map (ctyp_of_typ ctx) typs)

  | Typ_exist _ ->
     (* Use Type_check.destruct_exist when optimising with SMT, to
        ensure that we don't cause any type variable clashes in
        local_env, and that we can optimize the existential based upon
        it's constraints. *)
     begin match destruct_exist (Env.expand_synonyms ctx.local_env typ) with
     | Some (kids, nc, typ) ->
        let env = add_existential l kids nc ctx.local_env in
        ctyp_of_typ { ctx with local_env = env } typ
     | None -> raise (Reporting.err_unreachable l __POS__ "Existential cannot be destructured!")
     end

  | Typ_var kid -> CT_poly

  | _ -> raise (Reporting.err_unreachable l __POS__ ("No C type for type " ^ string_of_typ typ))

(**************************************************************************)
(* 3. Optimization of primitives and literals                             *)
(**************************************************************************)

let hex_char =
  let open Sail2_values in
  function
  | '0' -> [B0; B0; B0; B0]
  | '1' -> [B0; B0; B0; B1]
  | '2' -> [B0; B0; B1; B0]
  | '3' -> [B0; B0; B1; B1]
  | '4' -> [B0; B1; B0; B0]
  | '5' -> [B0; B1; B0; B1]
  | '6' -> [B0; B1; B1; B0]
  | '7' -> [B0; B1; B1; B1]
  | '8' -> [B1; B0; B0; B0]
  | '9' -> [B1; B0; B0; B1]
  | 'A' | 'a' -> [B1; B0; B1; B0]
  | 'B' | 'b' -> [B1; B0; B1; B1]
  | 'C' | 'c' -> [B1; B1; B0; B0]
  | 'D' | 'd' -> [B1; B1; B0; B1]
  | 'E' | 'e' -> [B1; B1; B1; B0]
  | 'F' | 'f' -> [B1; B1; B1; B1]
  | _ -> failwith "Invalid hex character"

let literal_to_fragment (L_aux (l_aux, _) as lit) =
  match l_aux with
  | L_num n -> Some (F_lit (V_int n), CT_constant n)
  | L_hex str when String.length str <= 16 ->
     let content = Util.string_to_list str |> List.map hex_char |> List.concat in
     Some (F_lit (V_bits content), CT_fbits (String.length str * 4, true))
  | L_unit -> Some (F_lit V_unit, CT_unit)
  | L_true -> Some (F_lit (V_bool true), CT_bool)
  | L_false -> Some (F_lit (V_bool false), CT_bool)
  | _ -> None

let c_literals ctx =
  let rec c_literal env l = function
    | AV_lit (lit, typ) as v ->
       begin match literal_to_fragment lit with
       | Some (frag, ctyp) -> AV_C_fragment (frag, typ, ctyp)
       | None -> v
       end
    | AV_tuple avals -> AV_tuple (List.map (c_literal env l) avals)
    | v -> v
  in
  map_aval c_literal

(**************************************************************************)
(* 3. Generating SMT                                                      *)
(**************************************************************************)

(* When generating SMT when we encounter joins between two or more
   blocks such as in the example below, we have to generate a muxer
   that chooses the correct value of v_n or v_m to assign to v_o. We
   use the pi nodes that contain the global path condition for each
   block to generate an if-then-else for each phi function. The order
   of the arguments to each phi function is based on the graph node
   index for the predecessor nodes.

   +---------------+      +---------------+
   | pi(cond_1)    |      | pi(cond_2)    |
   | ...           |      | ...           |
   | Basic block 1 |      | Basic block 2 |
   +---------------+      +---------------+
              \               /
               \             /
            +---------------------+
            | v/o = phi(v/n, v/m) |
            | ...                 |
            +---------------------+

   would generate:

   (define-const v/o (ite cond_1 v/n v/m_))
*)
let smt_ssanode env cfg preds =
  let open Jib_ssa in
  function
  | Pi _ -> []
  | Phi (id, ctyp, ids) ->
     let get_pi n =
       match get_vertex cfg n with
       | Some ((ssanodes, _), _, _) ->
          List.concat (List.map (function Pi guards -> guards | _ -> []) ssanodes)
       | None -> failwith "Predecessor node does not exist"
     in
     let pis = List.map get_pi (IntSet.elements preds) in
     let mux =
       List.fold_right2 (fun pi id chain ->
           let pathcond =
             match pi with
             | [cval] -> smt_cval env cval
             | _ -> Fn ("and", List.map (smt_cval env) pi)
           in
           match chain with
           | Some smt ->
              Some (Ite (pathcond, Var (zencode_name id), smt))
           | None ->
              Some (Var (zencode_name id)))
         pis ids None
     in
     match mux with
     | None -> []
     | Some mux ->
        [Define_const (zencode_name id, smt_ctyp ctyp, mux)]

(* For any complex l-expression we need to turn it into a
   read-modify-write in the SMT solver. The SSA transform turns CL_id
   nodes into CL_rmw (read, write, ctyp) nodes when CL_id is wrapped
   in any other l-expression. The read and write must have the same
   name but different SSA numbers.
*)
let rec rmw_write = function
  | CL_rmw (_, write, ctyp) -> write, ctyp
  | CL_id _ -> assert false
  | CL_tuple (clexp, _) -> rmw_write clexp
  | clexp ->
     failwith (Pretty_print_sail.to_string (pp_clexp clexp))

let rmw_read = function
  | CL_rmw (read, _, _) -> zencode_name read
  | _ -> assert false

let rmw_modify smt = function
  | CL_tuple (clexp, n) ->
     let ctyp = clexp_ctyp clexp in
     begin match ctyp with
     | CT_tup ctyps ->
        let len = List.length ctyps in
        let set_tup i =
          if i == n then
            smt
          else
            Fn (Printf.sprintf "tup_%d_%d" len i, [Var (rmw_read clexp)])
        in
        Fn ("tup4", List.init len set_tup)
     | _ ->
        failwith "Tuple modify does not have tuple type"
     end
  | _ -> assert false

(* For a basic block (contained in a control-flow node / cfnode), we
   turn the instructions into a sequence of define-const and
   declare-const expressions. Because we are working with a SSA graph,
   each variable is guaranteed to only be declared once.
*)
let smt_instr env =
  let open Type_check in
  function
  | I_aux (I_funcall (CL_id (id, ret_ctyp), _, function_id, args), _) ->
     if Env.is_extern function_id env "c" then
       let name = Env.get_extern function_id env "c" in
       let value = smt_primop env name args ret_ctyp in
       [define_const id ret_ctyp value]
     else
       let smt_args = List.map (smt_cval env) args in
       [define_const id ret_ctyp (Fn (zencode_id function_id, smt_args))]

  | I_aux (I_init (ctyp, id, cval), _) | I_aux (I_copy (CL_id (id, ctyp), cval), _) ->
     [define_const id ctyp
        (smt_conversion (cval_ctyp cval) ctyp (smt_cval env cval))]

  | I_aux (I_copy (clexp, cval), _) ->
     let smt = smt_cval env cval in
     let write, ctyp = rmw_write clexp in
     [define_const write ctyp (rmw_modify smt clexp)]

  | I_aux (I_decl (ctyp, id), _) ->
     [declare_const id ctyp]

  | I_aux (I_end id, _) ->
     [Assert (Var (zencode_name id))]

  | I_aux (I_clear _, _) -> []

  | I_aux (I_match_failure, _) -> []

  | instr ->
     failwith ("Cannot translate: " ^ Pretty_print_sail.to_string (pp_instr instr))

let smt_cfnode all_cdefs env =
  let open Jib_ssa in
  function
  | CF_start inits ->
     let smt_reg_decs = generate_reg_decs inits all_cdefs in
     let smt_start (id, ctyp) =
       match id with
       | Have_exception _ -> define_const id ctyp (Bool_lit false)
       | _ -> declare_const id ctyp
     in
     smt_reg_decs @ List.map smt_start (NameMap.bindings inits)
  | CF_block instrs ->
     List.concat (List.map (smt_instr env) instrs)
  (* We can ignore any non basic-block/start control-flow nodes *)
  | _ -> []

let rec find_function id = function
  | CDEF_fundef (id', heap_return, args, body) :: _ when Id.compare id id' = 0 ->
     Some (heap_return, args, body)
  | _ :: cdefs ->
     find_function id cdefs
  | [] -> None

let smt_cdef out_chan env all_cdefs = function
  | CDEF_spec (function_id, arg_ctyps, ret_ctyp)
       when string_of_id function_id = "check_sat" ->
     begin match find_function function_id all_cdefs with
     | Some (None, args, instrs) ->
        let open Jib_ssa in
        let smt_args =
          List.map2 (fun id ctyp -> declare_const (Name (id, 0)) ctyp) args arg_ctyps
        in
        output_smt_defs out_chan smt_args;

        let instrs =
          let open Jib_optimize in
          instrs
          (* |> optimize_unit *)
          |> inline all_cdefs (fun _ -> true)
          |> flatten_instrs
        in

        let str = Pretty_print_sail.to_string PPrint.(separate_map hardline Jib_util.pp_instr instrs) in
        prerr_endline str;

        let start, cfg = ssa instrs in
        let chan = open_out "smt_ssa.gv" in
        make_dot chan cfg;
        close_out chan;

        let visit_order = topsort cfg in

        List.iter (fun n ->
            begin match get_vertex cfg n with
            | None -> ()
            | Some ((ssanodes, cfnode), preds, succs) ->
               let muxers =
                 ssanodes |> List.map (smt_ssanode env cfg preds) |> List.concat
               in
               let basic_block = smt_cfnode all_cdefs env cfnode in
               output_smt_defs out_chan muxers;
               output_smt_defs out_chan basic_block;
            end
          ) visit_order

     | _ -> failwith "Bad function body"
     end
  | _ -> ()

let rec smt_cdefs out_chan env ast =
  function
  | cdef :: cdefs ->
     smt_cdef out_chan env ast cdef;
     smt_cdefs out_chan env ast cdefs
  | [] -> ()

let generate_smt out_chan env ast =
  try
    let open Jib_compile in
    let ctx =
      initial_ctx
        ~convert_typ:ctyp_of_typ
        ~optimize_anf:(fun ctx aexp -> c_literals ctx aexp)
        env
    in
    let t = Profile.start () in
    let cdefs, ctx = compile_ast { ctx with specialize_calls = true; ignore_64 = true } ast in
    Profile.finish "Compiling to Jib IR" t;

    (* output_string out_chan "(set-option :produce-models true)\n"; *)
    output_string out_chan "(set-logic QF_AUFBVDT)\n";
    output_smt_defs out_chan
      [declare_datatypes (mk_enum "Unit" ["unit"]);
       Declare_tuple 2;
       Declare_tuple 3;
       Declare_tuple 4;
       Declare_tuple 5;
       declare_datatypes (mk_record "Bits" [("len", Bitvec !lbits_index);
                                            ("contents", Bitvec (lbits_size ()))])

      ];

    let smt_type_defs = List.concat (generate_ctype_defs cdefs) in
    output_string out_chan "\n; Sail type definitions\n";
    output_smt_defs out_chan smt_type_defs;

    output_string out_chan "\n; Sail function\n";
    smt_cdefs out_chan env cdefs cdefs;
    output_string out_chan "(check-sat)\n"
  with
  | Type_check.Type_error (_, l, err) ->
     raise (Reporting.err_typ l (Type_error.string_of_type_error err));
