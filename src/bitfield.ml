
module Big_int = Nat_big_num

open Initial_check
open Ast
open Ast_util

let bitvec size order =
  Printf.sprintf "vector(%i, %s, bit)" size (string_of_order order)

let rec combine = function
  | [] -> Defs []
  | (Defs defs) :: ast ->
     let (Defs defs') = combine ast in
     Defs (defs @ defs')

let newtype name size order =
  let nt = Printf.sprintf "newtype %s = Mk_%s : %s" name name (bitvec size order) in
  ast_of_def_string order nt

let full_getter name size order =
  let fg_val = Printf.sprintf "val _get_%s : %s -> %s" name name (bitvec size order) in
  let fg_function = Printf.sprintf "function _get_%s Mk_%s(v) = v" name name in
  combine [ast_of_def_string order fg_val; ast_of_def_string order fg_function]

let full_setter name size order =
  let fs_val = Printf.sprintf "val _set_%s : (register(%s), %s) -> unit effect {wreg}" name name (bitvec size order) in
  let fs_function = String.concat "\n"
    [ Printf.sprintf "function _set_%s (r_ref, v) = {" name;
                     "  r = _reg_deref(r_ref);";
      Printf.sprintf "  r = Mk_%s(v);" name;
                     "  (*r_ref) = r";
                     "}"
    ]
  in
  combine [ast_of_def_string order fs_val; ast_of_def_string order fs_function]

let full_overload name order =
  ast_of_def_string order (Printf.sprintf "overload _mod_bits = {_get_%s, _set_%s}" name name)

let full_accessor name size order =
  combine [full_getter name size order; full_setter name size order; full_overload name order]

let index_range_getter' name field order start stop =
  let size = if start > stop then start - (stop - 1) else stop - (start - 1) in
  let irg_val = Printf.sprintf "val _get_%s : %s -> %s" field name (bitvec size order) in
  let irg_function = Printf.sprintf "function _get_%s Mk_%s(v) = v[%i .. %i]" field name start stop in
  combine [ast_of_def_string order irg_val; ast_of_def_string order irg_function]

let index_range_setter' name field order start stop =
  let size = if start > stop then start - (stop - 1) else stop - (start - 1) in
  let irs_val = Printf.sprintf "val _set_%s : (register(%s), %s) -> unit effect {wreg}" field name (bitvec size order) in
  let irs_function = String.concat "\n"
    [ Printf.sprintf "function _set_%s (r_ref, v) = {" field;
      Printf.sprintf "  r = _get_%s(_reg_deref(r_ref));" name;
      Printf.sprintf "  r[%i .. %i] = v;" start stop;
      Printf.sprintf "  (*r_ref) = Mk_%s(r)" name;
                     "}"
    ]
  in
  combine [ast_of_def_string order irs_val; ast_of_def_string order irs_function]

let index_range_overload field order =
  ast_of_def_string order (Printf.sprintf "overload _mod_%s = {_get_%s, _set_%s}" field field field)

let index_range_accessor name field order (BF_aux (bf_aux, l)) =
  let getter n m = index_range_getter' name field order (Big_int.to_int n) (Big_int.to_int m) in
  let setter n m = index_range_setter' name field order (Big_int.to_int n) (Big_int.to_int m) in
  let overload = index_range_overload field order in
  match bf_aux with
  | BF_single n -> combine [getter n n; setter n n; overload]
  | BF_range (n, m) -> combine [getter n m; setter n m; overload]
  | BF_concat _ -> failwith "Unimplemented"

let field_accessor name order (id, ir) = index_range_accessor name (string_of_id id) order ir

let macro id size order ranges =
  let name = string_of_id id in
  combine ([newtype name size order; full_accessor name size order] @ List.map (field_accessor name order) ranges)
