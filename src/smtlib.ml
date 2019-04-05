
type smt_typ =
  | Bitvec of int
  | Bool
  | Datatype of string * (string * (string * smt_typ) list) list
  | Tuple of smt_typ list
  | Array of smt_typ * smt_typ

let rec smt_typ_equal t1 t2 =
  match t1, t2 with
  | Bitvec n, Bitvec m -> n = m
  | Bool, Bool -> true
  | Datatype (name1, ctors1), Datatype (name2, ctors2) ->
     let field_equal (field_name1, typ1) (field_name2, typ2) =
       field_name1 = field_name2 && smt_typ_equal typ1 typ2
     in
     let ctor_equal (ctor_name1, fields1) (ctor_name2, fields2) =
       ctor_name1 = ctor_name2
       && List.length fields1 = List.length fields2
       && List.for_all2 field_equal fields1 fields2
     in
     name1 = name2
     && List.length ctors1 = List.length ctors2
     && List.for_all2 ctor_equal ctors1 ctors2
  | _, _ -> false

let mk_enum name elems =
  Datatype (name, List.map (fun elem -> (elem, [])) elems)

let mk_record name fields =
  Datatype (name, [(name, fields)])

let mk_variant name ctors =
  Datatype (name, List.map (fun (ctor, ty) -> (ctor, [("un" ^ ctor, ty)])) ctors)

type smt_exp =
  | Bool_lit of bool
  | Hex of string
  | Bin of string
  | Var of string
  | Fn of string * smt_exp list
  | Ite of smt_exp * smt_exp * smt_exp
  | Extract of int * int * smt_exp
  | Tester of string * smt_exp

let extract i j x = Extract (i, j, x)

let bvnot x    = Fn ("bvnot", [x])
let bvand x y  = Fn ("bvand", [x; y])
let bvor x y   = Fn ("bvor", [x; y])
let bvneg x    = Fn ("bvneg", [x])
let bvadd x y  = Fn ("bvadd", [x; y])
let bvmul x y  = Fn ("bvmul", [x; y])
let bvudiv x y = Fn ("bvudiv", [x; y])
let bvurem x y = Fn ("bvurem", [x; y])
let bvshl x y  = Fn ("bvshl", [x; y])
let bvlshr x y = Fn ("bvlshr", [x; y])
let bvult x y  = Fn ("bvult", [x; y])

let bvzero n =
  if n mod 4 = 0 then
    Hex (String.concat "" (Util.list_init (n / 4) (fun _ -> "0")))
  else
    Bin (String.concat "" (Util.list_init n (fun _ -> "0")))

let bvones n =
  if n mod 4 = 0 then
    Hex (String.concat "" (Util.list_init (n / 4) (fun _ -> "F")))
  else
    Bin (String.concat "" (Util.list_init n (fun _ -> "1")))

type smt_def =
  | Define_fun of string * (string * smt_typ) list * smt_typ * smt_exp
  | Declare_const of string * smt_typ
  | Define_const of string * smt_typ * smt_exp
  | Declare_datatypes of string * (string * (string * smt_typ) list) list
  | Declare_tuple of int
  | Assert of smt_exp

let declare_datatypes = function
  | Datatype (name, ctors) -> Declare_datatypes (name, ctors)
  | _ -> assert false

let pp_sfun str docs =
  let open PPrint in
  parens (separate space (string str :: docs))

let rec pp_smt_exp =
  let open PPrint in
  function
  | Bool_lit b -> string (string_of_bool b)
  | Hex str -> string ("#x" ^ str)
  | Bin str -> string ("#b" ^ str)
  | Var str -> string str
  | Fn (str, exps) -> parens (string str ^^ space ^^ separate_map space pp_smt_exp exps)
  | Ite (cond, then_exp, else_exp) ->
     parens (separate space [string "ite"; pp_smt_exp cond; pp_smt_exp then_exp; pp_smt_exp else_exp])
  | Extract (i, j, exp) ->
     parens (string (Printf.sprintf "(_ extract %d %d)" i j) ^^ space ^^ pp_smt_exp exp)
  | Tester (kind, exp) ->
     parens (string (Printf.sprintf "(_ is %s)" kind) ^^ space ^^ pp_smt_exp exp)

let rec pp_smt_typ =
  let open PPrint in
  function
  | Bool -> string "Bool"
  | Bitvec n -> string (Printf.sprintf "(_ BitVec %d)" n)
  | Datatype (name, _) -> string name
  | Tuple tys -> pp_sfun ("Tup" ^ string_of_int (List.length tys)) (List.map pp_smt_typ tys)
  | Array (ty1, ty2) -> pp_sfun "Array" [pp_smt_typ ty1; pp_smt_typ ty2]

let pp_str_smt_typ (str, ty) = let open PPrint in string str ^^ space ^^ pp_smt_typ ty

let pp_smt_def =
  let open PPrint in
  let open Printf in
  function
  | Define_fun (str, args, ty, exp) ->
     parens (string "define-fun"
             ^^ space ^^ parens (separate_map space pp_str_smt_typ args)
             ^^ space ^^ pp_smt_typ ty
             ^//^ pp_smt_exp exp)

  | Declare_const (name, ty) ->
     pp_sfun "declare-const" [string name; pp_smt_typ ty]

  | Define_const (name, ty, exp) ->
     pp_sfun "define-const" [string name; pp_smt_typ ty; pp_smt_exp exp]

  | Declare_datatypes (name, ctors) ->
     let pp_ctor (ctor_name, fields) =
       match fields with
       | [] -> parens (string ctor_name)
       | _ -> pp_sfun ctor_name (List.map (fun field -> parens (pp_str_smt_typ field)) fields)
     in
     pp_sfun "declare-datatypes"
       [Printf.ksprintf string "((%s 0))" name;
        parens (parens (separate_map space pp_ctor ctors))]

  | Declare_tuple n ->
     let par = separate_map space string (Util.list_init n (fun i -> "T" ^ string_of_int i)) in
     let fields = separate space (Util.list_init n (fun i -> Printf.ksprintf string "(tup_%d_%d T%d)" n i i)) in
     pp_sfun "declare-datatypes"
       [Printf.ksprintf string "((Tup%d %d))" n n;
        parens (parens (separate space
                          [string "par";
                           parens par;
                           parens (parens (ksprintf string "tup%d" n ^^ space ^^ fields))]))]

  | Assert exp ->
     pp_sfun "assert" [pp_smt_exp exp]

let string_of_smt_def def = Pretty_print_sail.to_string (pp_smt_def def)

let output_smt_defs out_chan smt =
  List.iter (fun def -> output_string out_chan (string_of_smt_def def ^ "\n")) smt
