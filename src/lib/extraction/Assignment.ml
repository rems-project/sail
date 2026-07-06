open Ast
open Datatypes
open List0
open ListDef
open ListUtil
open TypeAnnot

(** val lexp_subexps : 'a1 lexp -> 'a1 exp list **)

let rec lexp_subexps = function
| LE_aux (aux, _) ->
  (match aux with
   | LE_deref x -> x :: []
   | LE_tuple ls -> concat (map lexp_subexps ls)
   | LE_vector_concat ls -> concat (map lexp_subexps ls)
   | LE_vector (l0, x) -> app (lexp_subexps l0) (x :: [])
   | LE_vector_range (l0, n, m) -> app (lexp_subexps l0) (n :: (m :: []))
   | LE_field (l0, _) -> lexp_subexps l0
   | _ -> [])

(** val update_lexp_subexps :
    'a1 exp list -> 'a1 lexp -> 'a1 lexp * 'a1 exp list **)

let rec update_lexp_subexps xs l = match l with
| LE_aux (aux, annot0) ->
  (match aux with
   | LE_deref _ ->
     (match xs with
      | [] -> (l, xs)
      | y :: ys -> ((LE_aux ((LE_deref y), annot0)), ys))
   | LE_tuple ls ->
     let (ls0, xs0) =
       fold_left (fun acc l0 ->
         let (ls0, xs0) = acc in
         let (l1, xs1) = update_lexp_subexps xs0 l0 in
         ((app ls0 (l1 :: [])), xs1)) ls ([], xs)
     in
     ((LE_aux ((LE_tuple ls0), annot0)), xs0)
   | LE_vector_concat ls ->
     let (ls0, xs0) =
       fold_left (fun acc l0 ->
         let (ls0, xs0) = acc in
         let (l1, xs1) = update_lexp_subexps xs0 l0 in
         ((app ls0 (l1 :: [])), xs1)) ls ([], xs)
     in
     ((LE_aux ((LE_vector_concat ls0), annot0)), xs0)
   | LE_vector (l0, _) ->
     let (l1, l2) = update_lexp_subexps xs l0 in
     (match l2 with
      | [] -> (l0, [])
      | n :: xs0 -> ((LE_aux ((LE_vector (l1, n)), annot0)), xs0))
   | LE_vector_range (l0, _, _) ->
     let (l1, l2) = update_lexp_subexps xs l0 in
     (match l2 with
      | [] -> (l0, [])
      | n :: l3 ->
        (match l3 with
         | [] -> (l0, [])
         | m :: xs0 -> ((LE_aux ((LE_vector_range (l1, n, m)), annot0)), xs0)))
   | LE_field (l0, f) ->
     let (l', ys) = update_lexp_subexps xs l0 in
     ((LE_aux ((LE_field (l', f)), annot0)), ys)
   | _ -> (l, xs))

type 'a zlexp_aux =
| LZ_id of id
| LZ_deref
| LZ_typ of typ * id
| LZ_tuple of 'a zlexp list
| LZ_vector_concat of 'a zlexp list
| LZ_vector of 'a zlexp
| LZ_vector_range of 'a zlexp
| LZ_field of 'a zlexp * id
and 'a zlexp =
| LZ_aux of 'a zlexp_aux * 'a annot

(** val lexp_to_z : 'a1 lexp -> 'a1 zlexp **)

let rec lexp_to_z = function
| LE_aux (aux, ann) ->
  (match aux with
   | LE_id id0 -> LZ_aux ((LZ_id id0), ann)
   | LE_deref _ -> LZ_aux (LZ_deref, ann)
   | LE_typ (typ0, id0) -> LZ_aux ((LZ_typ (typ0, id0)), ann)
   | LE_tuple ls -> LZ_aux ((LZ_tuple (map lexp_to_z ls)), ann)
   | LE_vector_concat ls ->
     LZ_aux ((LZ_vector_concat (map lexp_to_z ls)), ann)
   | LE_vector (l0, _) -> LZ_aux ((LZ_vector (lexp_to_z l0)), ann)
   | LE_vector_range (l0, _, _) ->
     LZ_aux ((LZ_vector_range (lexp_to_z l0)), ann)
   | LE_field (l0, f) -> LZ_aux ((LZ_field ((lexp_to_z l0), f)), ann))

(** val update_zlexp_subexps :
    'a1 exp list -> 'a1 zlexp -> 'a1 lexp option * 'a1 exp list **)

let rec update_zlexp_subexps xs = function
| LZ_aux (aux, annot0) ->
  (match aux with
   | LZ_id id0 -> ((Some (LE_aux ((LE_id id0), annot0))), xs)
   | LZ_deref ->
     (match xs with
      | [] -> (None, xs)
      | y :: ys -> ((Some (LE_aux ((LE_deref y), annot0))), ys))
   | LZ_typ (typ0, id0) ->
     ((Some (LE_aux ((LE_typ (typ0, id0)), annot0))), xs)
   | LZ_tuple ls ->
     let (o, xs0) =
       fold_left (consume update_zlexp_subexps) ls ((Some []), xs)
     in
     (match o with
      | Some ls0 -> ((Some (LE_aux ((LE_tuple (rev ls0)), annot0))), xs0)
      | None -> (None, xs0))
   | LZ_vector_concat ls ->
     let (o, xs0) =
       fold_left (consume update_zlexp_subexps) ls ((Some []), xs)
     in
     (match o with
      | Some ls0 ->
        ((Some (LE_aux ((LE_vector_concat (rev ls0)), annot0))), xs0)
      | None -> (None, xs0))
   | LZ_vector l0 ->
     let (o, l1) = update_zlexp_subexps xs l0 in
     (match o with
      | Some l2 ->
        (match l1 with
         | [] -> (None, [])
         | n :: xs0 -> ((Some (LE_aux ((LE_vector (l2, n)), annot0))), xs0))
      | None -> (None, []))
   | LZ_vector_range l0 ->
     let (o, l1) = update_zlexp_subexps xs l0 in
     (match o with
      | Some l2 ->
        (match l1 with
         | [] -> (None, [])
         | n :: l3 ->
           (match l3 with
            | [] -> (None, [])
            | m :: xs0 ->
              ((Some (LE_aux ((LE_vector_range (l2, n, m)), annot0))), xs0)))
      | None -> (None, []))
   | LZ_field (l0, fld) ->
     let (o, xs') = update_zlexp_subexps xs l0 in
     (match o with
      | Some l' -> ((Some (LE_aux ((LE_field (l', fld)), annot0))), xs')
      | None -> (None, xs')))

type var_type =
| Var_local
| Var_register

type 'v place =
| PL_id of id * var_type
| PL_register of 'v
| PL_vector of 'v place * 'v
| PL_vector_range of 'v place * 'v * 'v
| PL_field of 'v place * id

type 'v destructure =
| DL_tuple of 'v destructure list
| DL_vector_concat of (Types.vector_concat_split * 'v destructure) list
| DL_place of 'v place

module Typed =
 functor (Tannot:S) ->
 struct
  (** val zlexp_to_destructure :
      'a1 list -> Tannot.t zlexp -> 'a1 destructure option * 'a1 list **)

  let rec zlexp_to_destructure xs = function
  | LZ_aux (aux, annot0) ->
    (match aux with
     | LZ_id var ->
       (match Tannot.get_id_type (snd annot0) var with
        | Types.Local_variable ->
          ((Some (DL_place (PL_id (var, Var_local)))), xs)
        | Types.Global_register ->
          ((Some (DL_place (PL_id (var, Var_register)))), xs)
        | Types.Enum_member -> (None, xs))
     | LZ_deref ->
       (match xs with
        | [] -> (None, [])
        | x :: xs' -> ((Some (DL_place (PL_register x))), xs'))
     | LZ_typ (_, var) ->
       (match Tannot.get_id_type (snd annot0) var with
        | Types.Local_variable ->
          ((Some (DL_place (PL_id (var, Var_local)))), xs)
        | Types.Global_register ->
          ((Some (DL_place (PL_id (var, Var_register)))), xs)
        | Types.Enum_member -> (None, xs))
     | LZ_tuple ls ->
       let (o, xs0) =
         fold_left (consume zlexp_to_destructure) ls ((Some []), xs)
       in
       (match o with
        | Some ds -> ((Some (DL_tuple (rev ds))), xs0)
        | None -> (None, xs0))
     | LZ_vector_concat ls ->
       let widths =
         map (fun pat ->
           let LZ_aux (_, annot1) = pat in Tannot.get_split (snd annot1)) ls
       in
       let (o, xs0) =
         fold_left (consume zlexp_to_destructure) ls ((Some []), xs)
       in
       (match o with
        | Some ds ->
          ((Some (DL_vector_concat (combine widths (rev ds)))), xs0)
        | None -> (None, xs0))
     | LZ_vector l0 ->
       let (o, l1) = zlexp_to_destructure xs l0 in
       (match o with
        | Some d ->
          (match d with
           | DL_place p ->
             (match l1 with
              | [] -> (None, [])
              | n :: xs0 -> ((Some (DL_place (PL_vector (p, n)))), xs0))
           | _ -> (None, []))
        | None -> (None, []))
     | LZ_vector_range l0 ->
       let (o, l1) = zlexp_to_destructure xs l0 in
       (match o with
        | Some d ->
          (match d with
           | DL_place p ->
             (match l1 with
              | [] -> (None, [])
              | n :: l2 ->
                (match l2 with
                 | [] -> (None, [])
                 | m :: xs0 ->
                   ((Some (DL_place (PL_vector_range (p, n, m)))), xs0)))
           | _ -> (None, []))
        | None -> (None, []))
     | LZ_field (l0, fld) ->
       let (o, xs0) = zlexp_to_destructure xs l0 in
       (match o with
        | Some d ->
          (match d with
           | DL_place p -> ((Some (DL_place (PL_field (p, fld)))), xs0)
           | _ -> (None, []))
        | None -> (None, [])))
 end
