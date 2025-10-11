open Ascii
open Datatypes

(** val compare : string -> string -> comparison **)

let rec compare s1 s2 =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ ->
    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

      (fun _ -> Eq)
      (fun _ _ -> Lt)
      s2)
    (fun c1 s1' ->
    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

      (fun _ -> Gt)
      (fun c2 s2' ->
      match Ascii.compare c1 c2 with
      | Eq -> compare s1' s2'
      | x -> x)
      s2)
    s1

(** val ltb : string -> string -> bool **)

let ltb s1 s2 =
  match compare s1 s2 with
  | Lt -> true
  | _ -> false
