(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* Modified by Scott Owens 2010-10-28 *)

(* $Id: set.ml 6694 2004-11-25 00:06:06Z doligez $ *)

(* Sets over ordered types *)

type 'a rep = Empty | Node of 'a rep * 'a * 'a rep * int

(* Sets are represented by balanced binary trees (the heights of the
 children differ by at most 2 *)

let height = function
    Empty -> 0
  | Node(_, _, _, h) -> h

(* Creates a new node with left son l, value v and right son r.
 We must have all elements of l < v < all elements of r.
 l and r must be balanced and | height l - height r | <= 2.
 Inline expansion of height for better speed. *)

let create l v r =
  let hl = match l with Empty -> 0 | Node(_,_,_,h) -> h in
  let hr = match r with Empty -> 0 | Node(_,_,_,h) -> h in
    Node(l, v, r, (if hl >= hr then hl + 1 else hr + 1))

(* Same as create, but performs one step of rebalancing if necessary.
 Assumes l and r balanced and | height l - height r | <= 3.
 Inline expansion of create for better speed in the most frequent case
 where no rebalancing is required. *)

let bal l v r =
  let hl = match l with Empty -> 0 | Node(_,_,_,h) -> h in
  let hr = match r with Empty -> 0 | Node(_,_,_,h) -> h in
    if hl > hr + 2 then begin
      match l with
          Empty -> invalid_arg "Set.bal"
        | Node(ll, lv, lr, _) ->
            if height ll >= height lr then
              create ll lv (create lr v r)
            else begin
              match lr with
                  Empty -> invalid_arg "Set.bal"
                | Node(lrl, lrv, lrr, _)->
                    create (create ll lv lrl) lrv (create lrr v r)
            end
    end else if hr > hl + 2 then begin
      match r with
          Empty -> invalid_arg "Set.bal"
        | Node(rl, rv, rr, _) ->
            if height rr >= height rl then
              create (create l v rl) rv rr
            else begin
              match rl with
                  Empty -> invalid_arg "Set.bal"
                | Node(rll, rlv, rlr, _) ->
                    create (create l v rll) rlv (create rlr rv rr)
            end
    end else
      Node(l, v, r, (if hl >= hr then hl + 1 else hr + 1))

(* Insertion of one element *)

let rec add cmp x = function
    Empty -> Node(Empty, x, Empty, 1)
  | Node(l, v, r, _) as t ->
      let c = cmp x v in
        if c = 0 then t else
          if c < 0 then bal (add cmp x l) v r else bal l v (add cmp x r)

(* Same as create and bal, but no assumptions are made on the
 relative heights of l and r. *)

let rec join cmp l v r =
  match (l, r) with
      (Empty, _) -> add cmp v r
    | (_, Empty) -> add cmp v l
    | (Node(ll, lv, lr, lh), Node(rl, rv, rr, rh)) ->
        if lh > rh + 2 then bal ll lv (join cmp lr v r) else
          if rh > lh + 2 then bal (join cmp l v rl) rv rr else
            create l v r

(* Smallest and greatest element of a set *)

let rec min_elt = function
    Empty -> raise Not_found
  | Node(Empty, v, r, _) -> v
  | Node(l, v, r, _) -> min_elt l

let rec max_elt = function
    Empty -> raise Not_found
  | Node(l, v, Empty, _) -> v
  | Node(l, v, r, _) -> max_elt r

(* Remove the smallest element of the given set *)

let rec remove_min_elt = function
    Empty -> invalid_arg "Set.remove_min_elt"
  | Node(Empty, v, r, _) -> r
  | Node(l, v, r, _) -> bal (remove_min_elt l) v r

(* Merge two trees l and r into one.
 All elements of l must precede the elements of r.
 Assume | height l - height r | <= 2. *)

let merge t1 t2 =
  match (t1, t2) with
      (Empty, t) -> t
    | (t, Empty) -> t
    | (_, _) -> bal t1 (min_elt t2) (remove_min_elt t2)

(* Merge two trees l and r into one.
 All elements of l must precede the elements of r.
 No assumption on the heights of l and r. *)

let concat cmp t1 t2 =
  match (t1, t2) with
      (Empty, t) -> t
    | (t, Empty) -> t
    | (_, _) -> join cmp t1 (min_elt t2) (remove_min_elt t2)

(* Splitting.  split x s returns a triple (l, present, r) where
 - l is the set of elements of s that are < x
 - r is the set of elements of s that are > x
 - present is false if s contains no element equal to x,
 or true if s contains an element equal to x. *)

let rec split cmp x = function
    Empty ->
      (Empty, false, Empty)
  | Node(l, v, r, _) ->
      let c = cmp x v in
        if c = 0 then (l, true, r)
        else if c < 0 then
          let (ll, pres, rl) = split cmp x l in (ll, pres, join cmp rl v r)
          else
            let (lr, pres, rr) = split cmp x r in (join cmp l v lr, pres, rr)

(* Implementation of the set operations *)

let empty = Empty

let is_empty = function Empty -> true | _ -> false

let rec mem cmp x = function
    Empty -> false
  | Node(l, v, r, _) ->
      let c = cmp x v in
        c = 0 || mem cmp x (if c < 0 then l else r)

let singleton x = Node(Empty, x, Empty, 1)

let rec remove cmp x = function
    Empty -> Empty
  | Node(l, v, r, _) ->
      let c = cmp x v in
        if c = 0 then merge l r else
          if c < 0 then bal (remove cmp x l) v r else bal l v (remove cmp x r)

let rec union cmp s1 s2 =
  match (s1, s2) with
      (Empty, t2) -> t2
    | (t1, Empty) -> t1
    | (Node(l1, v1, r1, h1), Node(l2, v2, r2, h2)) ->
        if h1 >= h2 then
          if h2 = 1 then add cmp v2 s1 else begin
            let (l2, _, r2) = split cmp v1 s2 in
              join cmp (union cmp l1 l2) v1 (union cmp r1 r2)
          end
        else
          if h1 = 1 then add cmp v1 s2 else begin
            let (l1, _, r1) = split cmp v2 s1 in
              join cmp (union cmp l1 l2) v2 (union cmp r1 r2)
          end

let rec inter cmp s1 s2 =
  match (s1, s2) with
      (Empty, t2) -> Empty
    | (t1, Empty) -> Empty
    | (Node(l1, v1, r1, _), t2) ->
        match split cmp v1 t2 with
            (l2, false, r2) ->
              concat cmp (inter cmp l1 l2) (inter cmp r1 r2)
          | (l2, true, r2) ->
              join cmp (inter cmp l1 l2) v1 (inter cmp r1 r2)

let rec diff cmp s1 s2 =
  match (s1, s2) with
      (Empty, t2) -> Empty
    | (t1, Empty) -> t1
    | (Node(l1, v1, r1, _), t2) ->
        match split cmp v1 t2 with
            (l2, false, r2) ->
              join cmp (diff cmp l1 l2) v1 (diff cmp r1 r2)
          | (l2, true, r2) ->
              concat cmp (diff cmp l1 l2) (diff cmp r1 r2)

type 'a enumeration = End | More of 'a * 'a rep * 'a enumeration

let rec cons_enum s e =
  match s with
      Empty -> e
    | Node(l, v, r, _) -> cons_enum l (More(v, r, e))

let rec compare_aux cmp e1 e2 =
  match (e1, e2) with
      (End, End) -> 0
    | (End, _)  -> -1
    | (_, End) -> 1
    | (More(v1, r1, e1), More(v2, r2, e2)) ->
        let c = cmp v1 v2 in
          if c <> 0
          then c
          else compare_aux cmp (cons_enum r1 e1) (cons_enum r2 e2)

let compare cmp s1 s2 =
  compare_aux cmp (cons_enum s1 End) (cons_enum s2 End)

let equal cmp s1 s2 =
  compare cmp s1 s2 = 0

let rec subset cmp s1 s2 =
  match (s1, s2) with
      Empty, _ ->
        true
    | _, Empty ->
        false
    | Node (l1, v1, r1, _), (Node (l2, v2, r2, _) as t2) ->
        let c = cmp v1 v2 in
          if c = 0 then
            subset cmp l1 l2 && subset cmp r1 r2
          else if c < 0 then
            subset cmp (Node (l1, v1, Empty, 0)) l2 && subset cmp r1 t2
          else
            subset cmp (Node (Empty, v1, r1, 0)) r2 && subset cmp l1 t2

let rec iter f = function
    Empty -> ()
  | Node(l, v, r, _) -> iter f l; f v; iter f r

let rec fold f s accu =
  match s with
      Empty -> accu
    | Node(l, v, r, _) -> fold f r (f v (fold f l accu))

let map cmp f s = fold (fun e s -> add cmp (f e) s) s empty

let map_union cmp f s = fold (fun e s -> union cmp (f e) s) s empty


let rec for_all p = function
    Empty -> true
  | Node(l, v, r, _) -> p v && for_all p l && for_all p r

let rec exists p = function
    Empty -> false
  | Node(l, v, r, _) -> p v || exists p l || exists p r

let filter cmp p s =
  let rec filt accu = function
    | Empty -> accu
    | Node(l, v, r, _) ->
        filt (filt (if p v then add cmp v accu else accu) l) r in
    filt Empty s

let partition cmp p s =
  let rec part (t, f as accu) = function
    | Empty -> accu
    | Node(l, v, r, _) ->
        part (part (if p v then (add cmp v t, f) else (t, add cmp v f)) l) r in
    part (Empty, Empty) s

let rec cardinal = function
    Empty -> 0
  | Node(l, v, r, _) -> cardinal l + 1 + cardinal r

let rec elements_aux accu = function
    Empty -> accu
  | Node(l, v, r, _) -> elements_aux (v :: elements_aux accu r) l

let elements s =
  elements_aux [] s

let choose = min_elt

type 'a set = { cmp : 'a -> 'a -> int; s : 'a rep }
                
let empty c = { cmp = c; s = Empty; }

let is_empty s = is_empty s.s

let mem x s = mem s.cmp x s.s

let add x s = { s with s = add s.cmp x s.s }

let singleton c x = { cmp = c; s = singleton x }

let remove x s = { s with s = remove s.cmp x s.s }

let union s1 s2 = { s1 with s = union s1.cmp s1.s s2.s }

let map_union c f s1 = { cmp = c; s = map_union c (fun x -> (f x).s) s1.s}

let inter s1 s2 = { s1 with s = inter s1.cmp s1.s s2.s }

let diff s1 s2 = { s1 with s = diff s1.cmp s1.s s2.s }

let compare_by cmp s1 s2 = compare cmp s1.s s2.s

let compare s1 s2 = compare s1.cmp s1.s s2.s

let equal s1 s2 = equal s1.cmp s1.s s2.s

let subset s1 s2 = subset s1.cmp s1.s s2.s
let subset_proper s1 s2 = (subset s1 s2) && not (equal s1 s2)

let iter f s = iter f s.s

let fold f s a = fold f s.s a

let map c f s = {cmp = c; s = map c f s.s}

let for_all p s = for_all p s.s

let exists p s = exists p s.s

let filter p s = { s with s = filter s.cmp p s.s }

let partition p s =
  let (r1,r2) = partition s.cmp p s.s in
    ({s with s = r1}, {s with s = r2})

let cardinal s = cardinal s.s

let elements s = elements s.s

let min_elt s = min_elt s.s

let min_elt_opt s = try Some (min_elt s) with Not_found -> None

let max_elt s = max_elt s.s

let max_elt_opt s = try Some (max_elt s) with Not_found -> None

let choose s = choose s.s

let set_case s c_emp c_sing c_else = match s.s with
    Empty -> c_emp
  | Node(Empty, v, Empty, _) -> c_sing v
  | _ -> c_else

let split x s =
  let (l,present,r) = split s.cmp x s.s in
    ({ s with s = l }, present, { s with s = r })

let from_list c l =
  List.fold_left (fun s x -> add x s) (empty c) l

let comprehension1 cmp f p s =
  fold (fun x s -> if p x then add (f x) s else s) s (empty cmp) 

let comprehension2 cmp f p s1 s2 =
  fold
    (fun x1 s -> 
       fold 
         (fun x2 s ->
            if p x1 x2 then add (f x1 x2) s else s)
         s2
         s) 
    s1 
    (empty cmp) 

let comprehension3 cmp f p s1 s2 s3 =
  fold 
    (fun x1 s -> 
       fold 
         (fun x2 s -> 
            fold 
              (fun x3 s ->
                 if p x1 x2 x3 then add (f x1 x2 x3) s else s)
              s3
              s)
         s2
         s) 
    s1 
    (empty cmp) 

let comprehension4 cmp f p s1 s2 s3 s4 =
  fold 
    (fun x1 s -> 
       fold 
         (fun x2 s -> 
            fold 
              (fun x3 s -> 
                 fold 
                   (fun x4 s ->
                      if p x1 x2 x3 x4 then add (f x1 x2 x3 x4) s else s)
                   s4
                   s)
              s3
              s)
         s2
         s) 
    s1 
    (empty cmp) 

let comprehension5 cmp f p s1 s2 s3 s4 s5 =
  fold 
    (fun x1 s -> 
       fold 
         (fun x2 s -> 
            fold 
              (fun x3 s -> 
                 fold 
                   (fun x4 s -> 
                      fold 
                        (fun x5 s ->
                           if p x1 x2 x3 x4 x5 then add (f x1 x2 x3 x4 x5) s else s)
                        s5
                        s)
                   s4
                   s)
              s3
              s)
         s2
         s) 
    s1 
    (empty cmp) 

let comprehension6 cmp f p s1 s2 s3 s4 s5 s6 =
  fold 
    (fun x1 s -> 
       fold 
         (fun x2 s -> 
            fold 
              (fun x3 s -> 
                 fold 
                   (fun x4 s -> 
                      fold 
                        (fun x5 s -> 
                           fold 
                             (fun x6 s -> 
                                if p x1 x2 x3 x4 x5 x6 then add (f x1 x2 x3 x4 x5 x6) s else s)
                             s6
                             s)
                        s5
                        s)
                   s4
                   s)
              s3
              s)
         s2
         s) 
    s1 
    (empty cmp) 

let comprehension7 cmp f p s1 s2 s3 s4 s5 s6 s7 =
  fold 
    (fun x1 s -> 
       fold 
         (fun x2 s -> 
            fold 
              (fun x3 s -> 
                 fold 
                   (fun x4 s -> 
                      fold 
                        (fun x5 s -> 
                           fold 
                             (fun x6 s -> 
                                fold 
                                  (fun x7 s -> 
                                     if p x1 x2 x3 x4 x5 x6 x7 then add (f x1 x2 x3 x4 x5 x6 x7) s else s)
                                  s7
                                  s)
                             s6
                             s)
                        s5
                        s)
                   s4
                   s)
              s3
              s)
         s2
         s) 
    s1 
    (empty cmp) 

let bigunion c xss =
  fold union xss (empty c)

let sigma c xs ys = 
  fold (fun x xys -> fold (fun y xys -> add (x,y) xys) (ys x) xys) xs (empty c)

let cross c xs ys = sigma c xs (fun _ -> ys)

let rec lfp s f =
  let s' = f s in
    if subset s' s then
      s
    else
      lfp (union s' s) f

let tc c r =
  let one_step r = fold (fun (x,y) xs -> fold (fun (y',z) xs ->
     if c (y,y) (y',y') = 0 then add (x,z) xs else xs) r xs) r (empty c) in
  lfp r one_step


let get_elem_compare s = s.cmp

