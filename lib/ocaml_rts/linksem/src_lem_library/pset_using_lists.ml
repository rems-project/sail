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
(* Modified by Kyndylan Nienhuis 2013-04-.. *)

(* $Id: set.ml 6694 2004-11-25 00:06:06Z doligez $ *)

(* Sets over ordered types *)



(* Implementation of the set operations *)

type 'a rep = 'a list

exception Not_implemented

let rec add cmp x list =
  x::list
  
let empty = []

let is_empty = function [] -> true | _ -> false

let rec mem cmp x = function
    [] -> false
  | v::l ->
      let c = cmp x v in
        c = 0 || mem cmp x l

let singleton x = [x]

let rec remove cmp x = function
    [] -> []
  | v::l ->
      let c = cmp x v in
        if c = 0 then remove cmp x l else
          v::(remove cmp x l)

let compare cmp s1 s2 =
  raise Not_implemented

let equal cmp s1 s2 =
  compare cmp s1 s2 = 0

let rec iter f = function
    [] -> ()
  | v::l -> iter f l; f v

let rec fold f s accu =
  match s with
      [] -> accu
    | v::l -> f v (fold f l accu)

let map cmp f s = fold (fun e s -> add cmp (f e) s) s empty

let rec for_all p = function
    [] -> true
  | v::l -> p v && for_all p l

let rec exists p = function
    [] -> false
  | v::l -> p v || exists p l
  
let rec subset cmp s1 s2 =
  for_all (fun e -> mem cmp e s2) s1

let filter cmp p s =
  let rec filt accu = function
    | [] -> accu
    | v::r ->
        filt (if p v then add cmp v accu else accu) r in
    filt [] s

let partition cmp p s =
  let rec part (l, r as accu) = function
    | [] -> accu
    | h::t ->
        part (if p h then (add cmp h l, r) else (l, add cmp h r)) t in
    part ([], []) s

let rec union cmp s1 s2 =
  match s1 with 
      [] -> s2
    | v::l -> v::(union cmp l s2)

let rec inter cmp s1 s2 =
  filter cmp (fun e -> mem cmp e s2) s1

let rec cardinal cmp = function
    [] -> 0
  | h::t -> (cardinal cmp (remove cmp h t)) + 1

let elements s =
  s
  
let diff cmp s s = 
  raise Not_implemented
  
let min_elt s = 
  raise Not_implemented

let max_elt s = 
  raise Not_implemented

let split cmp x s =
  raise Not_implemented

(* It's not determenistic in the sense that s1.choose = s2.choose given that s1 equals s2 *)
let choose = function
    [] -> raise Not_found
  | h::_ -> h

type 'a set = { cmp : 'a -> 'a -> int; s : 'a rep }
             
let empty c = { cmp = c; s = []; }

let is_empty s = is_empty s.s

let mem x s = mem s.cmp x s.s

let add x s = { s with s = add s.cmp x s.s }

let singleton c x = { cmp = c; s = singleton x }

let remove x s = { s with s = remove s.cmp x s.s }

let union s1 s2 = { s1 with s = union s1.cmp s1.s s2.s }

let inter s1 s2 = { s1 with s = inter s1.cmp s1.s s2.s }

let diff s1 s2 = { s1 with s = diff s1.cmp s1.s s2.s }

let compare s1 s2 = compare s1.cmp s1.s s2.s

let equal s1 s2 = equal s1.cmp s1.s s2.s

let subset s1 s2 = subset s1.cmp s1.s s2.s

let iter f s = iter f s.s

let fold f s a = fold f s.s a

let map c f s = {cmp = c; s = map c f s.s}

let for_all p s = for_all p s.s

let exists p s = exists p s.s

let filter p s = { s with s = filter s.cmp p s.s }

let partition p s =
  let (r1,r2) = partition s.cmp p s.s in
    ({s with s = r1}, {s with s = r2})

let cardinal s = cardinal s.cmp s.s

let elements s = elements s.s

let min_elt s = min_elt s.s

let max_elt s = max_elt s.s

let choose s = choose s.s

let split x s =
  let (l,present,r) = split s.cmp x s.s in
    ({ s with s = l }, present, { s with s = r })

let from_list c l =
  {cmp = c; s = l}

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

let rec lfp s f =
  let s' = f s in
    if subset s' s then
      s
    else
      lfp (union s' s) f

let cross c xs ys = 
  fold (fun x xys -> fold (fun y xys -> add (x,y) xys) ys xys) xs (empty c)

let rec lfp s f =
  let s' = f s in
    if subset s' s then
      s
    else
      lfp (union s' s) f

let tc c r =
  let one_step r = fold (fun (x,y) xs -> fold (fun (y',z) xs ->
     if y = y' then add (x,z) xs else xs) r xs) r (empty c) in
  lfp r one_step
