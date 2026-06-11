open Basics
open Datatypes
open Base

(** val set_size : ('a1, 'a2) coq_Elements -> 'a2 coq_Size **)

let set_size h =
  compose length (elements h)
