open Nat_num

type 'a vector = Vector of  'a array

val vconcat : 'a vector -> 'a vector -> 'a vector 

val vmap : ('a ->'b) ->  'a vector  -> 'b vector 

val vfold :  ('b -> 'a -> 'b) -> 'b -> 'a vector -> 'b

val vzip : 'a vector -> 'b vector -> ('a * 'b) vector 

val vmapacc : ('a -> 'c -> ('b * 'c)) -> 'a vector -> 'c -> ('b vector) * 'c

val vmapi : (nat -> 'a -> 'b) -> 'a vector -> 'b vector

val extend : 'a -> nat -> 'a vector -> 'a vector

val duplicate : 'a vector -> 'a vector

val vlength : 'a vector -> nat

val vector_access : nat ->'a vector -> 'a

val vector_slice : nat -> nat ->'a vector -> 'a vector

val make_vector : 'a list -> nat -> 'a vector

