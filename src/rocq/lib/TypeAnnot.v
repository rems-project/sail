Require Import Ast.

(** Sail annotates terms with custom type annotation data, which we
    don't have access to here. Instead use a functor parameterised by
    the following signature, which can provide the methods we need. *)
Module Type S.
  Parameter t : Set.

  Parameter get_type : t -> typ.

  Parameter get_id_type : t -> id -> id_type.

  Parameter get_split : t -> vector_concat_split.

  Parameter is_bitvector : t -> bool.

  Parameter fallthrough : Ast.pexp t.
End S.
