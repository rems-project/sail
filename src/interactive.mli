open Ast
open Type_check

val opt_interactive : bool ref
val opt_emacs_mode : bool ref
val opt_suppress_banner : bool ref

val ast : tannot defs ref

val env : Env.t ref
