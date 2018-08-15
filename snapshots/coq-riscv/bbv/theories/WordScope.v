(* Word.v defines notations for words by first opening word_scope, and then closing it again,
   to prevent notation clashes.
   It does, however, bind word_scope to the type word, so whenever an expression of type word
   is expected, it is parsed with notations enabled, but when the expected type is unknown,
   word notations don't work by default.
   If you want to enable them even for unknown expected types, you can import this file
   instead of Word.v. *)

Require Export bbv.Word.
Open Scope word_scope.
