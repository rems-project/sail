# Sail RISC-V model for Coq

This directory contains the Coq files for the Sail RISC-V model, in
`sail/riscv`, along with the Sail Coq library (`sail/lib/coq`) and the
MIT BBV library for bitvector support.  The `build` script checks all
of the files, and `clean` removes the generated files.  The main model
is in `sail/riscv/riscv.v`.

The Coq version of the model was generated from the Sail sources
available at <https://github.com/rems-project/sail/tree/sail2/riscv>,
commit `b73f6d13b4bf2291f71616abdb046e2ca657d868`, and were manually
patched to deal with parts of the model that the tool does not fully
deal with, mostly due to recursive functions.  The manual changes can
be found in `sail/riscv/coq.patch`.

To reproduce the output from that particular commit of Sail, a small
change is needed in the type checker, given below.  This will be fixed
in the trunk shortly.

```
diff --git a/src/type_check.ml b/src/type_check.ml
index f98ddb9..9a7ae61 100644
--- a/src/type_check.ml
+++ b/src/type_check.ml
@@ -2560,7 +2560,7 @@ and type_coercion env (E_aux (_, (l, _)) as annotated_exp) typ =
   begin
     try
       typ_debug (lazy ("PERFORMING TYPE COERCION: from " ^ string_of_typ (typ_of annotated_exp) ^ " to " ^ string_of_typ typ));
-      subtyp l env (typ_of annotated_exp) typ; annotated_exp
+      subtyp l env (typ_of annotated_exp) typ; switch_typ annotated_exp typ
     with
     | Type_error (_, trigger) when Env.allow_casts env ->
        let casts = filter_casts env (typ_of annotated_exp) typ (Env.get_casts env) in
```
