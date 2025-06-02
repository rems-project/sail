From SailStdpp Require Import Base.
Require Import armV8_types.

Definition TMCommitEffect (_ : unit) : M unit := returnM tt.

Definition SCTLR_EL1_type_to_SCTLR_type (x : SCTLR_EL1_type) : SCTLR_type := x.

Inductive diafp := DIAFP_none : unit -> diafp.
