Require Import ZArith Eqdep_dec String List.

Module Z_eq_dec.
Definition U := Z.
Definition eq_dec := Z.eq_dec.
End Z_eq_dec.
Module ZEqdep := DecidableEqDep (Z_eq_dec).

(* Opaque identity for bad unchecked operations. *)
Definition dummy {T:Type} (t:T) : T.
exact t.
Qed.

(* To avoid carrying around proofs that vector sizes are correct everywhere,
   we extend many operations to cover nonsensical sizes.  To help, we have a
   typeclass of inhabited types so that we can pick a default value, and an
   opaque function that returns it - well typed Sail code reduction
   should never reach this definition. *)

Class Inhabited (T:Type) := { inhabitant : T }.
Definition dummy_value {T:Type} `{Inhabited T} := inhabitant.
Global Opaque dummy_value.

#[export] Instance unit_inhabited : Inhabited unit := { inhabitant := tt }.
#[export] Instance z_inhabited : Inhabited Z := { inhabitant := 0 }.
#[export] Instance string_inhabited : Inhabited string := { inhabitant := "" }.
#[export] Instance bool_inhabited : Inhabited bool := { inhabitant := false }.
#[export] Instance pair_inhabited {X Y} `{Inhabited X} `{Inhabited Y} : Inhabited (X * Y) := {
  inhabitant := (inhabitant, inhabitant)
}.
#[export] Instance list_inhabited {X} : Inhabited (list X) := { inhabitant := List.nil }.
#[export] Instance option_inhabited {X} : Inhabited (option X) := { inhabitant := None }.

(* For the indexed machine words we sometimes need to change to an
   equivalent index.  These provide nat and Z casts that compute. *)

Section TypeCasts.

Fixpoint cast_nat {T : nat -> Type} {m n : nat} : T m -> m = n -> T n :=
  match m, n return T m -> m = n -> T n with
  | O, O => fun x _ => x
  | S m', S n' => fun x e => @cast_nat (fun o => T (S o)) m' n' x ltac:(congruence)
  | S m', O => fun x e => ltac:(congruence)
  | O, S n' => fun x e => ltac:(congruence)
  end.

Lemma cast_nat_refl n T (x : T n) (e : n = n) : cast_nat x e = x.
revert T x e.
induction n.
- reflexivity.
- intros.
  simpl.
  apply IHn with (T := fun m => T (S m)).
Qed.

Fixpoint cast_positive (T : positive -> Type) (p q : positive) : T p -> p = q -> T q.
refine (
match p, q with
| xH, xH => fun x _ => x
| xO p', xO q' => fun x e => cast_positive (fun x => T (xO x)) p' q' x _
| xI p', xI q' => fun x e => cast_positive (fun x => T (xI x)) p' q' x _
| _, _ => _
end); congruence.
Defined.

Definition cast_Z {T : Z -> Type} {m n} : forall (x : T m) (eq : m = n), T n.
refine (match m,n with
| Z0, Z0 => fun x _ => x
| Zneg p1, Zneg p2 => fun x e => cast_positive (fun p => T (Zneg p)) p1 p2 x _
| Zpos p1, Zpos p2 => fun x e => cast_positive (fun p => T (Zpos p)) p1 p2 x _
| _,_ => _
end); congruence.
Defined.

Lemma cast_positive_refl : forall p T x (e : p = p),
  cast_positive T p p x e = x.
induction p.
* intros. simpl. rewrite IHp; auto.
* intros. simpl. rewrite IHp; auto.
* reflexivity.
Qed.

Lemma cast_Z_refl {T : Z -> Type} {m} {H:m = m} (x : T m) : cast_Z x H = x.
destruct m.
* reflexivity.
* simpl. rewrite cast_positive_refl. reflexivity.
* simpl. rewrite cast_positive_refl. reflexivity.
Qed.

Definition autocast {T : Z -> Type} {m n} `{Inhabited (T n)} (x : T m) : T n :=
match Z.eq_dec m n with
| left eq => cast_Z x eq
| right _ => dummy_value
end.
#[global] Arguments autocast _ _ & _ _.

Lemma autocast_refl {T} n `{Inhabited (T n)} (x : T n) : autocast x = x.
unfold autocast.
apply (decide_left (Z.eq_dec n n)); auto.
intro.
apply cast_Z_refl.
Qed.

(* Note that `rewrite` won't automatically open a subgoal for `EQ` because it's
   named, so either give it up-front or use erwrite.  In general it's probably
   better to avoid using this in favour of autocast_refl or autocast_eq_dep, which
   don't need to mention the equality proof in the result. *)
Lemma autocast_eq {T m n} `{Inhabited (T n)} (x : T m) : forall EQ : m = n, autocast x = cast_Z x EQ.
intros.
subst.
rewrite autocast_refl.
rewrite cast_Z_refl.
reflexivity.
Qed.

Lemma autocast_eq_dep T m n `{Inhabited (T n)} x : m = n -> EqdepFacts.eq_dep Z T m x n (autocast x).
intro EQ.
subst.
rewrite autocast_refl.
constructor.
Qed.

End TypeCasts.
