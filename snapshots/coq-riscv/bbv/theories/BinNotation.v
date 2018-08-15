
(* Adapted from http://poleiro.info/posts/2013-04-03-parse-errors-as-type-errors.html,
   https://github.com/arthuraa/poleiro/blob/master/theories/ForceOption.v
   to produce N instead of nat *)

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.NArith.

Local Open Scope char_scope.

Local Open Scope N_scope.

Definition binDigitToN (c : ascii) : option N :=
  match c with
    | "0" => Some 0
    | "1" => Some 1
    | _   => None
  end.

Open Scope string_scope.

Fixpoint readBinNAux (s : string) (acc : N) : option N :=
  match s with
    | "" => Some acc
    | String c s' =>
      match binDigitToN c with
        | Some n => readBinNAux s' (2 * acc + n)
        | None => None
      end
  end.

Definition readBinN (s : string) : option N := readBinNAux s 0.

Goal readBinN "11111111" = Some 255.
Proof. reflexivity. Qed.

Definition forceOption A Err (o : option A) (err : Err) : match o with
                                                            | Some _ => A
                                                            | None => Err
                                                          end :=
  match o with
    | Some a => a
    | None => err
  end.

Inductive parseError := ParseError.

Definition bin (s : string) := forceOption N parseError (readBinN s) ParseError.

Goal bin"11111111" = 255.
Proof. reflexivity. Qed.

Goal bin"1011" = 11.
Proof. reflexivity. Qed.

Goal bin"1O" = ParseError.
Proof. reflexivity. Qed.
