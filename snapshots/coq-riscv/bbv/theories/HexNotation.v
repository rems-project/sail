
(* Adapted from http://poleiro.info/posts/2013-04-03-parse-errors-as-type-errors.html,
   https://github.com/arthuraa/poleiro/blob/master/theories/ForceOption.v
   to produce N instead of nat *)

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.NArith.

Local Open Scope char_scope.

Local Open Scope N_scope.

Definition hexDigitToN (c : ascii) : option N :=
  match c with
    | "0" => Some 0
    | "1" => Some 1
    | "2" => Some 2
    | "3" => Some 3
    | "4" => Some 4
    | "5" => Some 5
    | "6" => Some 6
    | "7" => Some 7
    | "8" => Some 8
    | "9" => Some 9
    | "a" | "A" => Some 10
    | "b" | "B" => Some 11
    | "c" | "C" => Some 12
    | "d" | "D" => Some 13
    | "e" | "E" => Some 14
    | "f" | "F" => Some 15
    | _   => None
  end.

Open Scope string_scope.

Fixpoint readHexNAux (s : string) (acc : N) : option N :=
  match s with
    | "" => Some acc
    | String c s' =>
      match hexDigitToN c with
        | Some n => readHexNAux s' (16 * acc + n)
        | None => None
      end
  end.

Definition readHexN (s : string) : option N := readHexNAux s 0.

Goal readHexN "ff" = Some 255.
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

Definition hex (s : string) := forceOption N parseError (readHexN s) ParseError.

Goal hex"ff" = 255.
Proof. reflexivity. Qed.

Goal hex"a0f" = 2575.
Proof. reflexivity. Qed.

Goal hex"1O" = ParseError.
Proof. reflexivity. Qed.

Goal hex"ff34c8e3" = 4281649379.
Proof. reflexivity. Qed.
