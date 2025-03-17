/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat
-/

-- Taken from https://github.com/leanprover/LNSym/blob/main/Arm/BitVec.lean

import Lean.Elab.Term
import Lean.Meta.Reduce
import Std.Tactic.BVDecide

open BitVec

/- Bitvector pattern component syntax category, originally written by
Leonardo de Moura. -/
declare_syntax_cat bvpat_comp
syntax num (":" num)? : bvpat_comp
syntax ident (":" num)? : bvpat_comp
syntax "_" (":" num)? : bvpat_comp

/--
Bitvector pattern syntax category.
Example: [sf:1,0011010000,Rm:5,000000,Rn:5,Rd:5]
-/
declare_syntax_cat bvpat
syntax num : bvpat
syntax "[" bvpat_comp,* "]" ("if" term)? : bvpat

open Lean

abbrev BVPatComp := TSyntax `bvpat_comp
abbrev BVPat := TSyntax `bvpat

/-- Return the number of bits in a bit-vector component pattern. -/
def BVPatComp.length (c : BVPatComp) : Nat := Id.run do
  match c with
  | `(bvpat_comp| $n:num $[: $_]?) =>
    let some str := n.raw.isLit? `num | pure 0
    return str.length
  | `(bvpat_comp| $_:ident : $n:num) | `(bvpat_comp| _ : $n:num) =>
    return n.raw.toNat
  | `(bvpat_comp| $_:ident ) | `(bvpat_comp| _) =>
    return 1
  | _ =>
    return 0

/--
If the pattern component is a bitvector literal, convert it into a bit-vector term
denoting it.
-/
def BVPatComp.toBVLit? (c : BVPatComp) : MacroM (Option Term) := do
  match c with
  | `(bvpat_comp| $n:num $[: $_]?) =>
    let len := c.length
    let some str := n.raw.isLit? `num | Macro.throwErrorAt c "invalid bit-vector literal"
    let bs := str.toList
    let mut val := 0
    for b in bs do
      if b = '1' then
        val := 2*val + 1
      else if b = '0' then
        val := 2*val
      else
        Macro.throwErrorAt c "invalid bit-vector literal, '0'/'1's expected"
    let r ← `(BitVec.ofNat $(quote len) $(quote val))
    return some r
  | _ => return none

/--
If the pattern component is a pattern variable of the form `<id>:<size>` return
`some id`.
-/
def BVPatComp.toBVVar? (c : BVPatComp) : MacroM (Option (TSyntax `ident)) := do
  match c with
  | `(bvpat_comp| $x:ident $[: $_:num]?) =>
    return some x
  | _ => return none

def BVPat.getComponents (p : BVPat) : MacroM ((Array BVPatComp) × Option Term) :=
  match p with
  | `(bvpat|$n:num) => do
    let n ← `(bvpat_comp|$n:num)
    return (#[n],none)
  | `(bvpat| [$comp,*] $[if $t]?) => return (comp.getElems.reverse,t)
  | _ => return (#[],none)

/--
Return the number of bits in a bit-vector pattern.
-/
def BVPat.length (p : BVPat) : MacroM Nat := do
  let mut sz := 0
  for c in (← p.getComponents).1 do
    sz := sz + c.length
  return sz

/--
Given a variable `var` representing a term that matches the pattern `pat`, and a term `rhs`,
return a term of the form
```
let y₁ := var.extract ..
...
let yₙ := var.extract ..
rhs
```
where `yᵢ`s are the pattern variables in `pat`.
-/
def declBVPatVars (vars : Array Term) (pats : Array BVPat) (rhs : Term) : MacroM Term := do
  let mut result := rhs
  for (pat, var) in pats.zip vars do
    let mut shift  := 0
    for c in (← pat.getComponents).1 do
      let len := c.length
      if let some y ← c.toBVVar? then
        let rhs ← `(extractLsb $(quote (shift + (len - 1))) $(quote shift) $var)
        result ← `(let $y := $rhs; $result)
      shift := shift + len
  return result


/--
Return a term that evaluates to `true` if `var` is an instance of the pattern `pat`.
-/
def genBVPatMatchTest (vars : Array Term) (pats : Array BVPat): MacroM Term := do
  if vars.size != pats.size then
    Macro.throwError "incorrect number of patterns"
  let mut result ← `(true)

  for (pat, var) in pats.zip vars do
    let mut shift := 0
    let (cs,if') ← pat.getComponents
    for c in cs do
      let len := c.length
      if let some bv ← c.toBVLit? then
        let test ← `(extractLsb $(quote (shift + (len - 1))) $(quote shift) $var == $bv)
        result ← `($result && $test)
      shift := shift + len
    if let some t := if' then
      let t ← declBVPatVars vars pats t
      result ← `($result && $t)
  return result

/--
Define the `match_bv .. with | bvpat => rhs | _ => rhs`.
The last entry is the `else`-case since we currently do not check whether
the patterns are exhaustive or not.
-/
syntax (name := matchBv) "match_bv " term,+ "with" (atomic("| " bvpat,+) " => " term)* ("| " "_ " " => " term)? : term

open Lean
open Elab
open Term

def checkBVPatLengths (lens : Array (Option Nat)) (pss : Array (Array BVPat)) : TermElabM Unit := do
    for (len, i) in lens.zipIdx do
      let mut patLen := none
      for ps in pss do
        unless ps.size == lens.size do
          throwError "Expected {lens.size} patterns, found {ps.size}"
        let p := ps[i]!
        let pLen ← liftMacroM p.length

        -- compare the length to that of the type of the discriminant
        if let some pLen' := len then
          unless pLen == pLen' do
            throwErrorAt p "Expected pattern of length {pLen'}, found {pLen} instead"

        -- compare the lengths of the patterns
        if let some pLen' := patLen then
          unless pLen == pLen' do
            throwErrorAt  p "patterns have differrent lengths"
        else
          patLen := some pLen

-- We use this to gather all the conditions expressing that the
-- previous pattern matches failed. This allows in turn to prove
-- exaustivity of the pattern matching.
abbrev dite_gather {α : Sort u} {old : Prop} (c : Prop) [h : Decidable c]
        (t : old ∧ c → α) (e : old ∧ ¬ c → α) (ho : old) : α :=
  if hc : c then
    t (And.intro ho hc)
  else
    e (And.intro ho hc)

@[term_elab matchBv]
partial
def elabMatchBv : TermElab := fun stx typ? =>
  match stx with
  | `(match_bv $[$discrs:term],* with
      $[ | $[$pss:bvpat],* => $rhss:term ]*
         $[| _ => $rhsElse?:term]?) => do
    let xs := discrs

    -- try to get the length of the BV to error-out
    -- if a pattern has the wrong length
    -- TODO: is it the best way to do that?
    let lens ← discrs.mapM (fun x => do
      let x ← elabTerm x none
      let typ ← Meta.inferType x
      match_expr typ with
      | BitVec n  =>
        let n ← Meta.reduce n
        match n with
        | .lit (.natVal n) => return some n
        | _ => return none
      | _ => return none)

    checkBVPatLengths lens pss

    let mut result :=
      ← if let some rhsElse := rhsElse? then
          `(Function.const _ $rhsElse)
        else
          `(fun _ => by bv_decide)

    for ps in pss.reverse, rhs in rhss.reverse do
      let test ← liftMacroM <| genBVPatMatchTest xs ps
      let rhs  ← liftMacroM <| declBVPatVars xs ps rhs
      result ← `(dite_gather $test (Function.const _ $rhs) $result)
    let res ← liftMacroM <| `($result True.intro)
    elabTerm res typ?
  | _ => throwError "invalid syntax"


----------- TESTS -----------

-- def test (merge_var : (BitVec 8)) : IO Unit := do
  -- match_bv merge_var with
  -- | [00,1111,00] => return ()
  -- | [0,_:5,1,0]  => return ()
  -- | [0,_:5,1,_]  => return ()
  -- | [0,_:5,1,1]  => return ()
  -- | _ =>            return ()

-- def test_1 (x : BitVec 32) : BitVec 16 :=
--    match_bv x with
--    | [sf:1,0011010000,Rm:5,000000,Rn:5,Rd:5] => sf ++ Rm ++ Rn ++ Rd
--    | [sf:1,0000010000,11111000000,Rn:5,Rd:5] => sf ++ Rn ++ Rd ++ Rd
--    | _ => 0#16

-- def test_2 (x y : BitVec 32) : BitVec 16 :=
--    match_bv x, y with
--    | [sf:1,0011010000,Rm:5,000000,Rn:5,Rd:5], [sf':1,0000010000,11111000000,Rn':5,Rd':5]
--        => sf ++ Rm ++ Rn ++ Rd
--    | [sf:1,0000010000,11111000000,Rn:5,Rd:5], [sf:1,0000010000,11111000000,Rn:5,Rd:5] => sf ++ Rn ++ Rd ++ Rd
--    | _ => 0#16

-- /-- error: Expected pattern of length 33, found 32 instead -/
-- #guard_msgs in
-- def test_fail_length_one_pat (x : BitVec 33) : Bool :=
--    match_bv x with
--    | [sf:1,0011010000,Rm:5,000000,Rn:5,Rd:5] => true
--    | [sf:1,0000010000,11111000000,Rn:6,Rd:5] => false
--    | _ => true

-- /-- error: Expected pattern of length 33, found 32 instead -/
-- #guard_msgs in
-- def test_fail_length_two_pats (x : BitVec 32) (y : BitVec 33) : BitVec 16 :=
--    match_bv x, y with
--    | [sf:1,0011010000,Rm:5,000000,Rn:5,Rd:5], [sf':1,0000010000,11111000000,Rn':6,Rd':5]
--        => sf ++ Rm ++ Rn ++ Rd
--    | [sf:1,0000010000,11111000000,Rn:5,Rd:5], [sf:1,0000010000,11111000000,Rn:5,Rd:5] => sf ++ Rn ++ Rd ++ Rd
--    | _ => 0#16


-- def xlen := 32

-- def write_CSR (x : BitVec 12): Bool := match_bv x with
--   | [1011100,index:5] if xlen == 32 && index >= 3 => true
--   | [1011000,index:5] if index >= 3 => true
--   | _ => true

-- -- TODO: it would be nice to check that the pattern length corresponds to the
-- -- length of the bit-vector being pattern match against...
-- def test_exhaustive_1 (x : BitVec 1) : Bool :=
--   match_bv x with
--   | [0] => true
--   | [1] => false

-- def test_exhaustive_2 (x : BitVec 2) : Bool :=
--   match_bv x with
--   | [0, _:1] => true
--   | [1, _:1] => false

-- -- Failing test, because it is not exhaustive!
-- -- TODO: have a more informative error message
-- /--
-- error: The prover found a counterexample, consider the following assignment:
-- x = 0x0#2
-- -/
-- #guard_msgs in
-- def test_fail_exhaustive_3 (x : BitVec 2) : Bool :=
--   match_bv x with
--   | [01] => true
--   | [1, _:1] => false
