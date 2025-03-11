structure IntRange where
  start : Int := 0
  stop  : Int
  step  : Nat := 1
  step_pos : 0 < step := by omega

namespace IntRange

instance instMemIntRange : Membership Int IntRange where
  mem r i := r.start ≤ i ∧ i < r.stop ∧ (i - r.start).toNat % r.step = 0

instance : DecidableRel (fun (i : Int) (r : IntRange) => i ∈ r) := fun i r => by
  simp [instMemIntRange]
  infer_instance

/-- The number of elements in the range. -/
def size (r : IntRange) : Nat := ((r.stop - r.start).toNat + r.step - 1) / r.step

@[inline] protected def forIn' [Monad m] (range : IntRange) (init : β)
    (f : (i : Int) → i ∈ range → β → m (ForInStep β)) : m β :=
  if size_lt : range.start + ↑range.step * (↑range.size - 1) < range.stop then
    let rec @[specialize] loop (b : β) (numIterations : Nat) (i : Int)
          (hs : (i - range.start).toNat % range.step = 0) (hl : range.start ≤ i)
          (hnum : i + range.step * (numIterations - 1) < range.stop) : m β := do
        match numIterations with
        | .succ num =>
          match ← f i ⟨hl, Int.lt_of_le_of_lt (Int.le_add_of_nonneg_right
            (Int.mul_nonneg (Int.ofNat_zero_le range.step)
              (Int.le_sub_one_of_lt (Int.ofNat_succ_pos num)))) hnum, hs⟩ b with
          | .done b => pure b
          | .yield b =>
            loop b num (i + range.step) (by rw [Int.add_comm, Int.add_sub_assoc,
                Int.toNat_add (Int.ofNat_zero_le range.step) (Int.sub_nonneg_of_le hl)]; simpa)
              (by omega)
              (Int.lt_of_le_of_lt (Int.add_assoc _ _ _ ▸
                Int.add_le_add_left (by simp [Int.mul_sub]; omega) i) hnum)
        | 0 =>
          pure b
    loop init range.size range.start (by simp) (Int.le_refl _) size_lt
  else pure init

instance : ForIn' m IntRange Int inferInstance where
  forIn' := IntRange.forIn'

@[inline] protected def forM [Monad m] (range : IntRange) (f : Int → m PUnit) : m PUnit :=
  let rec @[specialize] loop (i : Int) (numIterations : Nat) : m PUnit := do
    match numIterations with
    | .succ num =>
      f i
      loop (i + range.step) num
    | 0 => pure ⟨⟩
  have := range.step_pos
  loop range.start range.size

instance : ForM m IntRange Int where
  forM := IntRange.forM

syntax:max "[" withoutPosition(":" term) "]i" : term
syntax:max "[" withoutPosition(term ":" term) "]i" : term
syntax:max "[" withoutPosition(":" term ":" term) "]i" : term
syntax:max "[" withoutPosition(term ":" term ":" term) "]i" : term

macro_rules
  | `([ : $stop]i) => `({ stop := $stop, step_pos := Nat.zero_lt_one : IntRange })
  | `([ $start : $stop ]i) => `({ start := $start, stop := $stop, step_pos := Nat.zero_lt_one : IntRange })
  | `([ $start : $stop : $step ]i) => `({ start := $start, stop := $stop, step := $step : IntRange })
  | `([ : $stop : $step ]i) => `({ stop := $stop, step := $step : IntRange })

end IntRange
