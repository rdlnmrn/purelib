module
import Purelib.Data.Nat.Addition
import Purelib.Tactic.Ring
-- Public power expressions retain the same natural monoid operations.
public import Purelib.Algebra.Semiring.Nat

section
public section

/-!
# Finite sharpness witnesses for the Dirichlet window

This module constructs a wholly rational family of index-one windows.  The
parameters satisfy the Pell identity

`m ^ 2 - 4 * m * n + n ^ 2 = 1`,

so their normalized coordinates approach the quadratic boundary without
introducing its omitted irrational zero.  Every member is finite data and
will carry its own minimal-cylinder certificate.
-/

namespace Purelib.NumberTheory.Pell.FiniteBranch

/-! ## Pell states at each supplied finite stage -/

/-- The additive Pell state `(m,d)`, with the eventual denominator
`n=m+d`.  Keeping the positive difference `d` rather than a signed matrix
recurrence makes every executable step subtraction-free. -/
@[expose] def pellState : Nat → Nat × Nat
  | 0 => (1, 3)
  | stage + 1 =>
      let previous := Purelib.NumberTheory.Pell.FiniteBranch.pellState stage
      (previous.1 + previous.2, 2 * previous.1 + 3 * previous.2)

section
open Purelib.NumberTheory
/-- Numerator `m` of the critical rational parameter. -/
@[expose] def pellNumerator (stage : Nat) : Nat := (Pell.FiniteBranch.pellState stage).1

/-- Positive difference `d=n-m` in the subtraction-free recurrence. -/
@[expose] def pellDifference (stage : Nat) : Nat := (Pell.FiniteBranch.pellState stage).2

/-- Denominator `n=m+d` of the critical rational parameter. -/
@[expose] def pellDenominator (stage : Nat) : Nat :=
  Pell.FiniteBranch.pellNumerator stage + Pell.FiniteBranch.pellDifference stage

/-- The initial Pell numerator is one. -/
@[simp] theorem pellNumerator_zero : Pell.FiniteBranch.pellNumerator 0 = 1 := rfl
/-- The initial denominator-minus-numerator difference is three. -/
@[simp] theorem pellDifference_zero : Pell.FiniteBranch.pellDifference 0 = 3 := rfl
/-- The initial Pell denominator is four. -/
@[simp] theorem pellDenominator_zero : Pell.FiniteBranch.pellDenominator 0 = 4 := rfl

/-- The next numerator is the current numerator plus the retained difference. -/
@[simp] theorem pellNumerator_succ (stage : Nat) :
    Pell.FiniteBranch.pellNumerator (stage + 1) =
      Pell.FiniteBranch.pellNumerator stage + Pell.FiniteBranch.pellDifference stage := by
  rfl

/-- The next difference is twice the current numerator plus three times the current difference. -/
@[simp] theorem pellDifference_succ (stage : Nat) :
    Pell.FiniteBranch.pellDifference (stage + 1) =
      2 * Pell.FiniteBranch.pellNumerator stage + 3 * Pell.FiniteBranch.pellDifference stage := by
  rfl

/-- The subtraction-free form of the Pell identity. -/
theorem pellDifference_sq
    (stage : Nat) :
    Pell.FiniteBranch.pellDifference stage ^ 2 =
      2 * Pell.FiniteBranch.pellNumerator stage ^ 2 +
        2 * Pell.FiniteBranch.pellNumerator stage * Pell.FiniteBranch.pellDifference stage + 1 := by
  induction stage with
  | zero => decide
  | succ stage inductionHypothesis =>
      rw [Pell.FiniteBranch.pellNumerator_succ, Pell.FiniteBranch.pellDifference_succ]
      apply Purelib.Data.Nat.Addition.add_left_cancel
      calc
        (2 * Pell.FiniteBranch.pellNumerator stage ^ 2 +
              2 * Pell.FiniteBranch.pellNumerator stage * Pell.FiniteBranch.pellDifference stage) +
            (2 * Pell.FiniteBranch.pellNumerator stage +
              3 * Pell.FiniteBranch.pellDifference stage) ^ 2 =
          (2 * (Pell.FiniteBranch.pellNumerator stage + Pell.FiniteBranch.pellDifference stage) ^ 2 +
              2 * (Pell.FiniteBranch.pellNumerator stage + Pell.FiniteBranch.pellDifference stage) *
                (2 * Pell.FiniteBranch.pellNumerator stage + 3 * Pell.FiniteBranch.pellDifference stage)) +
            Pell.FiniteBranch.pellDifference stage ^ 2 := by ring1
        _ =
          (2 * (Pell.FiniteBranch.pellNumerator stage + Pell.FiniteBranch.pellDifference stage) ^ 2 +
              2 * (Pell.FiniteBranch.pellNumerator stage + Pell.FiniteBranch.pellDifference stage) *
                (2 * Pell.FiniteBranch.pellNumerator stage + 3 * Pell.FiniteBranch.pellDifference stage)) +
            (2 * Pell.FiniteBranch.pellNumerator stage ^ 2 +
              2 * Pell.FiniteBranch.pellNumerator stage * Pell.FiniteBranch.pellDifference stage + 1) := by
          rw [inductionHypothesis]
        _ =
          (2 * Pell.FiniteBranch.pellNumerator stage ^ 2 +
              2 * Pell.FiniteBranch.pellNumerator stage * Pell.FiniteBranch.pellDifference stage) +
            (2 * (Pell.FiniteBranch.pellNumerator stage + Pell.FiniteBranch.pellDifference stage) ^ 2 +
              2 * (Pell.FiniteBranch.pellNumerator stage + Pell.FiniteBranch.pellDifference stage) *
                (2 * Pell.FiniteBranch.pellNumerator stage + 3 * Pell.FiniteBranch.pellDifference stage) + 1) := by
          ring1

/-- The positive state remains in the elementary chamber
`2*m < d ≤ 3*m`. -/
theorem pellDifference_bounds (stage : Nat) :
    2 * Pell.FiniteBranch.pellNumerator stage < Pell.FiniteBranch.pellDifference stage ∧
      Pell.FiniteBranch.pellDifference stage ≤ 3 * Pell.FiniteBranch.pellNumerator stage := by
  induction stage with
  | zero => decide
  | succ stage inductionHypothesis =>
      rw [Pell.FiniteBranch.pellNumerator_succ, Pell.FiniteBranch.pellDifference_succ]
      have differencePositive : 0 < Pell.FiniteBranch.pellDifference stage :=
        (Nat.zero_le (2 * Pell.FiniteBranch.pellNumerator stage)).trans_lt
          inductionHypothesis.1
      constructor
      · calc
          2 * (Pell.FiniteBranch.pellNumerator stage + Pell.FiniteBranch.pellDifference stage) =
              2 * Pell.FiniteBranch.pellNumerator stage + 2 * Pell.FiniteBranch.pellDifference stage := by ring1
          _ < 2 * Pell.FiniteBranch.pellNumerator stage + 3 * Pell.FiniteBranch.pellDifference stage :=
            Nat.add_lt_add_left
              (Nat.mul_lt_mul_of_pos_right (by decide) differencePositive) _
      · calc
          2 * Pell.FiniteBranch.pellNumerator stage + 3 * Pell.FiniteBranch.pellDifference stage ≤
              3 * Pell.FiniteBranch.pellNumerator stage + 3 * Pell.FiniteBranch.pellDifference stage :=
            Nat.add_le_add_right
              (Nat.mul_le_mul_right (Pell.FiniteBranch.pellNumerator stage) (by decide)) _
          _ = 3 * (Pell.FiniteBranch.pellNumerator stage + Pell.FiniteBranch.pellDifference stage) := by ring1

/-- Every finite Pell numerator is positive. -/
theorem pellNumerator_pos (stage : Nat) : 0 < Pell.FiniteBranch.pellNumerator stage := by
  induction stage with
  | zero => decide
  | succ stage inductionHypothesis =>
      rw [Pell.FiniteBranch.pellNumerator_succ]
      exact inductionHypothesis.trans_le
        (Nat.le_add_right (Pell.FiniteBranch.pellNumerator stage) (Pell.FiniteBranch.pellDifference stage))

/-- Every finite Pell denominator-minus-numerator difference is positive. -/
theorem pellDifference_pos (stage : Nat) : 0 < Pell.FiniteBranch.pellDifference stage := by
  exact (Nat.zero_le (2 * Pell.FiniteBranch.pellNumerator stage)).trans_lt
    (Pell.FiniteBranch.pellDifference_bounds stage).1

/-- Every finite Pell denominator is positive. -/
theorem pellDenominator_pos (stage : Nat) : 0 < Pell.FiniteBranch.pellDenominator stage := by
  unfold Pell.FiniteBranch.pellDenominator
  exact (Pell.FiniteBranch.pellNumerator_pos stage).trans_le
    (Nat.le_add_right (Pell.FiniteBranch.pellNumerator stage) (Pell.FiniteBranch.pellDifference stage))

/-- Every next finite Pell denominator strictly exceeds three times the current denominator.

The subtraction-free recurrence adds the original positive difference to
three times the original denominator. This gives uniform multiplicative
growth without introducing a limit or an irrational parameter.
-/
theorem three_mul_pellDenominator_lt_succ (stage : Nat) :
    3 * pellDenominator stage < pellDenominator (stage + 1) := by
  have differencePositive := pellDifference_pos stage
  unfold pellDenominator
  rewrite [pellNumerator_succ, pellDifference_succ]
  calc
    3 * (pellNumerator stage + pellDifference stage) =
        3 * pellNumerator stage + 3 * pellDifference stage := by ring1
    _ < 3 * pellNumerator stage + 3 * pellDifference stage + pellDifference stage := by
      have shifted := Nat.add_lt_add_left differencePositive
        (3 * pellNumerator stage + 3 * pellDifference stage)
      simpa only [Nat.add_zero] using shifted
    _ = _ := by ring1

end

/-- Squaring preserves a strict natural-number comparison.  The direct
finite proof avoids the generic upstream order lemma's quotient-bearing
inheritance route. -/
theorem natMulSelf_lt_natMulSelf {left right : Nat}
    (less : left < right) : left * left < right * right := by
  cases left with
  | zero =>
      simpa only [Nat.zero_mul] using
        Nat.mul_pos (Nat.zero_lt_of_lt less) (Nat.zero_lt_of_lt less)
  | succ left =>
      exact
        (Nat.mul_lt_mul_of_pos_left less (Nat.succ_pos left)).trans
          (Nat.mul_lt_mul_of_pos_right less (Nat.zero_lt_of_lt less))

open Purelib.NumberTheory
/-- Denominators in the displayed family exceed the recursion index, giving
a direct finite witness above every supplied natural scale. -/
theorem stage_lt_pellDenominator (stage : Nat) :
    stage < Pell.FiniteBranch.pellDenominator stage := by
  have numeratorGrowth : stage < Pell.FiniteBranch.pellNumerator stage := by
    induction stage with
    | zero => decide
    | succ stage inductionHypothesis =>
        rw [Pell.FiniteBranch.pellNumerator_succ]
        have differencePositive := Pell.FiniteBranch.pellDifference_pos stage
        exact (Nat.succ_le_of_lt inductionHypothesis).trans_lt (by
          simpa only [Nat.add_zero] using
            Nat.add_lt_add_left differencePositive (Pell.FiniteBranch.pellNumerator stage))
  unfold Pell.FiniteBranch.pellDenominator
  exact numeratorGrowth.trans_le
    (Nat.le_add_right (Pell.FiniteBranch.pellNumerator stage) (Pell.FiniteBranch.pellDifference stage))

/-- The usual Pell equation, written without natural subtraction. -/
theorem pellEquation (stage : Nat) :
    Pell.FiniteBranch.pellNumerator stage ^ 2 + Pell.FiniteBranch.pellDenominator stage ^ 2 =
      4 * Pell.FiniteBranch.pellNumerator stage * Pell.FiniteBranch.pellDenominator stage + 1 := by
  calc
    Pell.FiniteBranch.pellNumerator stage ^ 2 + Pell.FiniteBranch.pellDenominator stage ^ 2 =
        2 * Pell.FiniteBranch.pellNumerator stage ^ 2 +
          2 * Pell.FiniteBranch.pellNumerator stage * Pell.FiniteBranch.pellDifference stage +
            Pell.FiniteBranch.pellDifference stage ^ 2 := by
      unfold Pell.FiniteBranch.pellDenominator
      ring1
    _ = 4 * Pell.FiniteBranch.pellNumerator stage ^ 2 +
        4 * Pell.FiniteBranch.pellNumerator stage * Pell.FiniteBranch.pellDifference stage + 1 := by
      rw [Pell.FiniteBranch.pellDifference_sq]
      ring1
    _ = 4 * Pell.FiniteBranch.pellNumerator stage * Pell.FiniteBranch.pellDenominator stage + 1 := by
      unfold Pell.FiniteBranch.pellDenominator
      ring1
end Purelib.NumberTheory.Pell.FiniteBranch

end
