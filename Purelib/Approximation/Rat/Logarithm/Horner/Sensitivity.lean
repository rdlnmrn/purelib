module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rat.Logarithm.Horner.Basic
import Purelib.Approximation.Rat.Logarithm.Horner.Bounds
public import Purelib.Approximation.Rat.Logarithm.Horner.Sample
import Purelib.Approximation.Rat.Logarithm.Reduction
import Purelib.Approximation.Rat.Logarithm.Reduction.Sensitivity
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rat.Logarithm

open Purelib.Approximation.Rat.Logarithm.Horner

open Purelib.Approximation.Rat.Logarithm.Horner.Basic

open Purelib.Approximation.Rat.Logarithm.Reduction

open Purelib.Data.Rat

section
public section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

namespace Purelib.Approximation.Rat.Logarithm.Horner.Sensitivity

/-- At a positive index, the shared logarithm Horner coefficient has square at most one. -/
theorem coefficient_sq_le_one {index : Nat} (positive : 1 ≤ index) :
    ComplexLog.coefficient index ^ 2 ≤ 1 := by
  have squared := Fraction.Order.Arithmetic.pow_le_pow_direct
    (ComplexLog.coefficient_nonneg positive) (ComplexLog.coefficient_le_one index) 2
  simpa only [one_pow] using squared
end Purelib.Approximation.Rat.Logarithm.Horner.Sensitivity

end

section
public section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

namespace Purelib.Approximation.Rat.Logarithm.Horner.Sensitivity

/-- The difference between logarithm Horner steps separates argument change from retained-tail change. -/
theorem step_inputs_sub (w v : Fraction.Rational) (index : Nat)
    (wTail vTail : Fraction.Rational) :
    Horner.Basic.step w index wTail - Horner.Basic.step v index vTail =
      Log.coefficient index * ((w - v) * wTail + v * (wTail - vTail)) := by
  rw [Horner.Basic.step_eq, Horner.Basic.step_eq]
  ring1

/-- The rational squared-input sensitivity constant sixteen for the finite logarithm Horner recurrence. -/
@[expose] def hornerInputScale : Fraction.Rational := 16

/-- Equal-depth logarithm Horner values have squared difference at most sixteen times the squared argument difference.

Both reduced arguments lie between zero and one ninth, and the starting coefficient index is positive. -/
theorem horner_input_close {w v : Fraction.Rational}
    (wNonnegative : 0 ≤ w) (wLe : w ≤ 1 / 9)
    (vNonnegative : 0 ≤ v) (vLe : v ≤ 1 / 9) :
    ∀ (depth index : Nat), 1 ≤ index →
      (Horner.Basic.horner w index depth - Horner.Basic.horner v index depth) ^ 2 ≤
        Approximation.Rat.Logarithm.Horner.Sensitivity.hornerInputScale * (w - v) ^ 2
  | 0, _, _ => by
      rw [Horner.Basic.horner_zero, Horner.Basic.horner_zero]
      change (0 : Fraction.Rational) ^ 2 ≤ Approximation.Rat.Logarithm.Horner.Sensitivity.hornerInputScale * (w - v) ^ 2
      exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.sq_nonneg_direct (w - v))
  | depth + 1, index, positive => by
      rw [Horner.Basic.horner_succ, Horner.Basic.horner_succ,
        Approximation.Rat.Logarithm.Horner.Sensitivity.step_inputs_sub]
      rw [show (Log.coefficient index * ((w - v) * Horner.Basic.horner w (index + 1) depth +
        v * (Horner.Basic.horner w (index + 1) depth - Horner.Basic.horner v (index + 1) depth))) ^ 2 =
        Log.coefficient index ^ 2 * ((w - v) * Horner.Basic.horner w (index + 1) depth +
        v * (Horner.Basic.horner w (index + 1) depth - Horner.Basic.horner v (index + 1) depth)) ^ 2 by ring1]
      let wTail := Horner.Basic.horner w (index + 1) depth
      let vTail := Horner.Basic.horner v (index + 1) depth
      let differenceSq := (w - v) ^ 2
      have wTailBounds := Horner.Bounds.horner_bounds wNonnegative wLe depth (index + 1)
        (by omega)
      have wTailSq : wTail ^ 2 ≤ 4 := by
        have squared := Fraction.Order.Arithmetic.pow_le_pow_direct
          ((by decide : (0 : Fraction.Rational) ≤ 1).trans wTailBounds.1)
          wTailBounds.2 2
        simpa only [wTail] using (squared.trans_eq (by decide))
      have tailDifference : (wTail - vTail) ^ 2 ≤
          Approximation.Rat.Logarithm.Horner.Sensitivity.hornerInputScale * differenceSq :=
        Purelib.Approximation.Rat.Logarithm.Horner.Sensitivity.horner_input_close wNonnegative wLe vNonnegative vLe
          depth
          (index + 1) (by omega)
      have vSq : v ^ 2 ≤ 1 / 4 := by
        calc
          v ^ 2 ≤ (1 / 9 : Fraction.Rational) ^ 2 :=
            Fraction.Order.Arithmetic.pow_le_pow_direct vNonnegative vLe 2
          _ ≤ 1 / 4 := by decide
      have firstBound : ((w - v) * wTail) ^ 2 ≤ 4 * differenceSq := by
        rw [show ((w - v) * wTail) ^ 2 = (w - v) ^ 2 * wTail ^ 2 by ring1]
        have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          wTailSq (Fraction.Order.Arithmetic.sq_nonneg_direct (w - v))
        simpa only [differenceSq] using (show
          (w - v) ^ 2 * wTail ^ 2 ≤ (w - v) ^ 2 * 4 from scaled).trans_eq
            (by ring1)
      have secondBound : (v * (wTail - vTail)) ^ 2 ≤
          4 * differenceSq := by
        rw [show (v * (wTail - vTail)) ^ 2 = v ^ 2 * (wTail - vTail) ^ 2 by ring1]
        calc
          v ^ 2 * (wTail - vTail) ^ 2 ≤
              (1 / 4 : Fraction.Rational) *
                (Approximation.Rat.Logarithm.Horner.Sensitivity.hornerInputScale * differenceSq) :=
            Fraction.Order.Arithmetic.mul_le_mul_direct vSq tailDifference
              (Fraction.Order.Arithmetic.sq_nonneg_direct (wTail - vTail))
              (by decide)
          _ = 4 * differenceSq := by
            rw [Approximation.Rat.Logarithm.Horner.Sensitivity.hornerInputScale]
            calc
              (1 / 4 : Fraction.Rational) * (16 * differenceSq) =
                  ((1 / 4 : Fraction.Rational) * 16) * differenceSq := by ring1
              _ = 4 * differenceSq := by
                rw [show (1 / 4 : Fraction.Rational) * 16 = 4 by decide]
      have sumBound :
          ((w - v) * wTail + v * (wTail - vTail)) ^ 2 ≤
            Approximation.Rat.Logarithm.Horner.Sensitivity.hornerInputScale * differenceSq := by
        calc
          ((w - v) * wTail + v * (wTail - vTail)) ^ 2 ≤
              2 * (((w - v) * wTail) ^ 2 +
                (v * (wTail - vTail)) ^ 2) := Bounds.Square.sq_add_le_two _ _
          _ ≤ 2 * (4 * differenceSq + 4 * differenceSq) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (add_le_add firstBound secondBound) (by decide)
          _ = Approximation.Rat.Logarithm.Horner.Sensitivity.hornerInputScale * differenceSq := by
            rw [Approximation.Rat.Logarithm.Horner.Sensitivity.hornerInputScale]
            ring1
      have multiplied := Fraction.Order.Arithmetic.mul_le_mul_direct
        (Approximation.Rat.Logarithm.Horner.Sensitivity.coefficient_sq_le_one positive) sumBound
        (Fraction.Order.Arithmetic.sq_nonneg_direct
          ((w - v) * wTail + v * (wTail - vTail)))
        (by decide : (0 : Fraction.Rational) ≤ 1)
      simpa only [Fraction.Field.one_mul,
        ComplexLog.coefficient] using multiplied

/-- For inputs at least one half, logarithm output factors have squared difference at most four times the squared input
difference. -/
theorem outputFactor_sub_sq_le {x y : Fraction.Rational}
    (xHalf : 1 / 2 ≤ x) (yHalf : 1 / 2 ≤ y) :
    (Sample.outputFactor x - Sample.outputFactor y) ^ 2 ≤ 4 * (x - y) ^ 2 := by
  have argumentDifference := Reduction.Sensitivity.reducedArgument_sub_sq_le xHalf yHalf
  rw [Sample.outputFactor, Sample.outputFactor]
  have identity : 2 * Reduction.reducedArgument x - 2 * Reduction.reducedArgument y =
      2 * (Reduction.reducedArgument x - Reduction.reducedArgument y) := by ring1
  rw [identity]
  rw [show (2 * (Reduction.reducedArgument x - Reduction.reducedArgument y)) ^ 2 =
    (2 : Fraction.Rational) ^ 2 * (Reduction.reducedArgument x - Reduction.reducedArgument y) ^ 2 by ring1]
  have twoSq : (2 : Fraction.Rational) ^ 2 = 4 := by decide
  rw [twoSq]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    argumentDifference (by decide)

/-- The rational logarithm sample sensitivity constant combining two contributions of sixteen. -/
@[expose] def sampleInputScale : Fraction.Rational := 2 * (16 + 16)
end Purelib.Approximation.Rat.Logarithm.Horner.Sensitivity

end
