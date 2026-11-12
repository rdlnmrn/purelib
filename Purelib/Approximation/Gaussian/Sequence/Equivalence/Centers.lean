module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Approximation

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite comparison of centres enclosing equivalent names

Uniform rational enclosures of operationally equivalent finite samplers
bound the separation of their centres.  The proof does not select a common
completed value: any proposed rational violation supplies one positive
comparison request which contradicts that violation.
-/

namespace Purelib.Approximation.Gaussian.Sequence.Equivalence.Centers

/-- The ordinary two-error squared triangle bound, with no extra slack for operational comparison and no assumption that
either allowance is positive. -/
theorem separation_le {left right :
  ApproximationData}
    (equivalent : Equivalence.Equivalent left right)
    (leftCenter rightCenter : Data.Gaussian.Basic.Canonical) (leftAllowance rightAllowance : Fraction.Rational)
    (leftBound : ∀ index, Basic.normSq (left.sample index - leftCenter) ≤ leftAllowance)
    (rightBound : ∀ index, Basic.normSq (right.sample index - rightCenter) ≤ rightAllowance)
      :
    Basic.normSq (leftCenter - rightCenter) ≤ 2 * (leftAllowance + rightAllowance) := by
  by_cases bounded : Basic.normSq (leftCenter - rightCenter) ≤ 2 * (leftAllowance +
    rightAllowance)
  · exact bounded
  · have strict := Arithmetic.lt_of_not_ge_direct bounded
    let margin := Basic.normSq (leftCenter - rightCenter) - 2 * (leftAllowance +
      rightAllowance)
    have marginPositive : 0 < margin := Arithmetic.sub_pos_direct strict
    have allowanceNonnegative : 0 ≤ 2 * (leftAllowance + rightAllowance) :=
      Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg ((Basic.normSq_nonneg _).trans (leftBound 0))
          ((Basic.normSq_nonneg _).trans (rightBound 0)))
    have centerPositive : 0 < Basic.normSq (leftCenter - rightCenter) :=
      allowanceNonnegative.trans_lt strict
    let target := margin ^ 2 / (4 * Basic.normSq (leftCenter - rightCenter))
    have targetPositive : 0 < target :=
      Field.div_pos_direct
        (Arithmetic.pow_pos_direct marginPositive 2)
        (Arithmetic.mul_pos_direct (by decide) centerPositive)
    let comparison := equivalent.compare 0 0 target targetPositive
    let leftReading := left.sample comparison.leftIndex
    let rightReading := right.sample comparison.rightIndex
    have errorBound : Basic.normSq ((leftReading - leftCenter) - (rightReading -
      rightCenter)) ≤
        2 * (leftAllowance + rightAllowance) :=
      (Bounds.normSq_sub_le_two _ _).trans
        (Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add (leftBound _) (rightBound _)) (by decide))
    have gap : margin ≤ Basic.normSq (leftCenter - rightCenter) -
        Basic.normSq ((leftReading - leftCenter) - (rightReading - rightCenter)) :=
      Arithmetic.sub_le_sub_left_direct errorBound _
    have lower := Bounds.normSq_add_lower_of_gap marginPositive gap
    have recombine : (leftCenter - rightCenter) +
        ((leftReading - leftCenter) - (rightReading - rightCenter)) =
          leftReading - rightReading := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.sub_re,
          Data.Gaussian.Basic.sub_im] <;> ring1
    rw [recombine] at lower
    have upper := comparison.close (Nat.le_refl _) (Nat.le_refl _)
    exact (not_lt_of_ge lower upper).elim
end Purelib.Approximation.Gaussian.Sequence.Equivalence.Centers

end
