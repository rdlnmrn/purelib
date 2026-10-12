module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Exponential.Horner.Basic
import Purelib.Approximation.Gaussian.Exponential.Horner.Bounds
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
public import Purelib.Approximation.Gaussian.Exponential.Taylor.Integral
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.RationalEmbedding.Bounds
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Polynomial.Ascending.Gaussian.Integral
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Exponential

open Purelib.Approximation.Gaussian.Exponential.Horner

open Purelib.Approximation.Gaussian.Exponential.Taylor

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Polynomial.Ascending.Gaussian

section
@[expose] public section

/-!
# Exact integration and finite reading bounds for exponential polynomials

`polynomial n` has degree `n+1`, matching the existing finite Horner sample
at index `n`.  Its integral has the next sample index.  All statements concern
displayed coefficient lists and rational points, not a completed exponential.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Taylor.Integral.Bounds

/-- Later Gaussian exponential polynomial readings on the rational unit interval stay within the earlier index's
scale-ten quarter-radius allowance. -/
theorem later_reading_close {earlier later :
  Nat} (order : earlier ≤ later)
    {parameter : Fraction.Rational} (nonnegative : 0 ≤ parameter) (bounded : parameter ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (Evaluation.eval (Integral.polynomial later) ⟨parameter, 0⟩ -
      Evaluation.eval (Integral.polynomial earlier) ⟨parameter, 0⟩) ≤ Geometric.Basic.quarterRadius 10 earlier := by
  rw [Integral.eval_polynomial, Integral.eval_polynomial]
  have unit : Data.Gaussian.Norm.Basic.normSq
      (⟨parameter, 0⟩ : Canonical) ≤ 1 := by
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact RationalEmbedding.Bounds.unit_parameter nonnegative bounded
  exact Sample.sample_later_close
    (⟨parameter, 0⟩ : Canonical) unit
    (earlier := earlier) (later := later) order

/-- Later integrals of the finite exponential polynomials over the unit interval stay within the earlier index's
scale-ten quarter-radius allowance. -/
theorem integral_later_close {earlier later :
  Nat} (order : earlier ≤ later) :
    Data.Gaussian.Norm.Basic.normSq (Integral.definiteIntegral (Integral.polynomial later) 0 1 -
      Integral.definiteIntegral (Integral.polynomial earlier) 0 1) ≤ Geometric.Basic.quarterRadius 10 earlier := by
  rw [Integral.integral_polynomial, Integral.integral_polynomial]
  have cancellation :
      Sample.sample 1 (later + 1) - 1 - (Sample.sample 1 (earlier + 1) - 1) =
        Sample.sample 1 (later + 1) - Sample.sample 1 (earlier + 1) := by ring1
  rw [cancellation]
  exact (Sample.sample_later_close 1 (by decide) (Nat.add_le_add_right order 1)).trans
    (quarterRadius_antitone (by decide : (0 : Fraction.Rational) ≤ 10) (Nat.le_succ earlier))

/-- Every finite exponential polynomial integral over the unit interval has squared norm at most twenty-two. -/
theorem integral_bounded (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Integral.definiteIntegral (Integral.polynomial index) 0 1) ≤ 22 := by
  rw [Integral.integral_polynomial]
  calc
    Data.Gaussian.Norm.Basic.normSq (Sample.sample 1 (index + 1) - 1) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq (Sample.sample 1 (index + 1)) +
          Data.Gaussian.Norm.Basic.normSq (1 : Canonical)) :=
      Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _
    _ ≤ 2 * (10 + 1) := by
      rw [Data.Gaussian.Norm.Basic.normSq_one]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (Sample.sample_bounded 1 (by decide) (index + 1)) le_rfl) (by decide)
    _ = 22 := by decide

/-- The real coordinate of the exact exponential integral reading is one plus half its shifted inner Horner value. -/
theorem integral_reading_re (index : Nat) :
    (Sample.sample 1 (index + 1) - 1).re =
      1 + (1 / 2 : Fraction.Rational) * (Horner.Basic.horner 1 3 index).re := by
  simp only [Sample.sample, Basic.horner_succ, Horner.Basic.step_eq,
    _root_.one_mul, Basic.add_re, Basic.sub_re, Basic.one_re, Scale.scale_re]
  change (1 + (1 / (1 : Fraction.Rational)) *
    (1 + (1 / (2 : Fraction.Rational)) * (Horner.Basic.horner 1 3 index).re)) - 1 = _
  rw [show (1 / (1 : Fraction.Rational)) = 1 from by decide]
  ring1

/-- Even the first integrated truncation is at least `3/2`; this supplies a small symbolic certificate for the real
controller's first decision. -/
theorem integral_norm_lower (index : Nat) :
    (9 / 4 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (Sample.sample 1 (index + 1) - 1) := by
  have realLower : (3 / 2 : Fraction.Rational) ≤ (Sample.sample 1 (index + 1) - 1).re := by
    rw [integral_reading_re]
    calc
      3 / 2 = (1 : Fraction.Rational) + (1 / 2) * 1 := by decide
      _ ≤ 1 + (1 / 2 : Fraction.Rational) * (Horner.Basic.horner 1 3 index).re :=
        add_le_add le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Horner.Bounds.horner_one_re_lower index 3) (by decide))
  have squareLower := Fraction.Order.Arithmetic.pow_le_pow_direct
    (show (0 : Fraction.Rational) ≤ 3 / 2 from by decide) realLower 2
  calc
    9 / 4 = (3 / 2 : Fraction.Rational) ^ 2 := by decide
    _ ≤ (Sample.sample 1 (index + 1) - 1).re ^ 2 := squareLower
    _ = (Sample.sample 1 (index + 1) - 1).re ^ 2 + 0 := by ring1
    _ ≤ Data.Gaussian.Norm.Basic.normSq (Sample.sample 1 (index + 1) - 1) :=
      add_le_add le_rfl (Fraction.Order.Arithmetic.sq_nonneg_direct _)
end Purelib.Approximation.Gaussian.Exponential.Taylor.Integral.Bounds

end
