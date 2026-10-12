module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Approximation.Gaussian.Exponential.Horner.Taylor
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
public import Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial
import Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Majorant
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Geometric.Bounds
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
import Purelib.Polynomial.Ascending.Rational.Geometric
import Purelib.Polynomial.Ascending.Rational.Geometric.Cayley

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
public section

/-! Approximation Gaussian Logarithm Local Inverse Polynomial Error and its finite structural certificates. -/

namespace Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Logarithm.Local.Inverse
open Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial
open Purelib.Data.Rat
open Purelib.Polynomial.Ascending.Rational
open Purelib.Polynomial.Ascending.Rational.Geometric

/-- The rational squared-error coefficient combining the finite composition tail and geometric-chart remainder. -/
@[expose] public def expLogErrorScale : Fraction.Rational := 2 * (5 * 10 + 3 * 3)

/-- The exponential–local-logarithm error coefficient is nonnegative. -/
theorem expLogErrorScale_nonnegative : 0 ≤
  Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error.expLogErrorScale :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (by decide))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (by decide)))

/-- On the one-ninth quadrance disk, the finite exponential–logarithm composition approximates the Cayley chart with the
displayed geometric squared-error bound. -/
theorem exponentialLocalLog_chart_error {z : Data.Gaussian.Basic.Canonical}
    (zBound : Data.Gaussian.Norm.Basic.normSq z ≤ 1 / 9) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      (GaussianEvaluation.eval (Polynomial.exponentialLocalLog (2 * depth + 2) depth) z -
        (1 + z) / (1 - z)) ≤
      Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error.expLogErrorScale * (1 / 4 : Fraction.Rational) ^
        depth := by
  let polynomialValue :=
    GaussianEvaluation.eval (Polynomial.exponentialLocalLog (2 * depth + 2) depth) z
  let prefixValue := GaussianEvaluation.eval (Geometric.geometricPrefix (2 * depth + 2)) z
  let chartValue := (1 + z) / (1 - z)
  have split : polynomialValue - chartValue =
      (polynomialValue - prefixValue) + (prefixValue - chartValue) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.sub_re,
        Data.Gaussian.Basic.sub_im] <;> ring1
  rw [split]
  have highBound := Majorant.exponentialLocalLog_highTail_bound zBound depth
  have chartBound := Cayley.geometricPrefix_chart_error zBound (2 * depth + 2)
  have ninthToFour :
      (1 / 9 : Fraction.Rational) ^ (2 * depth + 3) ≤
        (4 / 9 : Fraction.Rational) ^ (2 * depth + 3) :=
    Fraction.Order.Arithmetic.pow_le_pow_direct (by decide) (by decide) _
  calc
    Data.Gaussian.Norm.Basic.normSq ((polynomialValue - prefixValue) +
        (prefixValue - chartValue)) ≤
      2 * (Data.Gaussian.Norm.Basic.normSq (polynomialValue - prefixValue) +
        Data.Gaussian.Norm.Basic.normSq (prefixValue - chartValue)) :=
          Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 *
        ((5 * 10) * (4 / 9 : Fraction.Rational) ^ (2 * depth + 3) +
          9 * (1 / 9 : Fraction.Rational) ^ (2 * depth + 3)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add highBound chartBound) (by decide)
    _ ≤ 2 *
        ((5 * 10) * (4 / 9 : Fraction.Rational) ^ (2 * depth + 3) +
          9 * (4 / 9 : Fraction.Rational) ^ (2 * depth + 3)) := by
      apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
        (by decide)
      exact add_le_add le_rfl
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          ninthToFour (by decide))
    _ = Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error.expLogErrorScale *
          (4 / 9 : Fraction.Rational) ^ (2 * depth + 3) := by
      rw [show (9 : Fraction.Rational) = 3 * 3 by decide]
      dsimp only [Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error.expLogErrorScale]
      ring1
    _ ≤ Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error.expLogErrorScale * (1 / 4 : Fraction.Rational) ^
      depth :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Geometric.Bounds.fourNinth_depth_bound depth)
        Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error.expLogErrorScale_nonnegative

/-! Approximation Gaussian Logarithm Local Inverse Polynomial Error and its finite structural certificates. -/

/-- Evaluate the local logarithm at the given depth and its exponential at twice that depth plus one. -/
@[expose] public def localExpLogSample (z : Data.Gaussian.Basic.Canonical) (depth : Nat) : Data.Gaussian.Basic.Canonical
  :=
  Exponential.Horner.Sample.sample
    (Logarithm.Local.Horner.Sample.sample z depth) (2 * depth + 1)

/-- The synchronized nested Horner sample equals evaluation of the finite composed polynomial. -/
theorem localExpLogSample_eq_eval (z : Data.Gaussian.Basic.Canonical) (depth : Nat) :
    Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error.localExpLogSample z depth =
      GaussianEvaluation.eval (Polynomial.exponentialLocalLog (2 * depth + 2) depth) z := by
  rw [Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error.localExpLogSample,
    Exponential.Horner.Taylor.sample_eq_truncatedExp,
    Polynomial.eval_exponentialLocalLog]

/-- The synchronized exponential–logarithm sample approximates the Cayley chart on the one-ninth quadrance disk with the
retained geometric squared-error bound. -/
theorem localExpLogSample_chart_error {z : Data.Gaussian.Basic.Canonical}
    (zBound : Data.Gaussian.Norm.Basic.normSq z ≤ 1 / 9) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      (Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error.localExpLogSample z depth - (1 + z) / (1 - z)) ≤
      Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error.expLogErrorScale * (1 / 4 : Fraction.Rational) ^
        depth := by
  rw [Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error.localExpLogSample_eq_eval]
  exact Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error.exponentialLocalLog_chart_error zBound depth
end Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error

end
