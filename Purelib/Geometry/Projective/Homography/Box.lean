module
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Projective

open Purelib.Geometry.Rational.Box.Square

open Purelib.Geometry.Rational.Box.Square.Centered

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
@[expose] public section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

namespace Purelib.Geometry.Projective.Homography.Box

/-! ## Generic finite homographic box transport -/

/-- Computed squared-norm upper bound for the affine numerator `a t + b` on a rational tail box. -/
def numeratorNormSqBound (matrix :
  GaussianMatrix) (tailBox : Rational.Box) : Fraction.Rational :=
  2 * (Data.Gaussian.Norm.Basic.normSq matrix.a * tailBox.normSqBound +
    Data.Gaussian.Norm.Basic.normSq matrix.b)

/-- The computed affine numerator squared-norm bound is nonnegative. -/
theorem numeratorNormSqBound_nonneg (matrix :
  GaussianMatrix) (tailBox : Rational.Box) :
    0 ≤ numeratorNormSqBound matrix tailBox := by
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Data.Gaussian.Norm.Basic.normSq_nonneg matrix.a) tailBox.normSqBound_nonneg)
      (Data.Gaussian.Norm.Basic.normSq_nonneg matrix.b))

/-- Every point in the tail box satisfies the computed affine numerator bound. -/
theorem numerator_normSq_le
    (matrix : GaussianMatrix) {tailBox : Rational.Box} {tail :
      Data.Gaussian.Basic.Canonical}
    (inside : tailBox.Contains tail) :
    Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix tail) ≤
      numeratorNormSqBound matrix tailBox := by
  calc
    Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix tail) =
      Data.Gaussian.Norm.Basic.normSq (matrix.a * tail + matrix.b) := rfl
    _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (matrix.a * tail) + Data.Gaussian.Norm.Basic.normSq
      matrix.b) :=
      Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ = 2 * (Data.Gaussian.Norm.Basic.normSq matrix.a * Data.Gaussian.Norm.Basic.normSq tail +
      Data.Gaussian.Norm.Basic.normSq matrix.b) := by
      rw [Data.Gaussian.Norm.Basic.normSq_mul]
    _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq matrix.a * tailBox.normSqBound +
      Data.Gaussian.Norm.Basic.normSq matrix.b) := by
      apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      · exact add_le_add_left
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (tailBox.normSq_le_normSqBound inside) (Data.Gaussian.Norm.Basic.normSq_nonneg matrix.a)) _
      · decide
    _ = numeratorNormSqBound matrix tailBox := rfl

/-- Squared-norm bound for the homographic output after applying the supplied positive denominator margin. -/
def homographicNormSqBound (matrix :
  GaussianMatrix) (tailBox : Rational.Box)
    (denominatorMargin : Fraction.Rational) : Fraction.Rational :=
  numeratorNormSqBound matrix tailBox / denominatorMargin

/-- A positive denominator margin makes the homographic squared-norm bound nonnegative. -/
theorem homographicNormSqBound_nonneg
    (matrix : GaussianMatrix) (tailBox : Rational.Box) {denominatorMargin :
      Fraction.Rational}
    (marginPositive : 0 < denominatorMargin) :
    0 ≤ homographicNormSqBound matrix tailBox denominatorMargin :=
  Fraction.Order.Field.div_nonneg_direct
    (numeratorNormSqBound_nonneg matrix tailBox) marginPositive.le

/-- Square-root-free half-width used by the generic transport box. -/
def homographicRadius (matrix : GaussianMatrix)
  (tailBox : Rational.Box)
    (denominatorMargin : Fraction.Rational) : Fraction.Rational :=
  homographicNormSqBound matrix tailBox denominatorMargin + 1

/-- The computed transport radius is nonnegative for a positive denominator margin. -/
theorem homographicRadius_nonneg
    (matrix : GaussianMatrix) (tailBox : Rational.Box) {denominatorMargin :
      Fraction.Rational}
    (marginPositive : 0 < denominatorMargin) :
    0 ≤ homographicRadius matrix tailBox denominatorMargin :=
  add_nonneg
    (homographicNormSqBound_nonneg matrix tailBox marginPositive) (by decide)

/-- A total rational output box computed from a tail box and positive denominator separation. -/
def homographicBox (matrix : GaussianMatrix)
  (tailBox : Rational.Box)
    (denominatorMargin : Fraction.Rational) (marginPositive : 0 < denominatorMargin) :
    Rational.Box :=
  BoxTransport.centeredBox 0 (homographicRadius matrix tailBox denominatorMargin)
    (homographicRadius_nonneg matrix tailBox marginPositive)

/-- Bound the homographic squared norm throughout a tail box.

The supplied positive margin must bound the squared norm of the affine denominator from below at the displayed point. -/
theorem homographic_normSq_le
    (matrix : GaussianMatrix) {tailBox : Rational.Box} {tail :
      Data.Gaussian.Basic.Canonical}
    {denominatorMargin : Fraction.Rational} (inside : tailBox.Contains tail)
    (marginPositive : 0 < denominatorMargin)
    (denominatorLower : denominatorMargin ≤
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix tail)) :
    Data.Gaussian.Norm.Basic.normSq (Homography.Basic.homographic matrix tail) ≤
      homographicNormSqBound matrix tailBox denominatorMargin := by
  have denominatorNormPositive : 0 < Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix tail)
    :=
    marginPositive.trans_le denominatorLower
  have denominatorNonzero : Homography.Basic.denominator matrix tail ≠ 0 := by
    intro zero
    rw [zero, Data.Gaussian.Norm.Basic.normSq_zero] at denominatorNormPositive
    exact (lt_irrefl _ denominatorNormPositive).elim
  have numeratorBound := numerator_normSq_le matrix inside
  have quotientIdentity : Data.Gaussian.Norm.Basic.normSq (Homography.Basic.homographic matrix tail) =
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix tail) /
        Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix tail) := by
    rw [Homography.Basic.homographic, Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Field.inv_eq,
      Data.Gaussian.Field.normSq_inv _ denominatorNonzero]
    rfl
  rw [quotientIdentity]
  have first : Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix tail) /
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix tail) ≤
      numeratorNormSqBound matrix tailBox /
        Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix tail) := by
    apply (Fraction.Order.Field.div_le_iff_pos
      denominatorNormPositive).2
    calc
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix tail) ≤
          numeratorNormSqBound matrix tailBox := numeratorBound
      _ = (numeratorNormSqBound matrix tailBox /
          Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix tail)) *
            Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix tail) :=
        (Fraction.Field.div_mul_cancel_of_ne _ _
          denominatorNormPositive.ne').symm
  exact first.trans
    (Fraction.Order.Field.div_le_div_of_nonneg_left_direct
      (numeratorNormSqBound_nonneg matrix tailBox) marginPositive
      denominatorLower)

/-- Constructive finite rational box transport. Every hypothesis concerns one displayed tail and finite certificates; no
set of compatible tails or completed value is formed. -/
theorem homographicBox_contains
    (matrix : GaussianMatrix) {tailBox : Rational.Box} {tail :
      Data.Gaussian.Basic.Canonical}
    {denominatorMargin : Fraction.Rational} (inside : tailBox.Contains tail)
    (marginPositive : 0 < denominatorMargin)
    (denominatorLower : denominatorMargin ≤
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix tail)) :
    (homographicBox matrix tailBox denominatorMargin marginPositive).Contains
      (Homography.Basic.homographic matrix tail) := by
  let bound := homographicNormSqBound matrix tailBox denominatorMargin
  let radius := homographicRadius matrix tailBox denominatorMargin
  have boundNonnegative : 0 ≤ bound :=
    homographicNormSqBound_nonneg matrix tailBox marginPositive
  have radiusNonnegative : 0 ≤ radius :=
    homographicRadius_nonneg matrix tailBox marginPositive
  have boundLeRadiusSq : bound ≤ radius ^ 2 := by
    have boundLeRadius : bound ≤ radius := le_add_of_nonneg_right (by decide)
    have oneLeRadius : (1 : Fraction.Rational) ≤ radius := by
      exact le_add_of_nonneg_left boundNonnegative
    calc
      bound = bound * 1 := by ring1
      _ ≤ radius * radius :=
        Fraction.Order.Arithmetic.mul_le_mul_direct boundLeRadius oneLeRadius
          (by decide) radiusNonnegative
      _ = radius ^ 2 := by ring1
  unfold homographicBox
  apply Centered.centeredBox_contains_of_normSq_sub_le radiusNonnegative
  have normBound := homographic_normSq_le matrix inside marginPositive
    denominatorLower
  calc
    Data.Gaussian.Norm.Basic.normSq (Homography.Basic.homographic matrix tail - 0) =
        Data.Gaussian.Norm.Basic.normSq (Homography.Basic.homographic matrix tail) := by
      rw [Data.Gaussian.Basic.sub_zero]
    _ ≤ bound := normBound
    _ ≤ radius ^ 2 := boundLeRadiusSq
end Purelib.Geometry.Projective.Homography.Box

end
