module
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Projective.Homography.Norm
public import Purelib.Geometry.Projective.Homography.Polynomial
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Projective

open Purelib.LinearAlgebra.Coordinates2.Matrix

open Purelib.Polynomial

section
@[expose] public section

/-!
# Bounded finite charts for CCL branch boundaries

Circle boundaries use the primary and reciprocal stereographic charts on the
fixed rational cell `[-1,1]`.  Coordinate-line boundaries use one symmetric
cell whose radius is computed from a coefficient majorant for the affine
numerator and an explicitly supplied positive lower bound for the affine
denominator.  Each chart is immediately sent through the finite cleared-gcd
and Sturm event classifier.
-/

namespace Purelib.Geometry.Projective.Homography

/-- Coefficient-computed upper bound for the squared norm of a decoded point throughout a box with the displayed
denominator lower bound. -/
def decodedNormMajorant
    (matrix : GaussianMatrix) (box : Rational.Box) (denominatorMargin :
      Fraction.Rational) :
    Fraction.Rational :=
  Dense.Gaussian.Bounds.Box.denseEvalNormMajorant
      (Homography.affineNumeratorPolynomial matrix) box /
    denominatorMargin

/-- A positive denominator margin gives a positive decoded norm majorant. -/
theorem decodedNormMajorant_pos
    (matrix : GaussianMatrix) (box : Rational.Box) {denominatorMargin :
      Fraction.Rational}
    (marginPositive : 0 < denominatorMargin) :
    0 < decodedNormMajorant matrix box denominatorMargin :=
  Fraction.Order.Field.div_pos_direct
    (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos
      (Homography.affineNumeratorPolynomial matrix) box)
    marginPositive

/-- The rational homographic value is uniformly norm-bounded on the box once its denominator has the supplied positive
lower bound. -/
theorem normSq_homographic_le_decodedNormMajorant
    (matrix : GaussianMatrix) (box : Rational.Box) {denominatorMargin :
      Fraction.Rational}
    (marginPositive : 0 < denominatorMargin) {value : Data.Gaussian.Basic.Canonical}
    (inside : box.Contains value)
    (denominatorLower : denominatorMargin ≤
      Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value)) :
    Data.Gaussian.Norm.Basic.normSq (Homography.Basic.homographic matrix value) ≤
      decodedNormMajorant matrix box denominatorMargin := by
  let denominatorNorm :=
    Data.Gaussian.Norm.Basic.normSq (Homography.Basic.denominator matrix value)
  let numeratorNorm :=
    Data.Gaussian.Norm.Basic.normSq (Homography.Basic.numerator matrix value)
  let majorant :=
    Dense.Gaussian.Bounds.Box.denseEvalNormMajorant
      (Homography.affineNumeratorPolynomial matrix) box
  have denominatorPositive : 0 < denominatorNorm :=
    marginPositive.trans_le denominatorLower
  have denominatorNonzero :
      Homography.Basic.denominator matrix value ≠ 0 := by
    intro zero
    change 0 < Data.Gaussian.Norm.Basic.normSq
      (Homography.Basic.denominator matrix value) at denominatorPositive
    rw [zero, Data.Gaussian.Norm.Basic.normSq_zero] at denominatorPositive
    exact (lt_irrefl 0 denominatorPositive).elim
  have numeratorBound : numeratorNorm ≤ majorant := by
    simpa only [numeratorNorm, Homography.eval_affineNumeratorPolynomial] using
      Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormMajorant
        (Homography.affineNumeratorPolynomial matrix) inside
  have sameDenominator : numeratorNorm / denominatorNorm ≤
      majorant / denominatorNorm := by
    apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
    calc
      numeratorNorm ≤ majorant := numeratorBound
      _ = majorant / denominatorNorm * denominatorNorm :=
        (Fraction.Field.div_mul_cancel_of_ne majorant
          denominatorNorm denominatorPositive.ne').symm
  have majorantNonnegative : 0 ≤ majorant :=
    (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos
      (Homography.affineNumeratorPolynomial matrix) box).le
  have largerDenominator : majorant / denominatorNorm ≤
      majorant / denominatorMargin :=
    Fraction.Order.Field.div_le_div_of_nonneg_left_direct
      majorantNonnegative marginPositive denominatorLower
  rw [Homography.normSq_homographic matrix value
    denominatorNonzero]
  change numeratorNorm * denominatorNorm⁻¹ ≤ _
  simpa only [Algebra.Field.ExplicitField.div_eq_mul_inv, decodedNormMajorant,
    numeratorNorm, denominatorNorm, majorant] using
      sameDenominator.trans largerDenominator

/-- Positive symmetric radius for the single coordinate-line chart. Adding one avoids a square root while retaining a
direct parameter bound. -/
def lineParameterRadius
    (matrix : GaussianMatrix) (box : Rational.Box) (denominatorMargin :
      Fraction.Rational) :
    Fraction.Rational :=
  decodedNormMajorant matrix box denominatorMargin + 1

/-- A positive denominator margin gives a positive coordinate-line chart radius. -/
theorem lineParameterRadius_pos
    (matrix : GaussianMatrix) (box : Rational.Box) {denominatorMargin :
      Fraction.Rational}
    (marginPositive : 0 < denominatorMargin) :
    0 < lineParameterRadius matrix box denominatorMargin := by
  let majorant := decodedNormMajorant matrix box denominatorMargin
  have majorantPositive : 0 < majorant :=
    decodedNormMajorant_pos matrix box marginPositive
  have addOne := Fraction.Order.Arithmetic.add_lt_add_left_direct
    (show (0 : Fraction.Rational) < 1 by decide) majorant
  calc
    0 < majorant := majorantPositive
    _ = majorant + 0 := by ring1
    _ < majorant + 1 := addOne
    _ = lineParameterRadius matrix box denominatorMargin := rfl
end Purelib.Geometry.Projective.Homography

end
