module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

public import Purelib.Riemann.Periods.PeriodMatrix

@[expose] public section

/-! Compute canonical inverse clearance from a lower bound valid only beyond a retained threshold. -/
namespace Purelib.Riemann.Integration.ScalarTailLower

open Purelib.Riemann.Periods.PeriodMatrix
open Purelib.LinearAlgebra.Gaussian.QuadraticForm

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Data in
set_option genInjectivity false in
/-- A positive scalar quadrance floor valid from a retained threshold onward.

The floor concerns the canonical scaled inverse of the same named matrix. Samples before the threshold have no
lower-bound requirement. -/
structure ScalarTailLowerCertificate {size : Nat} (matrix : NamedMatrix size) where
  /-- The natural index from which the scalar floor applies. -/ threshold : Nat
  /-- The retained rational lower bound for scalar sample quadrance. -/ lowerSq : Coordinate
  /-- The scalar quadrance lower bound is strictly positive. -/ positive : 0 < lowerSq
  /-- Every sample beyond the threshold satisfies the retained quadrance floor. -/ sample_lower : ∀ index, threshold ≤
    index → lowerSq ≤ Data.Gaussian.Norm.Basic.normSq ((canonicalScaledInverse matrix).scalar.sample index)

constructive_injectivity ScalarTailLowerCertificate

namespace ScalarTailLowerCertificate

variable {size : Nat} {matrix : NamedMatrix size} (certificate : ScalarTailLowerCertificate matrix)

section
open Purelib.Approximation
/-- Compute an anchor beyond the threshold with scalar error below half the retained floor. -/
def tailAnchor : Nat :=
  Rational.Geometric.Search.firstQuarterBelow (canonicalScaledInverse matrix).scalar.errorScale certificate.threshold
    (certificate.lowerSq / 2)

/-- The computed tail anchor is at least the retained threshold. -/
theorem threshold_le_tailAnchor : certificate.threshold ≤ certificate.tailAnchor :=
  Rational.Geometric.Search.firstQuarterBelow_ge _ _ _

end

open Purelib.Approximation in
open Purelib.Data in
/-- The computed anchor has positive canonical scalar-tail clearance.

Its geometric error is below half the retained sample floor, so the scalar sample supplies strictly positive remaining
clearance. -/
theorem tailAnchor_clearance_positive : 0 < scalarTailClearanceAt matrix certificate.tailAnchor := by
  let scalar := (canonicalScaledInverse matrix).scalar
  let anchor := certificate.tailAnchor
  have halfPositive : 0 < certificate.lowerSq / 2 := Rat.Fraction.Order.Field.div_pos_direct certificate.positive (by
    decide)
  have radiusSmall : Rational.Geometric.Basic.quarterRadius scalar.errorScale anchor < certificate.lowerSq / 2 :=
    Rational.Geometric.Search.firstQuarterBelow_accurate scalar.errorScale scalar.errorScale_nonneg
      certificate.threshold (certificate.lowerSq / 2) halfPositive
  have lowerHalfLeSampleHalf : certificate.lowerSq / 2 ≤ Data.Gaussian.Norm.Basic.normSq (scalar.sample anchor) / 2
    := by
    simp only [Rat.Fraction.Field.div_eq_mul_inv_direct]
    exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (certificate.sample_lower anchor
      certificate.threshold_le_tailAnchor)
      (Rat.Fraction.Order.Field.inv_pos_direct (by decide : (0 : Coordinate) < 2)).le
  exact Rat.Fraction.Order.Arithmetic.sub_pos_direct (radiusSmall.trans_le lowerHalfLeSampleHalf)

/-- Package the computed anchor and its positive clearance as a scalar-tail separation certificate. -/
def toScalarTailSeparationCertificate : ScalarTailSeparationCertificate matrix :=
  ⟨certificate.tailAnchor, certificate.tailAnchor_clearance_positive⟩

end ScalarTailLowerCertificate
end Purelib.Riemann.Integration.ScalarTailLower
