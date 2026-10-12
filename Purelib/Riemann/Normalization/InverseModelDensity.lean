module
public import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
public import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Geometry.EvaluationLower

import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Checked density retained by finite inverse-root models

The residual bound of an actual polynomial inverse-root model already
implies a positive lower norm. Combining it with the two square-root-free
surface-density checks retains one quarter of the certified density. No
exact Gaussian square root, sheet extraction, or additional successful
coefficient check is required. This norm estimate is insensitive to the
sign; operational sheet ownership is still needed for primitive comparisons.
-/

namespace Purelib.Riemann.Normalization.InverseModelDensity.InverseRootPolynomial

open Purelib.Riemann.Normalization.InverseModelOverlap (normalized_value_lower)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data in
/-- Retain one quarter of a certified density after multiplying by an approximate inverse root.

The density is nonnegative, bounded by numerator norm, and remains valid after multiplication by parameter norm; the
inverse-root residual is at most one sixteenth. -/
theorem density_mul_inverse_lower {parameter numerator value : Gaussian} {density : Coordinate}
    (nonnegative : 0 ≤ density) (belowNumerator : density ≤ normSq numerator)
    (valid : density * normSq parameter ≤ normSq numerator)
    (small : normSq (1 - parameter * value ^ 2) ≤ 1 / 16) :
    density / 4 ≤ normSq (numerator * value) := by
  rw [Gaussian.Basic.Canonical.normSq_mul]
  have lower := (by decide : (1 / 4 : Coordinate) ≤ 1 / 3).trans (normalized_value_lower small)
  if bounded : normSq value ≤ 1 then
    have square : normSq value ^ 2 ≤ normSq value := by
      calc
        _ = normSq value * normSq value := by ring1
        _ ≤ normSq value * 1 := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded
          (Gaussian.Basic.Canonical.normSq_nonneg value)
        _ = _ := by ring1
    have product : (1 / 4 : Coordinate) ≤ normSq parameter * normSq value :=
      lower.trans (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square
        (Gaussian.Basic.Canonical.normSq_nonneg parameter))
    calc
      density / 4 = density * (1 / 4) := by simp only [Rat.Fraction.Field.div_eq_mul_inv_direct]; ring1
      _ ≤ density * (normSq parameter * normSq value) :=
        Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product nonnegative
      _ = (density * normSq parameter) * normSq value := by ring1
      _ ≤ _ := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct valid
        (Gaussian.Basic.Canonical.normSq_nonneg value)
  else
    calc
      density / 4 = density * (1 / 4) := by simp only [Rat.Fraction.Field.div_eq_mul_inv_direct]; ring1
      _ ≤ density * 1 := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide) nonnegative
      _ = density := by ring1
      _ ≤ normSq numerator := belowNumerator
      _ = normSq numerator * 1 := by ring1
      _ ≤ _ := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (le_of_not_ge bounded)
        (Gaussian.Basic.Canonical.normSq_nonneg numerator)

end Purelib.Riemann.Normalization.InverseModelDensity.InverseRootPolynomial

namespace Purelib.Riemann.Normalization.InverseModelDensity.SurfaceCell

open Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy (SurfaceCell)
open Purelib.Polynomial.Geometry.EvaluationLower (GaussianVector coefficientPolynomial)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Normalization.InverseModelOverlap (normalized_value_lower)

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- The retained inverse polynomial preserves one quarter of a surface cell's density lower bound.

The query point lies in both certified boxes, which need not be equal; the model's actual residual bound supplies the
inverse estimate. -/
theorem densityLower_le_inverseModel {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : Geometry.EvaluationLower.GaussianVector genus} (cell :
      Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) {box : Box}
    (model : Normalization.InverseRootPolynomial.Model curve.polynomial box) {point : Gaussian}
    (inside : cell.box.Contains point) (inModel : box.Contains point) :
    cell.densityLower / 4 ≤ normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point *
      model.value.eval point) := by
  have numerator := cell.density_below_numerator point inside
  have valid := cell.density_valid point inside
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at numerator valid
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  apply InverseRootPolynomial.density_mul_inverse_lower cell.densityLower_nonnegative numerator valid
  rw [← model.residual_eq]
  exact (model.residualBound point inModel).trans model.bound_small

end Purelib.Riemann.Normalization.InverseModelDensity.SurfaceCell
