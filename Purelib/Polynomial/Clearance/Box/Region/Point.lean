module

public import Purelib.Polynomial.Clearance.Box.Region
public import Purelib.Geometry.Rational.Box.Square.Centered
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion.Uniform
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Polynomial-clear rational squares about an actual nonroot

The original dense polynomial supplies its coefficient-computed Lipschitz
budget on the unit square about the retained point. The existing uniform
exclusion radius then pays variation on one explicit smaller square. Its
region clearance is a quantitative nonzero-value certificate throughout
that same square, including every boundary point.
-/

public section

namespace Purelib.Polynomial.Clearance.Box.Region.Point

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Rational (Box)
open Purelib.Geometry.Rational.Box.Square
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion

/-- The original unit-radius square used by the polynomial's finite coefficient budget. -/
@[expose] def ambient (center : Canonical) : Box :=
  Centered.Affine.centeredSquare center 1 (by decide +kernel)

/-- The computed positive local half-width is half the original uniform exclusion radius. -/
@[expose] def radius (polynomial : CoefficientPolynomial) (center : Canonical) : Fraction.Rational :=
  Uniform.uniformExclusionRadius polynomial (ambient center) (Norm.Basic.normSq (polynomial.eval center) / 8) / 2

/-- A retained nonzero polynomial value makes its computed local radius positive. -/
theorem radius_positive (polynomial : CoefficientPolynomial) (center : Canonical)
    (nonroot : polynomial.eval center ≠ 0) : 0 < radius polynomial center :=
  Fraction.Order.Field.div_pos_direct
    (Uniform.uniformExclusionRadius_pos polynomial (ambient center)
      (Fraction.Order.Field.div_pos_direct (Norm.Basic.normSq_pos nonroot) (by decide +kernel)))
    (by decide +kernel)

/-- The computed local square has half-width at most one half of the original unit radius. -/
theorem radius_le_half (polynomial : CoefficientPolynomial) (center : Canonical) :
    radius polynomial center ≤ 1 / 2 := by
  apply (Fraction.Order.Field.div_le_iff_pos (by decide +kernel : (0 : Fraction.Rational) < 2)).mpr
  rewrite [show ((1 / 2) * 2 : Fraction.Rational) = 1 by decide +kernel]
  exact Fraction.Order.Basic.min_le_left _ _

/-- The exact local square retains the original point and its computed positive half-width. -/
@[expose] def box (polynomial : CoefficientPolynomial) (center : Canonical)
    (nonroot : polynomial.eval center ≠ 0) : Box :=
  Centered.Affine.centeredSquare center (radius polynomial center)
    (radius_positive polynomial center nonroot).le

/-- The complete local square lies in the original coefficient-budget square. -/
theorem box_refines (polynomial : CoefficientPolynomial) (center : Canonical)
    (nonroot : polynomial.eval center ≠ 0) : (box polynomial center nonroot).Refines (ambient center) :=
  Box.Refinement.StrictInterior.refines
    (Centered.centeredSquare_strictInterior_of_lt center
      (radius_positive polynomial center nonroot).le (by decide +kernel)
      ((radius_le_half polynomial center).trans_lt (by decide +kernel)))

/-- The original retained point belongs to its exact computed polynomial-clear square. -/
theorem center_inside (polynomial : CoefficientPolynomial) (center : Canonical)
    (nonroot : polynomial.eval center ≠ 0) : (box polynomial center nonroot).Contains center :=
  Centered.centeredSquare_contains_center center
    (radius polynomial center) (radius_positive polynomial center nonroot).le

/-- Every nearby value with the computed squared-distance payment belongs to the same original local square. -/
theorem contains_of_distance (polynomial : CoefficientPolynomial) (center : Canonical)
    (nonroot : polynomial.eval center ≠ 0) {value : Canonical}
    (distance : Norm.Basic.normSq (value - center) ≤ radius polynomial center ^ 2) :
    (box polynomial center nonroot).Contains value :=
  Centered.centeredBox_contains_of_normSq_sub_le
    (radius_positive polynomial center nonroot).le distance

/-- Every point of the exact local square pays one eighth of the original polynomial-value quadrance in variation. -/
theorem variation_lt (polynomial : CoefficientPolynomial) (center : Canonical)
    (nonroot : polynomial.eval center ≠ 0) {value : Canonical}
    (inside : (box polynomial center nonroot).Contains value) :
    Norm.Basic.normSq (polynomial.eval value - polynomial.eval center) <
      Norm.Basic.normSq (polynomial.eval center) / 8 := by
  let original := Uniform.uniformExclusionRadius polynomial (ambient center)
    (Norm.Basic.normSq (polynomial.eval center) / 8)
  have originalPositive : 0 < original := Uniform.uniformExclusionRadius_pos polynomial (ambient center)
    (Fraction.Order.Field.div_pos_direct (Norm.Basic.normSq_pos nonroot) (by decide +kernel))
  have radiusLe : radius polynomial center ≤ original := by
    apply (Fraction.Order.Field.div_le_iff_pos (by decide +kernel : (0 : Fraction.Rational) < 2)).mpr
    have bound := Arithmetic.mul_le_mul_of_nonneg_left_direct
      (by decide +kernel : (1 : Fraction.Rational) ≤ 2) originalPositive.le
    rewrite [Fraction.Field.mul_one_direct] at bound
    exact bound
  have square := Arithmetic.pow_le_pow_direct
    (radius_positive polynomial center nonroot).le radiusLe 2
  have displacement := Centered.centeredSquare_normSq_sub_center_le center
    (radius_positive polynomial center nonroot).le inside
  have movement := Gaussian.Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound polynomial
    ((box_refines polynomial center nonroot).contains inside)
    (Centered.centeredSquare_contains_center center 1 (by decide +kernel))
  have constant := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (by decide +kernel : (2 : Fraction.Rational) ≤ 4)
    (Gaussian.Bounds.Box.denseLipschitzBound_pos polynomial (ambient center)).le
  calc
    _ ≤ Gaussian.Bounds.Box.denseLipschitzBound polynomial (ambient center) *
        (2 * radius polynomial center ^ 2) := movement.trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct displacement
        (Gaussian.Bounds.Box.denseLipschitzBound_pos polynomial (ambient center)).le)
    _ ≤ (4 * Gaussian.Bounds.Box.denseLipschitzBound polynomial (ambient center)) * original ^ 2 := by
      have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct square
        (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
          (Gaussian.Bounds.Box.denseLipschitzBound_pos polynomial (ambient center)).le)
      exact (show _ = (2 * Gaussian.Bounds.Box.denseLipschitzBound polynomial (ambient center)) *
        radius polynomial center ^ 2 by ring1).trans_le
          (scaled.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct constant
            (Arithmetic.sq_nonneg_direct original)))
    _ < _ := Uniform.uniform_exclusion_margin polynomial (ambient center)
      (Fraction.Order.Field.div_pos_direct (Norm.Basic.normSq_pos nonroot) (by decide +kernel))

/-- The actual local polynomial quadrance is at least one quarter of its exact retained center value. -/
theorem lower (polynomial : CoefficientPolynomial) (center : Canonical)
    (nonroot : polynomial.eval center ≠ 0) {value : Canonical}
    (inside : (box polynomial center nonroot).Contains value) :
    Norm.Basic.normSq (polynomial.eval center) / 4 ≤ Norm.Basic.normSq (polynomial.eval value) := by
  have variation := variation_lt polynomial center nonroot inside
  have reversed : Norm.Basic.normSq (polynomial.eval center - polynomial.eval value) =
      Norm.Basic.normSq (polynomial.eval value - polynomial.eval center) := Norm.Bounds.normSq_sub_symm _ _
  have estimate := Norm.Bounds.half_normSq_sub_le_normSq_sub (polynomial.eval center)
    (polynomial.eval center - polynomial.eval value)
  rewrite [reversed, show polynomial.eval center - (polynomial.eval center - polynomial.eval value) =
    polynomial.eval value by ring1] at estimate
  have paid : Norm.Basic.normSq (polynomial.eval center) / 4 ≤
      Norm.Basic.normSq (polynomial.eval center) / 2 - Norm.Basic.normSq (polynomial.eval center) / 8 := by
    rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.div_eq_mul_inv_direct]
    have equal : Norm.Basic.normSq (polynomial.eval center) * (2 : Fraction.Rational)⁻¹ -
        Norm.Basic.normSq (polynomial.eval center) * (8 : Fraction.Rational)⁻¹ =
          Norm.Basic.normSq (polynomial.eval center) * ((2 : Fraction.Rational)⁻¹ - (8 : Fraction.Rational)⁻¹) := by
      ring1
    rewrite [equal]
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct
      (by decide +kernel : (4 : Fraction.Rational)⁻¹ ≤ (2 : Fraction.Rational)⁻¹ - (8 : Fraction.Rational)⁻¹)
      (Norm.Basic.normSq_nonneg _)
  exact paid.trans ((Arithmetic.sub_le_sub_left_direct variation.le
    (Norm.Basic.normSq (polynomial.eval center) / 2)).trans estimate)

/-- Construct the original quantitative region clearance on the exact computed square about a nonroot. -/
@[expose] def clearance (polynomial : CoefficientPolynomial) (center : Canonical)
    (nonroot : polynomial.eval center ≠ 0) : RegionClearance polynomial (box polynomial center nonroot) :=
  { bound := Norm.Basic.normSq (polynomial.eval center) / 4
    positive := Fraction.Order.Field.div_pos_direct (Norm.Basic.normSq_pos nonroot) (by decide +kernel)
    lower := fun _ inside => lower polynomial center nonroot inside }

/-- The region clearance retains the exact original center-value quadrance payment. -/
theorem clearance_bound (polynomial : CoefficientPolynomial) (center : Canonical)
    (nonroot : polynomial.eval center ≠ 0) :
    (clearance polynomial center nonroot).bound = Norm.Basic.normSq (polynomial.eval center) / 4 := rfl

end Purelib.Polynomial.Clearance.Box.Region.Point
