module

public import Purelib.Polynomial.Clearance.Box.Region
public import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field

/-! # Closed-box clearance through a retained polynomial factorization

The actual source polynomial has a positive region clearance. A computed
Horner ceiling for the original cofactor transfers that clearance to the
retained factor throughout the same box, without choosing another root or
changing any geometric owner.
-/

public section

namespace Purelib.Polynomial.Clearance.Box.Region.RegionClearance

open Purelib
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Factorization
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

/-- Add one to the original cofactor's actual finite Horner quadrance ceiling. -/
def cofactorMargin (cofactor : CoefficientPolynomial) (box : Box) : Rational :=
  1 + Bounds.Box.denseEvalNormBound cofactor box

/-- The same retained cofactor margin is strictly positive even for the zero cofactor. -/
private theorem packaged_cofactorMargin_positive (cofactor : CoefficientPolynomial) (box : Box) :
    0 < cofactorMargin cofactor box := by
  have nonnegative := (Bounds.Box.denseHornerNormBounds_nonneg cofactor box).1
  have shifted := Order.Arithmetic.add_lt_add_right_direct (by decide +kernel : (0 : Rational) < 1)
    (Bounds.Box.denseEvalNormBound cofactor box)
  rewrite [Field.zero_add] at shifted
  exact nonnegative.trans_lt shifted

/-- The same retained original cofactor bound has its stated scalar readback. -/
theorem cofactorMargin_positive (cofactor : CoefficientPolynomial) (box : Box) :
    0 < cofactorMargin cofactor box :=
  packaged_cofactorMargin_positive cofactor box

/-- The actual cofactor value is bounded by its same original positive margin throughout the closed box. -/
private theorem packaged_cofactor_le_margin (cofactor : CoefficientPolynomial) (box : Box) {point : Canonical}
    (inside : box.Contains point) : Norm.Basic.normSq (cofactor.eval point) ≤ cofactorMargin cofactor box := by
  have bounded := Bounds.Box.normSq_eval_le_denseEvalNormBound cofactor inside
  have extra := Order.Arithmetic.add_le_add_direct (by decide +kernel : (0 : Rational) ≤ 1)
    (Order.Basic.le_refl (Bounds.Box.denseEvalNormBound cofactor box))
  rewrite [Field.zero_add] at extra
  exact bounded.trans extra

/-- The same retained original cofactor bound has its stated scalar readback. -/
theorem cofactor_le_margin (cofactor : CoefficientPolynomial) (box : Box) {point : Canonical}
    (inside : box.Contains point) : Norm.Basic.normSq (cofactor.eval point) ≤ cofactorMargin cofactor box :=
  packaged_cofactor_le_margin cofactor box inside

variable {source factor cofactor : CoefficientPolynomial} {box : Box}

/-- Source clearance and the checked ordered factorization pay a positive lower bound on the actual factor. -/
theorem factor_lower (clearance : RegionClearance source box)
    (identity : Identity.ProductIdentity source factor cofactor) (point : Canonical) (inside : box.Contains point) :
    clearance.bound / cofactorMargin cofactor box ≤ Norm.Basic.normSq (factor.eval point) := by
  apply (Order.Field.div_le_iff_pos (cofactorMargin_positive cofactor box)).mpr
  have original := clearance.lower point inside
  have displayed := Identity.eval_factorization identity point
  rewrite [displayed, Norm.Basic.normSq_mul] at original
  exact original.trans (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (cofactor_le_margin cofactor box inside) (Norm.Basic.normSq_nonneg _))

/-- Transfer the original region clearance to one retained factor using the finite cofactor ceiling.

The source/factor/cofactor and the closed box remain the original inputs.
Only one Horner ceiling and one positive quotient are computed; the scalar
factorization supplies the lower-bound proof at every actual box point.
-/
def ofFactor (clearance : RegionClearance source box)
    (identity : Identity.ProductIdentity source factor cofactor) : RegionClearance factor box :=
  let margin := cofactorMargin cofactor box
  let bound := clearance.bound / margin
  ⟨bound, Order.Field.div_pos_direct clearance.positive (cofactorMargin_positive cofactor box),
    factor_lower clearance identity⟩

/-- The complete transfer retains the one original cofactor-margin calculation and its actual positive quotient. -/
private theorem packaged_ofFactor_factory (clearance : RegionClearance source box)
    (identity : Identity.ProductIdentity source factor cofactor) :
    ofFactor clearance identity =
      (let margin := cofactorMargin cofactor box
       let bound := clearance.bound / margin
       ⟨bound, Order.Field.div_pos_direct clearance.positive (cofactorMargin_positive cofactor box),
         factor_lower clearance identity⟩ : RegionClearance factor box) := by rfl

/-- The complete transfer retains the one original cofactor-margin calculation and its actual positive quotient. -/
theorem ofFactor_factory (clearance : RegionClearance source box)
    (identity : Identity.ProductIdentity source factor cofactor) :
    ofFactor clearance identity =
      (let margin := cofactorMargin cofactor box
       let bound := clearance.bound / margin
       ⟨bound, Order.Field.div_pos_direct clearance.positive (cofactorMargin_positive cofactor box),
         factor_lower clearance identity⟩ : RegionClearance factor box) :=
  packaged_ofFactor_factory clearance identity

end Purelib.Polynomial.Clearance.Box.Region.RegionClearance

end
