module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Bounds
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Original spatial scalar coefficients and their separate magnitude payment

The ordinary spatial coefficient keeps the SAME old cofactor reading and
exact normalized ordinate, with the full original odd exponent on both.
The original tangent cancels precisely one normalized inverse factor.
Cached numerator bounds and two independently proved denominator floors give
a uniform spatial magnitude ceiling without including chart velocity.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential (Paths.polynomial parameter)}

/-- The original normalized-ordinate cancellation identifies the scalar spatial coefficient times its actual tangent.

The SAME original cofactor reading occurs on both sides. The original
quarter and labelled half-gap determine the tangent. Intrinsic regularity
pays the exact normalized factor; no approximate square or new arithmetic
observation is substituted into this scalar identity.
-/
theorem reading_mul_velocity (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (time : Fraction.Rational) (differential : OddPowerDifferential (Paths.polynomial parameter)) (root : Canonical)
    (regular : parameter ≠ criticalValue site) :
    reading (site := site) differential quarter time root *
      Tangent.baseVelocity site parameter 2 quarter time =
        Differential.reading site parameter quarter time differential root := by
  have cancellation := OddPowerDifferential.scalar_factor_cancellation
    (differential.scale * differential.numerator.eval
      (point site parameter 2 (Waist.direction quarter time) (of_decide_eq_true rfl)).base)
    (point site parameter 2 (Waist.direction quarter time) (of_decide_eq_true rfl)).ordinate
    (Stereographic.Tangent.logarithmicVelocity time) differential.denominatorPairs
    (parallel_ordinate_ne_zero site parameter (Waist.direction quarter time) regular)
  unfold reading Differential.reading
  rewrite [Tangent.baseVelocity_eq_ordinate_mul site parameter 2 quarter (of_decide_eq_true rfl) time]
  unfold OddPowerDifferential.denominatorExponent
  calc
    _ = ((differential.scale * differential.numerator.eval
      (point site parameter 2 (Waist.direction quarter time) (of_decide_eq_true rfl)).base *
      (point site parameter 2 (Waist.direction quarter time) (of_decide_eq_true rfl)).ordinate⁻¹ ^
        (2 * differential.denominatorPairs + 1)) *
      ((point site parameter 2 (Waist.direction quarter time) (of_decide_eq_true rfl)).ordinate *
        Stereographic.Tangent.logarithmicVelocity time)) * root⁻¹ ^ (2 * differential.denominatorPairs + 1) := by ring1
    _ = _ := congrArg (fun value : Canonical => value * root⁻¹ ^ (2 * differential.denominatorPairs + 1)) cancellation

namespace Bounds

open Purelib.Data.Rat.Fraction.Order

/-- The original retained numerator/scale caches and two full odd powers compute the spatial magnitude ceiling. -/
@[expose] def magnitude (data : Waist.Differential.Bounds.Data site parameter differential) : Fraction.Rational :=
  (data.scaleNorm * data.polynomial.value) *
    (Differential.Bounds.ordinateFloor data)⁻¹ ^ differential.denominatorExponent *
    16 ^ differential.denominatorExponent

/-- Intrinsic regularity makes the spatial scalar magnitude ceiling nonnegative. -/
theorem magnitude_nonnegative (data : Waist.Differential.Bounds.Data site parameter differential)
    (regular : parameter ≠ criticalValue site) : 0 ≤ magnitude data :=
  Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct data.scaleNorm_nonnegative data.polynomial_nonnegative.1)
      (Arithmetic.pow_nonneg_direct
        (Fraction.Order.Field.inv_pos_direct (Differential.Bounds.ordinateFloor_positive data regular)).le _))
    (Arithmetic.pow_nonneg_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 16) _)

/-- The SAME actual residual-certified cofactor reading obeys the computed ordinary spatial coefficient ceiling.

The numerator uses the original cached finite polynomial bound; regularity
pays the normalized ordinate, and the old reading's actual square residual
pays its independent cofactor floor. The two powers retain their original
full odd exponent, including cubic and quintic differential channels.
-/
theorem reading_normSq_le (data : Waist.Differential.Bounds.Data site parameter differential)
    (quarter : UnitCircuitQuarter) (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (time : Fraction.Rational) {root : Canonical}
    (residual : Norm.Basic.normSq (root * root - (unitPolynomial site).eval
      (point site parameter 2 (Waist.direction quarter time) (of_decide_eq_true rfl)).base) ≤
      Riemann.Branches.SquareRootSheets.residualTarget ((unitPolynomial site).eval
        (point site parameter 2 (Waist.direction quarter time) (of_decide_eq_true rfl)).base)) :
    Norm.Basic.normSq (reading (site := site) differential quarter time root) ≤ magnitude data := by
  have numerator : Norm.Basic.normSq (differential.scale * differential.numerator.eval
      (point site parameter 2 (Waist.direction quarter time) (of_decide_eq_true rfl)).base) ≤
      data.scaleNorm * data.polynomial.value := by
    rewrite [Norm.Basic.normSq_mul, ← data.scaleNorm_eq]
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Differential.Bounds.polynomial_value_le data quarter bound time) data.scaleNorm_nonnegative
  have paid := Norm.Reciprocal.coefficient_two_powers_normSq_le numerator
    (Differential.Bounds.ordinateFloor_positive data regular)
    (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1 / 16)
    (Differential.Bounds.ordinateFloor_le data quarter time)
    (UnitRoot.root_normSq_lower site
      (point_inside site parameter 2 (Waist.direction quarter time)
        (of_decide_eq_true rfl) (of_decide_eq_true rfl) (Fraction.Order.Basic.le_refl 2) bound) residual)
    differential.denominatorExponent differential.denominatorExponent
  rewrite [show (1 / 16 : Fraction.Rational)⁻¹ = 16 from of_decide_eq_true rfl] at paid
  exact paid

end Bounds

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive
