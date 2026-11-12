module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial
public import Purelib.Data.Rat.Fraction.Cast
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Monotonicity
import Purelib.Polynomial.Quadratic.Split
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Field

/-! # Uniform original-quarter full-cubic spatial clearance payments

The regular parallel ordinate floor and original cofactor patch clearance
bound the full cubic value at every actual conic point. One fixed polynomial
coefficient budget dominates all local source squares. A common positive
radius and computed dyadic chart depth consequently pay spatial connectors
throughout the retained original quarter, without obtaining new root samples.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Uniform

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Clearance.Box.Region
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Approximation

/-- The same internally derived full-cubic quadrance floor at every original regular parallel point. -/
@[expose] def cubicFloor (site : Fin 2) (parameter : Canonical) : Fraction.Rational :=
  (81 / Fraction.Cast.fromInt 1024) * Norm.Basic.normSq (halfGap site parameter) ^ 2

/-- The full-cubic floor is positive at an intrinsically regular labelled collision parameter. -/
theorem cubicFloor_positive (site : Fin 2) (parameter : Canonical)
    (regular : parameter ≠ criticalValue site) : 0 < cubicFloor site parameter :=
  Arithmetic.mul_pos_direct (by decide +kernel)
    (Arithmetic.pow_pos_direct
      (Norm.Basic.normSq_pos (Polynomial.Quadratic.Split.halfGap_ne_zero (by decide +kernel) regular.symm)) 2)

/-- The actual original cubic value pays that same floor at every retained parallel point. -/
theorem cubic_normSq_lower (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (bound : RadiusBound site parameter) :
    cubicFloor site parameter ≤ Norm.Basic.normSq
      ((Paths.polynomial parameter).eval (Radial.point site parameter 2 original (by decide +kernel)).base) := by
  let point := Radial.point site parameter 2 original (by decide +kernel)
  have unit := unit_lower site (point_inside site parameter 2 original (by decide +kernel)
    (by decide +kernel) (by decide +kernel) bound)
  have ordinate := parallel_ordinate_lower site parameter original
  have factor : (Paths.polynomial parameter).eval point.base =
      point.ordinate ^ 2 * (unitPolynomial site).eval point.base := by
    rewrite [polynomial_centered, point.coordinate_base, ← point.quadratic]
    rfl
  have ordinateNonnegative : 0 ≤ (9 / 16) * Norm.Basic.normSq (halfGap site parameter) :=
    Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _)
  have squared := Arithmetic.pow_le_pow_direct ordinateNonnegative ordinate 2
  have first := Arithmetic.mul_le_mul_of_nonneg_right_direct squared
    (by decide +kernel : (0 : Fraction.Rational) ≤ 1 / 4)
  have second := Arithmetic.mul_le_mul_of_nonneg_left_direct unit
    (Arithmetic.sq_nonneg_direct (Norm.Basic.normSq point.ordinate))
  have exactFloor : ((9 / 16) * Norm.Basic.normSq (halfGap site parameter)) ^ 2 * (1 / 4) =
      cubicFloor site parameter := by
    rewrite [Fraction.Field.mul_pow_direct]
    unfold cubicFloor
    calc
      _ = ((9 / 16 : Fraction.Rational) ^ 2 * (1 / 4)) * Norm.Basic.normSq (halfGap site parameter) ^ 2 := by
        ring1
      _ = _ := congrArg (fun factor => factor * Norm.Basic.normSq (halfGap site parameter) ^ 2)
        (by decide +kernel : (9 / 16 : Fraction.Rational) ^ 2 * (1 / 4) = 81 / Fraction.Cast.fromInt 1024)
  rewrite [factor, Norm.Basic.normSq_mul, pow_two, Norm.Basic.normSq_mul]
  exact exactFloor.symm.trans_le ((first.trans second).trans_eq (by ring1))

/-- The exact original full cubic is nonzero everywhere on the retained regular parallel conic circle. -/
theorem nonroot (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site) (bound : RadiusBound site parameter) :
    (Paths.polynomial parameter).eval (Radial.point site parameter 2 original (by decide +kernel)).base ≠ 0 := by
  intro zero
  have floor := cubic_normSq_lower site parameter original bound
  rewrite [zero, Norm.Basic.normSq_zero] at floor
  exact (not_le_of_gt (cubicFloor_positive site parameter regular)) floor

/-- One fixed collision-centered square supplies the polynomial coefficient budget for every original local source. -/
@[expose] def ambient (site : Fin 2) : Geometry.Rational.Box :=
  Geometry.Rational.Box.Square.Centered.Affine.centeredSquare (criticalValue site) 2 (by decide +kernel)

/-- Every original local unit-radius source square refines the same retained coefficient-budget square. -/
theorem sourceAmbient_refines (site : Fin 2) {base : Canonical} (inside : (spatialBox site).Contains base) :
    (Point.ambient base).Refines (ambient site) := by
  change (criticalValue site).re - 1 / 2 ≤ base.re ∧ base.re ≤ (criticalValue site).re + 1 / 2 ∧
    (criticalValue site).im - 1 / 2 ≤ base.im ∧ base.im ≤ (criticalValue site).im + 1 / 2 at inside
  change (criticalValue site).re - 2 ≤ base.re - 1 ∧ base.re + 1 ≤ (criticalValue site).re + 2 ∧
    (criticalValue site).im - 2 ≤ base.im - 1 ∧ base.im + 1 ≤ (criticalValue site).im + 2
  have lower (center value : Fraction.Rational) (paid : center - 1 / 2 ≤ value) : center - 2 ≤ value - 1 := by
    calc
      _ ≤ center - (1 / 2 + 1) := Arithmetic.sub_le_sub_left_direct
        (by decide +kernel : (1 / 2 + 1 : Fraction.Rational) ≤ 2) center
      _ = center - 1 / 2 - 1 := by ring1
      _ ≤ _ := Arithmetic.sub_le_sub_right_direct paid 1
  have upper (center value : Fraction.Rational) (paid : value ≤ center + 1 / 2) : value + 1 ≤ center + 2 := by
    calc
      _ ≤ (center + 1 / 2) + 1 := Arithmetic.add_le_add_right_direct paid 1
      _ = center + (1 / 2 + 1) := by ring1
      _ ≤ center + 2 := Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl center)
        (by decide +kernel : (1 / 2 + 1 : Fraction.Rational) ≤ 2)
  exact ⟨lower _ _ inside.1, upper _ _ inside.2.1, lower _ _ inside.2.2.1, upper _ _ inside.2.2.2⟩

/-- The common positive radius is computed once from the original full-cubic floor and fixed coefficient budget. -/
@[expose] def radius (site : Fin 2) (parameter : Canonical) : Fraction.Rational :=
  Bounds.Box.Exclusion.Uniform.uniformExclusionRadius (Paths.polynomial parameter) (ambient site)
    (cubicFloor site parameter / 8) / 2

/-- The common original-quarter spatial radius is strictly positive at either regular labelled collision. -/
theorem radius_positive (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site) :
    0 < radius site parameter :=
  Fraction.Order.Field.div_pos_direct
    (Bounds.Box.Exclusion.Uniform.uniformExclusionRadius_pos _ _
      (Fraction.Order.Field.div_pos_direct (cubicFloor_positive site parameter regular) (by decide +kernel)))
    (by decide +kernel)

/-- Every actual original local source radius dominates the same common original-quarter radius. -/
theorem radius_le_source (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site) (bound : RadiusBound site parameter) :
    radius site parameter ≤ Point.radius (Paths.polynomial parameter)
      (Radial.point site parameter 2 original (by decide +kernel)).base := by
  let polynomial := Paths.polynomial parameter
  let base := (Radial.point site parameter 2 original (by decide +kernel)).base
  let localBudget := Bounds.Box.denseLipschitzBound polynomial (Point.ambient base)
  let commonBudget := Bounds.Box.denseLipschitzBound polynomial (ambient site)
  have budgetOrder : localBudget ≤ commonBudget :=
    Bounds.Box.Monotonicity.denseLipschitzBound_le_of_refines polynomial
      (sourceAmbient_refines site (point_inside site parameter 2 original (by decide +kernel)
        (by decide +kernel) (by decide +kernel) bound))
  have localPositive : 0 < 8 * localBudget := Arithmetic.mul_pos_direct (by decide +kernel)
    (Bounds.Box.denseLipschitzBound_pos _ _)
  have denominatorOrder := Arithmetic.mul_le_mul_of_nonneg_left_direct budgetOrder
    (by decide +kernel : (0 : Fraction.Rational) ≤ 8)
  have lowerPositive : 0 < cubicFloor site parameter / 8 :=
    Fraction.Order.Field.div_pos_direct (cubicFloor_positive site parameter regular) (by decide +kernel)
  have first := Fraction.Order.Field.div_le_div_of_nonneg_left_direct lowerPositive.le
    localPositive denominatorOrder
  have floor := Fraction.Order.Field.divide_mono (cubic_normSq_lower site parameter original bound)
    (by decide +kernel : (0 : Fraction.Rational) < 8)
  have second := Fraction.Order.Field.divide_mono floor localPositive
  have smaller := Fraction.Order.Basic.min_le_min (Fraction.Order.Basic.le_refl 1) (first.trans second)
  exact Fraction.Order.Field.divide_mono smaller (by decide +kernel : (0 : Fraction.Rational) < 2)

/-- The common positive chart-time request pays every original local source square on the retained parallel quarter. -/
@[expose] def timeRequest (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site) :
    AccuracyRequest :=
  ⟨radius site parameter ^ 2 / (1 + (25 / 4) * Norm.Basic.normSq (halfGap site parameter)),
    Fraction.Order.Field.div_pos_direct (Arithmetic.pow_pos_direct
      (radius_positive site parameter regular) 2)
      (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide +kernel)
        (Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _)))⟩

/-- The sufficient finite dyadic chart index is common to all actual source nodes of that original quarter. -/
@[expose] def minimum (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site) : Nat :=
  Approximation.Rational.Geometric.Search.firstQuarterBelow 1 0 (timeRequest site parameter regular).tolerance

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2} {actual : Quarter site parameter 2 quarter positive}
variable {first last : Fraction.Rational} {firstInside : Riemann.RootContinuation.FixedRootBoxPath.Inside first}
variable {reading : Reading actual first firstInside}
variable {prepared : Gaussian.Division.Prepared reading.lift.value}

/-- The common computed chart-time tolerance pays the exact original retained source's local accuracy request. -/
theorem timeRequest_le_source (source : Source reading prepared) (regular : parameter ≠ criticalValue site) :
    (timeRequest site parameter regular).tolerance ≤ source.timeRequest.tolerance := by
  have radiusOrder := radius_le_source site parameter (Waist.direction quarter first) regular actual.data.bound
  have square := Arithmetic.pow_le_pow_direct (radius_positive site parameter regular).le radiusOrder 2
  exact Fraction.Order.Field.divide_mono square
    (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) < 1)
      (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 25 / 4)
        (Norm.Basic.normSq_nonneg _)))

/-- The common finite dyadic chart payment puts the actual original endpoint in its retained source's cleared square. -/
theorem target_inside (source : Source reading prepared) (regular : parameter ≠ criticalValue site)
    (payment : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1
      (minimum site parameter regular)) :
    source.box.Contains (coordinate site parameter 2 quarter positive last) :=
  source.target_inside_of_payment ((payment.trans
    (Approximation.Rational.Geometric.Search.firstQuarterBelow_accurate 1 (by decide +kernel) 0
      (timeRequest site parameter regular).tolerance (timeRequest site parameter regular).positive).le).trans
        (timeRequest_le_source source regular))

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Uniform
