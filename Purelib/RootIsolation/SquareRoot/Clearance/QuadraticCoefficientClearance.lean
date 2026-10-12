module
import Purelib.Polynomial.Power.Gaussian
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Lines

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
public import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.Ring

/-!
# Quadratic clearance using the actual positive coefficient majorant

The existing resultant certificates use a coefficient majorant floored at
one.  Near an axis that floor can unnecessarily weaken transport clearance.
Here a positive computed majorant is retained even below one; only a
nonpositive proposal falls back to one.  A separate affine interval bound
on the imaginary component strengthens sides whose image stays away from
zero.  Both bounds follow from finite rational algebra, with no extra
assumption on the input coefficients.

This supplements the existing certificate representation.  Strengthening an
owner changes neither its box nor its winding, and never lowers its clearance.
-/

namespace Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

open Fraction.Order
open Purelib.RootIsolation.SquareRoot.Clearance

/-- The rational coordinate field used by the quadratic clearance construction. -/
public abbrev Coordinate := Fraction.Rational
/-- The exact Gaussian coefficient type of the quadratic root polynomial. -/
public abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- The rational rectangular box carrying the quadratic boundary certificate. -/
public abbrev Box := Geometry.Rational.Box
/-- The original exact quadratic owner, retaining its parameter, state box and clearance. -/
public abbrev Owner := Riemann.Topology.SquareRootContinuationChain.Owner

/-- The exact quadratic polynomial attached to the supplied Gaussian parameter.

The original degree-two power construction retains the supplied canonical
Gaussian coefficient. Its exact dense polynomial is shared by the boundary
and line clearance certificates. -/
@[expose] public def rootPolynomial (parameter : SquareRoot.Clearance.QuadraticCoefficientClearance.Gaussian) :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter Riemann.RootContinuation.SquareRootDegree.degreeTwo

/-- Compute a positive Cauchy majorant for a constant term and an affine coefficient on a bounded line.

Use the unfloored squared-coefficient sum when positive, and one only when that sum vanishes. -/
@[expose] public def coefficientMajorant (constant slope intercept radiusSq : Coordinate) : Coordinate :=
  let value := constant ^ 2 + 2 * (slope ^ 2 * radiusSq + intercept ^ 2)
  if 0 < value then value else 1

/-- The coefficient majorant is positive, including the zero-coefficient fallback.

The positive computed sum is returned unchanged; the alternative branch returns the exact rational one. -/
public theorem coefficientMajorant_positive (constant slope intercept radiusSq : Coordinate) :
    0 < coefficientMajorant constant slope intercept radiusSq := by
  unfold coefficientMajorant
  dsimp only
  split
  · assumption
  · decide

/-- The constant and affine coefficient square sum is bounded by the computed majorant.

The selected positive sum bounds itself, and the fallback one bounds a nonpositive proposed sum. -/
public theorem coefficient_le_majorant (constant slope intercept radiusSq : Coordinate) :
    constant ^ 2 + 2 * (slope ^ 2 * radiusSq + intercept ^ 2) ≤
      coefficientMajorant constant slope intercept radiusSq := by
  unfold coefficientMajorant
  dsimp only
  split
  · exact le_rfl
  · rename_i nonpositive
    exact (le_of_not_gt nonpositive).trans (by decide)

/-- The sharper denominator never exceeds the existing floored majorant.

Both calculations use the same constant, affine coefficient and squared radius; the older calculation additionally
floors the sum at one. -/
public theorem coefficientMajorant_le_direct (constant slope intercept radiusSq : Coordinate) :
    coefficientMajorant constant slope intercept radiusSq ≤
      QuadraticLineClearance.ExactQuadraticOwnerClearance.directLineMajorant
        constant slope intercept radiusSq := by
  unfold coefficientMajorant QuadraticLineClearance.ExactQuadraticOwnerClearance.directLineMajorant
  dsimp only
  split
  · exact Basic.le_max_right _ _
  · exact Basic.le_max_left _ _

/-- For the displayed small nonzero coefficients, the computed majorant retains its value below one. -/
public theorem subunit_majorant : coefficientMajorant 0 1 0 (1 / 16) = 1 / 8 := by
  decide +kernel

/-- Zero coefficients use the positive fallback majorant one. -/
public theorem zero_majorant : coefficientMajorant 0 0 0 0 = 1 := by
  decide +kernel

/-- A nonzero elimination resultant gives a squared-value lower bound using the positive coefficient majorant.

The explicit determinant identity and the retained squared-coordinate bound imply the stated comparison after division
by the positive computed coefficient majorant. -/
public theorem line_lower (coordinate radiusSq constant slope intercept determinant
    realPart imaginaryPart : Coordinate) (coordinateSq : coordinate ^ 2 ≤ radiusSq)
    (identity : determinant = constant * realPart +
      (slope * coordinate + intercept) * imaginaryPart) :
    determinant ^ 2 / coefficientMajorant constant slope intercept radiusSq ≤
      realPart ^ 2 + imaginaryPart ^ 2 := by
  have productLe : slope ^ 2 * coordinate ^ 2 ≤ slope ^ 2 * radiusSq :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct coordinateSq
      (Arithmetic.sq_nonneg_direct _)
  have linearLe : (slope * coordinate + intercept) ^ 2 ≤
      2 * (slope ^ 2 * radiusSq + intercept ^ 2) := by
    calc
      (slope * coordinate + intercept) ^ 2 ≤
          2 * ((slope * coordinate) ^ 2 + intercept ^ 2) :=
        Bounds.Square.add_sq_le_two _ _
      _ = 2 * (slope ^ 2 * coordinate ^ 2 + intercept ^ 2) := by ring1
      _ ≤ _ := Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct productLe le_rfl) (by decide)
  have coefficientLe := (Arithmetic.add_le_add_direct le_rfl linearLe).trans
    (coefficient_le_majorant constant slope intercept radiusSq)
  have cauchy : determinant ^ 2 ≤
      coefficientMajorant constant slope intercept radiusSq *
        (realPart ^ 2 + imaginaryPart ^ 2) := by
    rw [identity]
    exact (Bounds.Square.dot_sq_le_product_sums _ _ _ _).trans
      (Arithmetic.mul_le_mul_of_nonneg_right_direct coefficientLe
        (add_nonneg (Arithmetic.sq_nonneg_direct _)
          (Arithmetic.sq_nonneg_direct _)))
  apply (Field.div_le_iff_pos
    (coefficientMajorant_positive constant slope intercept radiusSq)).mpr
  rw [Fraction.Field.mul_comm]
  exact cauchy

/-- Squared distance from zero to a displayed interval.  Intervals containing
zero contribute no clearance; no sign assumption is supplied by the caller.

The two endpoint signs select the nearest squared endpoint when the interval stays on one side of zero; otherwise the
computed gap is zero. -/
@[expose] public def intervalGapSq (lower upper : Coordinate) : Coordinate :=
  if 0 ≤ lower then lower ^ 2 else if upper ≤ 0 then upper ^ 2 else 0

/-- The computed squared gap from zero is a lower bound for every coordinate in the supplied interval.

An interval above zero uses its lower endpoint, one below zero uses its upper endpoint, and an interval crossing zero
contributes no positive gap. -/
public theorem intervalGapSq_le {lower upper value : Coordinate}
    (below : lower ≤ value) (above : value ≤ upper) :
    intervalGapSq lower upper ≤ value ^ 2 := by
  unfold intervalGapSq
  split
  · rename_i nonnegative
    exact Arithmetic.pow_le_pow_direct nonnegative below 2
  · split
    · rename_i nonpositive
      have negativeNonnegative : 0 ≤ -upper := by
        simpa only [neg_zero] using
          Arithmetic.neg_le_neg_direct nonpositive
      have bound := Arithmetic.pow_le_pow_direct negativeNonnegative
        (Arithmetic.neg_le_neg_direct above) 2
      have upperSquare : (-upper) ^ 2 = upper ^ 2 := by ring1
      have valueSquare : (-value) ^ 2 = value ^ 2 := by ring1
      rw [upperSquare, valueSquare] at bound
      exact bound
    · exact Arithmetic.sq_nonneg_direct _

/-- Compute the squared gap from zero of an affine function on a closed interval.

Order its endpoint values before applying the interval-gap calculation, so negative slopes retain the same guarantee. -/
@[expose] public def affineGapSq (slope intercept lower upper : Coordinate) : Coordinate :=
  intervalGapSq (min (slope * lower + intercept) (slope * upper + intercept))
    (max (slope * lower + intercept) (slope * upper + intercept))

/-- The displayed positive- and negative-slope affine gap calculations have their exact rational values. -/
public theorem affineGapSq_regressions :
    affineGapSq (-2) 1 1 2 = 1 ∧ affineGapSq 2 (-3) 1 2 = 0 ∧
      affineGapSq 2 1 0 1 = 1 := by
  decide +kernel

/-- The computed affine gap is a lower bound for the square of every affine value on the interval.

The two endpoint values are ordered before the gap is computed, preserving the comparison for either sign of the
rational slope. -/
public theorem affineGapSq_le (slope intercept : Coordinate)
    {lower upper value : Coordinate} (below : lower ≤ value) (above : value ≤ upper) :
    affineGapSq slope intercept lower upper ≤ (slope * value + intercept) ^ 2 := by
  apply intervalGapSq_le
  · by_cases nonnegative : 0 ≤ slope
    · exact (Basic.min_le_left _ _).trans (Arithmetic.add_le_add_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct below nonnegative) le_rfl)
    · have negativeNonnegative : 0 ≤ -slope := by
        simpa only [neg_zero] using Arithmetic.neg_le_neg_direct
          (le_of_not_ge nonnegative)
      have reversed := Arithmetic.neg_le_neg_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct above negativeNonnegative)
      have product : slope * upper ≤ slope * value := by
        calc
          slope * upper = -((-slope) * upper) := by ring1
          _ ≤ -((-slope) * value) := reversed
          _ = slope * value := by ring1
      exact (Basic.min_le_right _ _).trans (Arithmetic.add_le_add_direct product le_rfl)
  · by_cases nonnegative : 0 ≤ slope
    · exact (Arithmetic.add_le_add_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct above nonnegative) le_rfl).trans
          (Basic.le_max_right _ _)
    · have negativeNonnegative : 0 ≤ -slope := by
        simpa only [neg_zero] using Arithmetic.neg_le_neg_direct
          (le_of_not_ge nonnegative)
      have reversed := Arithmetic.neg_le_neg_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct below negativeNonnegative)
      have product : slope * value ≤ slope * lower := by
        calc
          slope * value = -((-slope) * value) := by ring1
          _ ≤ -((-slope) * lower) := reversed
          _ = slope * lower := by ring1
      exact (Arithmetic.add_le_add_direct product le_rfl).trans (Basic.le_max_left _ _)

/-- Compute vertical-side clearance from the sharper resultant quotient and affine imaginary-coordinate gap.

Take their maximum on the original box; each term independently bounds the polynomial quadrance from below. -/
@[expose] public def verticalBound (parameter : Gaussian) (box : Box) (x : Coordinate) : Coordinate :=
  max (QuadraticAxisElimination.verticalDeterminant parameter x ^ 2 /
    coefficientMajorant (4 * x ^ 2) (2 * x) parameter.im
      (max (box.yLower ^ 2) (box.yUpper ^ 2)))
    (affineGapSq (2 * x) (-parameter.im) box.yLower box.yUpper)

/-- Compute horizontal-side clearance from the sharper resultant quotient and affine imaginary-coordinate gap.

Both terms use the original box, parameter and exact quadratic coefficient data. -/
@[expose] public def horizontalBound (parameter : Gaussian) (box : Box) (y : Coordinate) : Coordinate :=
  max (QuadraticAxisElimination.horizontalDeterminant parameter y ^ 2 /
    coefficientMajorant (4 * y ^ 2) (-(2 * y)) (-parameter.im)
      (max (box.xLower ^ 2) (box.xUpper ^ 2)))
    (affineGapSq (2 * y) (-parameter.im) box.xLower box.xUpper)

/-- The refined vertical bound dominates the original direct vertical resultant bound.

The determinant, original vertical side and original squared-radius endpoints remain fixed while the positive
denominator becomes no larger. -/
public theorem direct_vertical_le (parameter : Gaussian) (box : Box) (x : Coordinate) :
    QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound parameter box x ≤
      verticalBound parameter box x :=
  (Field.div_le_div_of_nonneg_left_direct
    (Arithmetic.sq_nonneg_direct _)
    (coefficientMajorant_positive _ _ _ _) (coefficientMajorant_le_direct _ _ _ _)).trans
      (Basic.le_max_left _ _)

/-- The refined horizontal bound dominates the original direct horizontal resultant bound.

The determinant, original horizontal side and original squared-radius endpoints remain fixed while the positive
denominator becomes no larger. -/
public theorem direct_horizontal_le (parameter : Gaussian) (box : Box) (y : Coordinate) :
    QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound parameter box y ≤
      horizontalBound parameter box y :=
  (Field.div_le_div_of_nonneg_left_direct
    (Arithmetic.sq_nonneg_direct _)
    (coefficientMajorant_positive _ _ _ _) (coefficientMajorant_le_direct _ _ _ _)).trans
      (Basic.le_max_left _ _)

/-- A small near-axis regression where flooring the majorant at one loses
strictly useful clearance.  No winding computation is needed to check it.

Its four retained rational endpoints delimit the displayed narrow box around the real coordinate one, with both
interval-order witnesses checked by the kernel. -/
@[expose] public def nearAxisBox : Box :=
  ⟨99 / 100, 101 / 100, -1 / 100, 1 / 100, by decide +kernel, by decide +kernel⟩

/-- The displayed near-axis box has a strictly stronger coefficient clearance than the original direct bound. -/
public theorem nearAxis_strict_improvement :
    QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
        1 nearAxisBox nearAxisBox.yUpper <
      horizontalBound 1 nearAxisBox nearAxisBox.yUpper := by
  decide +kernel

/-- The refined vertical bound is a lower bound for quadratic polynomial quadrance on the selected vertical side.

The exact quadratic value has the retained real and imaginary coordinate formulas; the resultant quotient and affine gap
each provide a lower bound. -/
public theorem vertical_lower (parameter : Gaussian) (box : Box) (x y : Coordinate)
    (lower : box.yLower ≤ y) (upper : y ≤ box.yUpper) :
    verticalBound parameter box x ≤
      Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomial parameter).eval (Gaussian.Components.Basic.point x y)) := by
  have bound := line_lower y (max (box.yLower ^ 2) (box.yUpper ^ 2))
    (4 * x ^ 2) (2 * x) parameter.im
    (QuadraticAxisElimination.verticalDeterminant parameter x)
    (x ^ 2 - y ^ 2 - parameter.re) (2 * x * y - parameter.im)
    (Box.sq_le_endpoint_max lower upper)
    (by unfold QuadraticAxisElimination.verticalDeterminant; ring1)
  have evaluation : Data.Gaussian.Norm.Basic.normSq
      ((rootPolynomial parameter).eval (Gaussian.Components.Basic.point x y)) =
      (x ^ 2 - y ^ 2 - parameter.re) ^ 2 + (2 * x * y - parameter.im) ^ 2 := by
    rw [rootPolynomial, Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval,
      Riemann.RootContinuation.SquareRootDegree.degreeTwo_value, pow_two]
    change
      ((x * x - y * y) - parameter.re) ^ 2 +
          ((x * y + y * x) - parameter.im) ^ 2 =
        (x ^ 2 - y ^ 2 - parameter.re) ^ 2 + (2 * x * y - parameter.im) ^ 2
    ring1
  rw [evaluation]
  apply Basic.max_le bound
  have component := affineGapSq_le (2 * x) (-parameter.im) lower upper
  have componentEq : 2 * x * y + -parameter.im = 2 * x * y - parameter.im := by ring1
  rw [componentEq] at component
  exact component.trans (by
    calc
      (2 * x * y - parameter.im) ^ 2 =
          0 + (2 * x * y - parameter.im) ^ 2 := by ring1
      _ ≤ (x ^ 2 - y ^ 2 - parameter.re) ^ 2 +
          (2 * x * y - parameter.im) ^ 2 :=
        Arithmetic.add_le_add_right_direct (Arithmetic.sq_nonneg_direct _) _)

/-- The refined horizontal bound is a lower bound for quadratic polynomial quadrance on the selected horizontal side.

The same exact quadratic coordinate formulas apply on the horizontal side, with the original interval bounds supplying
the squared-coordinate control. -/
public theorem horizontal_lower (parameter : Gaussian) (box : Box) (x y : Coordinate)
    (lower : box.xLower ≤ x) (upper : x ≤ box.xUpper) :
    horizontalBound parameter box y ≤
      Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomial parameter).eval (Gaussian.Components.Basic.point x y)) := by
  have bound := line_lower x (max (box.xLower ^ 2) (box.xUpper ^ 2))
    (4 * y ^ 2) (-(2 * y)) (-parameter.im)
    (QuadraticAxisElimination.horizontalDeterminant parameter y)
    (x ^ 2 - y ^ 2 - parameter.re) (2 * x * y - parameter.im)
    (Box.sq_le_endpoint_max lower upper)
    (by unfold QuadraticAxisElimination.horizontalDeterminant; ring1)
  have evaluation : Data.Gaussian.Norm.Basic.normSq
      ((rootPolynomial parameter).eval (Gaussian.Components.Basic.point x y)) =
      (x ^ 2 - y ^ 2 - parameter.re) ^ 2 + (2 * x * y - parameter.im) ^ 2 := by
    rw [rootPolynomial, Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval,
      Riemann.RootContinuation.SquareRootDegree.degreeTwo_value, pow_two]
    change
      ((x * x - y * y) - parameter.re) ^ 2 +
          ((x * y + y * x) - parameter.im) ^ 2 =
        (x ^ 2 - y ^ 2 - parameter.re) ^ 2 + (2 * x * y - parameter.im) ^ 2
    ring1
  rw [evaluation]
  apply Basic.max_le bound
  have component := affineGapSq_le (2 * y) (-parameter.im) lower upper
  have componentEq : 2 * y * x + -parameter.im = 2 * x * y - parameter.im := by ring1
  rw [componentEq] at component
  exact component.trans (by
    calc
      (2 * x * y - parameter.im) ^ 2 =
          0 + (2 * x * y - parameter.im) ^ 2 := by ring1
      _ ≤ (x ^ 2 - y ^ 2 - parameter.re) ^ 2 +
          (2 * x * y - parameter.im) ^ 2 :=
        Arithmetic.add_le_add_right_direct (Arithmetic.sq_nonneg_direct _) _)

/-- Take the minimum of the four refined quadratic side bounds on the original box.

The selected side values remain attached to their original four rational box endpoints, and the minimum retains their
common lower bound. -/
@[expose] public def boundaryBound (parameter : Gaussian) (box : Box) : Coordinate :=
  min (verticalBound parameter box box.xLower)
    (min (verticalBound parameter box box.xUpper)
      (min (horizontalBound parameter box box.yLower)
        (horizontalBound parameter box box.yUpper)))

/-- The computed four-side minimum bounds quadratic polynomial quadrance at every boundary point.

Every boundary point lies on one of the four original sides, whose computed bound dominates the selected minimum. -/
public theorem boundary_lower (parameter : Gaussian) (box : Box) (point : Gaussian)
    (boundary : Box.Boundary.OnBoxBoundary box point) :
    boundaryBound parameter box ≤
      Data.Gaussian.Norm.Basic.normSq ((rootPolynomial parameter).eval point) := by
  rcases boundary with ⟨inside, left | right | bottom | top⟩
  · have equal : point = Gaussian.Components.Basic.point box.xLower point.im :=
      Gaussian.Basic.ext left rfl
    rw [equal]
    exact (Basic.min_le_left _ _).trans (vertical_lower parameter box _ _ inside.2.2.1 inside.2.2.2)
  · have equal : point = Gaussian.Components.Basic.point box.xUpper point.im :=
      Gaussian.Basic.ext right rfl
    rw [equal]
    exact ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _)).trans
      (vertical_lower parameter box _ _ inside.2.2.1 inside.2.2.2)
  · have equal : point = Gaussian.Components.Basic.point point.re box.yLower :=
      Gaussian.Basic.ext rfl bottom
    rw [equal]
    exact ((Basic.min_le_right _ _).trans ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _))).trans
      (horizontal_lower parameter box _ _ inside.1 inside.2.1)
  · have equal : point = Gaussian.Components.Basic.point point.re box.yUpper :=
      Gaussian.Basic.ext rfl top
    rw [equal]
    exact ((Basic.min_le_right _ _).trans ((Basic.min_le_right _ _).trans (Basic.min_le_right _ _))).trans
      (horizontal_lower parameter box _ _ inside.1 inside.2.1)

/-- A total same-box strengthening.  The original positive clearance covers
degenerate coefficient cases; the additional bound is certified independently.

The original parameter, winding, box and delayed refinement construction are retained; only the certified clearance
bound is replaced by its maximum with the new four-side value. -/
@[expose] public def strengthen {parameter : Gaussian} (owner : Owner parameter) : Owner parameter :=
  let box := owner.track.initial.box
  let clearance : Clearance.Box.Boundary.Basic.BoundaryClearance (rootPolynomial parameter) box :=
    { bound := max owner.track.initial.clearance.bound (boundaryBound parameter box)
      positive := owner.track.initial.clearance.positive.trans_le (Basic.le_max_left _ _)
      lower := fun point boundary => Basic.max_le
        (owner.track.initial.clearance.lower point boundary)
        (by
          have lower := boundary_lower parameter box point boundary
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using lower) }
  ExactQuadraticOwnerClearance.ownerOfState owner.parameterNonzero
    { box := box
      refinesAmbient := Box.refines_refl box
      proper := owner.track.initial.proper
      clearance := clearance
      rawWindingFour := owner.track.initial.rawWindingFour
      ambientLeftClearance := Clearance.Box.Boundary.Lines.leftOfBoundary clearance
      ambientRightClearance := Clearance.Box.Boundary.Lines.rightOfBoundary clearance
      ambientBottomClearance := Clearance.Box.Boundary.Lines.bottomOfBoundary clearance
      ambientTopClearance := Clearance.Box.Boundary.Lines.topOfBoundary clearance }

/-- Coefficient-based strengthening preserves the original quadratic owner's exact box.

The strengthening construction supplies the original state box directly to the same retained owner constructor. -/
@[simp] public theorem strengthen_box {parameter : Gaussian} (owner : Owner parameter) :
    (strengthen owner).track.initial.box = owner.track.initial.box := rfl

/-- Coefficient-based strengthening retains at least the original owner's clearance.

The selected maximum contains the original positive clearance bound on its left. -/
public theorem strengthen_clearance_le {parameter : Gaussian} (owner : Owner parameter) :
    owner.track.initial.clearance.bound ≤ (strengthen owner).track.initial.clearance.bound :=
  Basic.le_max_left _ _

/-- Coefficient-based strengthening retains at least the newly computed four-side boundary bound.

The selected maximum contains the newly computed four-side bound on its right. -/
public theorem boundaryBound_le_strengthen {parameter : Gaussian} (owner : Owner parameter) :
    boundaryBound parameter owner.track.initial.box ≤
      (strengthen owner).track.initial.clearance.bound := Basic.le_max_right _ _

end Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
