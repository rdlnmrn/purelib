module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Data.Rat.Interval.Bisection
public import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Integration.Polynomial.Gaussian.Path.ConstantComparison
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Field

/-!
# Actual midpoint refinement of a residual-controlled waist cell

The left child reuses the complete original starting lift. The right child
constructs the original signed lift at the exact midpoint once. Both prepare
one-quarter residual requests; the parent estimate derives the actual
coefficient comparisons for the two ordered children.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Polynomial.Ascending

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}
variable {targetRadicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {quarter : UnitCircuitQuarter} {regular : parameter ≠ criticalValue site}
variable {bound : normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)}
variable {span : Interval.Bounds}
variable {unit : Owner ((unitPolynomial site).eval
  (point site parameter (direction quarter span.lower) regular bound).base)}
variable {data : Bounds.Data site parameter differential} {simple : differential.denominatorPairs = 0}
variable {lift : Conic.Lift (point site parameter (direction quarter span.lower) regular bound) unit}
variable {accuracy : Fraction.Rational}

set_option genInjectivity false in
/-- The actual ordered midpoint children of one retained original waist cell.

The parent remains an index. The left child keeps its same complete starting
lift; the right midpoint lift is cached once and passed to its child.
-/
structure Split (parent : Cell data simple lift accuracy) where
  /-- The actual left child on the original left half and unchanged starting lift. -/
  left : Cell (span := Interval.Bisection.leftHalf span) data simple lift (accuracy / 4)
  /-- The complete original signed cubic lift cached once at the exact midpoint. -/
  rightLift : Conic.Lift
    (point site parameter (direction quarter (Interval.Bisection.midpoint span)) regular bound)
    (UnitRoot.owner site
      (point site parameter (direction quarter (Interval.Bisection.midpoint span)) regular bound).base
      (point_inside site parameter (direction quarter (Interval.Bisection.midpoint span)) regular bound))
  /-- The actual right child consumes that same midpoint lift. -/
  right : Cell (span := Interval.Bisection.rightHalf span) data simple rightLift (accuracy / 4)

constructive_injectivity Split

namespace Split

/-- Prepare both actual half-span children with one-quarter residual requests and one cached midpoint lift. -/
@[expose] def build (parent : Cell data simple lift accuracy) : Split parent := by
  have positive : (0 : Fraction.Rational) < accuracy / 4 :=
    Fraction.Order.Field.div_pos_direct parent.positive (by decide +kernel)
  have sourceWithin : lift.unitOwner.track.initial.box.Refines (UnitRoot.box site) := by
    rewrite [← parent.reading.rootBox_eq]
    exact parent.signed
  let left := Cell.build (span := Interval.Bisection.leftHalf span) data simple lift sourceWithin _ positive
  let rightLift := Waist.lift site parameter (direction quarter (Interval.Bisection.midpoint span)) regular bound
  have rightWithin : rightLift.unitOwner.track.initial.box.Refines (UnitRoot.box site) := by
    rewrite [rightLift.unitOwner_eq, UnitRoot.owner_initial_box]
    exact Box.refines_refl _
  let right := Cell.build (span := Interval.Bisection.rightHalf span) data simple rightLift rightWithin _ positive
  exact { left, rightLift, right }

/-- A positive residual request divided by four is no larger than the original request. -/
private theorem quarter_le (positive : (0 : Fraction.Rational) < accuracy) : accuracy / 4 ≤ accuracy := by
  rewrite [Fraction.Field.div_eq_mul_inv_direct]
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide +kernel) positive.le).trans_eq
    (Fraction.Field.mul_one_direct _)

/-- The actual left child's coefficient is within the original parent's paid local allowance. -/
theorem left_error_le {parent : Cell data simple lift accuracy} (split : Split parent) :
    normSq (split.left.reading.center - parent.reading.center) ≤ parent.allowance := by
  have inside : span.Contains (Interval.Bisection.leftHalf span).lower := ⟨Fraction.Order.Basic.le_refl _, span.valid⟩
  have signed := split.left.signed.contains split.left.reading.centerRoot_inside
  have accurate := split.left.accurate.le.trans (quarter_le parent.positive)
  have result := parent.candidate_error_le inside signed split.left.reading.centerResidual accurate
  rewrite [split.left.reading.center_eq]
  exact result

/-- The actual right midpoint coefficient is within the same original parent's paid local allowance. -/
theorem right_error_le {parent : Cell data simple lift accuracy} (split : Split parent) :
    normSq (split.right.reading.center - parent.reading.center) ≤ parent.allowance := by
  have inside : span.Contains (Interval.Bisection.rightHalf span).lower :=
    ⟨Interval.Bisection.lower_le_midpoint span, Interval.Bisection.midpoint_le_upper span⟩
  have signed := split.right.signed.contains split.right.reading.centerRoot_inside
  have accurate := split.right.accurate.le.trans (quarter_le parent.positive)
  have result := parent.candidate_error_le inside signed split.right.reading.centerResidual accurate
  rewrite [split.right.reading.center_eq]
  exact result

/-- Both the chart-width and residual contributions of the left child are exactly one quarter of the parent. -/
theorem left_allowance_eq {parent : Cell data simple lift accuracy} (split : Split parent) :
    split.left.allowance = parent.allowance / 4 := by
  rewrite [split.left.allowance_eq, parent.allowance_eq]
  change data.chartSlope * (Interval.Bisection.leftHalf span).width ^ 2 +
    2 * data.residualSlope * (accuracy / 4) =
    (data.chartSlope * span.width ^ 2 + 2 * data.residualSlope * accuracy) / 4
  rewrite [Interval.Bisection.leftHalf_width,
    Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
  have inverseTwoSquare : ((2 : Fraction.Rational)⁻¹) ^ 2 = (4 : Fraction.Rational)⁻¹ := by decide +kernel
  rewrite [Fraction.Field.mul_pow_direct, inverseTwoSquare]
  ring1

/-- The right child's same retained span and residual request give the identical quarter allowance. -/
theorem right_allowance_eq {parent : Cell data simple lift accuracy} (split : Split parent) :
    split.right.allowance = parent.allowance / 4 := by
  rewrite [split.right.allowance_eq, parent.allowance_eq]
  change data.chartSlope * (Interval.Bisection.rightHalf span).width ^ 2 +
    2 * data.residualSlope * (accuracy / 4) =
    (data.chartSlope * span.width ^ 2 + 2 * data.residualSlope * accuracy) / 4
  rewrite [Interval.Bisection.rightHalf_width,
    Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
  have inverseTwoSquare : ((2 : Fraction.Rational)⁻¹) ^ 2 = (4 : Fraction.Rational)⁻¹ := by decide +kernel
  rewrite [Fraction.Field.mul_pow_direct, inverseTwoSquare]
  ring1

/-- Read the actual two children in their original left-to-right parameter order. -/
@[expose] def children {parent : Cell data simple lift accuracy} (split : Split parent) : Basic.PathModel :=
  ⟨[split.left.model, split.right.model]⟩

/-- The original ordered child displacements telescope exactly to the parent parameter displacement. -/
theorem displacement_eq {parent : Cell data simple lift accuracy} (split : Split parent) :
    Basic.PathModel.displacementSum split.children.cells = parent.model.displacement := by
  change (split.left.model.finish - split.left.model.start) +
    ((split.right.model.finish - split.right.model.start) + 0) = parent.model.finish - parent.model.start
  apply Purelib.Data.Gaussian.Basic.ext
  · change (Interval.Bisection.midpoint span - span.lower) +
      ((span.upper - Interval.Bisection.midpoint span) + 0) = span.upper - span.lower
    ring1
  · change ((0 : Fraction.Rational) - 0) + ((0 - 0) + 0) = 0 - 0
    ring1

/-- Derive the existing constant-partition comparison from the actual retained parent and child coefficients. -/
def comparison {parent : Cell data simple lift accuracy} (split : Split parent) :
    Basic.PathModel.ConstantPartitionCertificate parent.model
      (Basic.PathModel.comparisonBlock parent.model split.children) := by
  let first := split.left.model
  let last := split.right.model
  have firstError : Basic.Canonical.normSq (split.left.reading.center - parent.reading.center) ≤
      (Basic.PathModel.comparisonCell parent.model first).localAllowance := by
    rewrite [← Norm.Basic.normSq_eq_canonical]
    exact split.left_error_le.trans (Basic.PathModel.parentAllowance_le parent.model first)
  have lastError : Basic.Canonical.normSq (split.right.reading.center - parent.reading.center) ≤
      (Basic.PathModel.comparisonCell parent.model last).localAllowance := by
    rewrite [← Norm.Basic.normSq_eq_canonical]
    exact split.right_error_le.trans (Basic.PathModel.parentAllowance_le parent.model last)
  exact
    { reference := parent.reading.center
      parent_polynomial_eq := rfl
      errors := [split.left.reading.center - parent.reading.center, split.right.reading.center - parent.reading.center]
      comparison := .cons split.left.reading.center _ rfl rfl firstError
        (.cons split.right.reading.center _ rfl rfl lastError .nil)
      displacement_eq := by
        change (first.finish - first.start) + ((last.finish - last.start) + 0) = parent.model.displacement
        exact split.displacement_eq }

/-- The actual two-child model forms a compatible constant refinement of the same original parent cell. -/
def compatible {parent : Cell data simple lift accuracy} (split : Split parent) :
    Basic.PathModel.CompatibleConstantPathRefinement [parent.model] split.children.cells :=
  .cons split.comparison .nil

/-- Reweight both original children while retaining their exact midpoint lift and paid root observations. -/
@[expose] def reweight {parent : Cell data simple lift accuracy} (split : Split parent)
    {nextDifferential : OddPowerDifferential targetRadicand} (nextData : Bounds.Data site parameter nextDifferential)
    (nextSimple : nextDifferential.denominatorPairs = 0) : Split (parent.reweight nextData nextSimple) :=
  { left := split.left.reweight nextData nextSimple
    rightLift := split.rightLift
    right := split.right.reweight nextData nextSimple }

end Split

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement
