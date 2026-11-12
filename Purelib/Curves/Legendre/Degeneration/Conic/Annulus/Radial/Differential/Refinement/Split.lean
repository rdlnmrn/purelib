module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Approximation.AccuracyRequest.Scaling
public import Purelib.Data.Rat.Interval.Bisection
public import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Integration.Polynomial.Gaussian.Path.ConstantComparison
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Field

/-! # Actual midpoint refinement on the retained regular parallel quarter

The left child uses the identical original starting query and cofactor
certificate. The right child queries the same already prepared geometric
quarter at the actual midpoint once. Quarter residual requests and the
original uniform coefficient estimate derive both child comparisons and
exact quarter contraction of local allowances.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Approximation
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Riemann.RootContinuation

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}
variable {targetRadicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {span : Interval.Bounds} {inside : FixedRootBoxPath.Inside span.lower}
variable {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {source : Transport.Reading actual span.lower inside} {accuracy : AccuracyRequest}

/-- The actual midpoint of a retained span remains within its original geometric quarter. -/
theorem midpoint_inside (within : ∀ time, span.Contains time → FixedRootBoxPath.Inside time) :
    FixedRootBoxPath.Inside (Interval.Bisection.midpoint span) :=
  within _ ⟨Interval.Bisection.lower_le_midpoint span, Interval.Bisection.midpoint_le_upper span⟩

set_option genInjectivity false in
/-- Actual ordered midpoint children of one scalar cell on the identical original prepared parallel quarter.

The parent and its original whole-span containment remain indices. The left
child retains the complete starting query; the right child retains a single
actual midpoint query of that same prepared quarter.
-/
structure Split (parent : Cells.Model data source accuracy)
    (within : ∀ time, span.Contains time → FixedRootBoxPath.Inside time) where
  /-- The left child uses the identical original source query and one-quarter residual request. -/
  left : Cells.Model (span := Interval.Bisection.leftHalf span) data source accuracy.quarter
  /-- The complete original requested-time reading cached once at the actual midpoint. -/
  rightSource : Transport.Reading actual (Interval.Bisection.midpoint span) (midpoint_inside within)
  /-- The right child consumes that exact midpoint source and the identical quarter request. -/
  right : Cells.Model (span := Interval.Bisection.rightHalf span) data rightSource accuracy.quarter

constructive_injectivity Split

namespace Split

/-- Prepare both paid half-span cells while querying the same original prepared quarter at the midpoint once. -/
@[expose] def build (parent : Cells.Model data source accuracy)
    (within : ∀ time, span.Contains time → FixedRootBoxPath.Inside time) : Split parent within :=
  let left := Cells.Model.build (span := Interval.Bisection.leftHalf span) data source parent.regular accuracy.quarter
  let rightSource := Transport.Reading.build actual (Interval.Bisection.midpoint span) (midpoint_inside within)
  let right := Cells.Model.build (span := Interval.Bisection.rightHalf span)
    data rightSource parent.regular accuracy.quarter
  { left, rightSource, right }

variable {parent : Cells.Model data source accuracy}
variable {within : ∀ time, span.Contains time → FixedRootBoxPath.Inside time}

/-- The left child's actual coefficient meets the original parent's retained local allowance. -/
theorem left_error_le (split : Split parent within) :
    normSq (split.left.center - parent.center) ≤ parent.allowance := by
  have inside : span.Contains (Interval.Bisection.leftHalf span).lower :=
    ⟨Fraction.Order.Basic.le_refl _, span.valid⟩
  have paid := split.left.sample.reading_residual_lt.le.trans accuracy.quarter_le
  have result := parent.candidate_error_le inside split.left.signed split.left.residual paid
  rewrite [split.left.center_eq]
  exact result

/-- The right child's actual midpoint coefficient meets the identical parent's retained local allowance. -/
theorem right_error_le (split : Split parent within) :
    normSq (split.right.center - parent.center) ≤ parent.allowance := by
  have inside : span.Contains (Interval.Bisection.rightHalf span).lower :=
    ⟨Interval.Bisection.lower_le_midpoint span, Interval.Bisection.midpoint_le_upper span⟩
  have paid := split.right.sample.reading_residual_lt.le.trans accuracy.quarter_le
  have result := parent.candidate_error_le inside split.right.signed split.right.residual paid
  rewrite [split.right.center_eq]
  exact result

/-- The left half's squared chart width and residual request give exactly one quarter of the parent allowance. -/
theorem left_allowance_eq (split : Split parent within) : split.left.allowance = parent.allowance / 4 := by
  rewrite [split.left.allowance_eq, parent.allowance_eq]
  change Bounds.signedChartSlope data * (Interval.Bisection.leftHalf span).width ^ 2 +
    2 * Bounds.residualSlope data * accuracy.quarter.tolerance =
    (Bounds.signedChartSlope data * span.width ^ 2 + 2 * Bounds.residualSlope data * accuracy.tolerance) / 4
  rewrite [Interval.Bisection.leftHalf_width, AccuracyRequest.quarter_tolerance,
    Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
  have inverseTwoSquare : ((2 : Fraction.Rational)⁻¹) ^ 2 = (4 : Fraction.Rational)⁻¹ := by decide +kernel
  rewrite [Fraction.Field.mul_pow_direct, inverseTwoSquare]
  ring1

/-- The right half has the identical exact quarter contraction of the original paid local allowance. -/
theorem right_allowance_eq (split : Split parent within) : split.right.allowance = parent.allowance / 4 := by
  rewrite [split.right.allowance_eq, parent.allowance_eq]
  change Bounds.signedChartSlope data * (Interval.Bisection.rightHalf span).width ^ 2 +
    2 * Bounds.residualSlope data * accuracy.quarter.tolerance =
    (Bounds.signedChartSlope data * span.width ^ 2 + 2 * Bounds.residualSlope data * accuracy.tolerance) / 4
  rewrite [Interval.Bisection.rightHalf_width, AccuracyRequest.quarter_tolerance,
    Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
  have inverseTwoSquare : ((2 : Fraction.Rational)⁻¹) ^ 2 = (4 : Fraction.Rational)⁻¹ := by decide +kernel
  rewrite [Fraction.Field.mul_pow_direct, inverseTwoSquare]
  ring1

/-- Read the same two actual child cells in their original left-to-right chart order. -/
@[expose] def children (split : Split parent within) : Basic.PathModel :=
  ⟨[split.left.cell, split.right.cell]⟩

/-- The original ordered child chart displacements telescope to the parent's exact chart displacement. -/
theorem displacement_eq (split : Split parent within) :
    Basic.PathModel.displacementSum split.children.cells = parent.cell.displacement := by
  change (split.left.cell.finish - split.left.cell.start) +
    ((split.right.cell.finish - split.right.cell.start) + 0) = parent.cell.finish - parent.cell.start
  apply Purelib.Data.Gaussian.Basic.ext
  · change (Interval.Bisection.midpoint span - span.lower) +
      ((span.upper - Interval.Bisection.midpoint span) + 0) = span.upper - span.lower
    ring1
  · change ((0 : Fraction.Rational) - 0) + ((0 - 0) + 0) = 0 - 0
    ring1

/-- Derive the existing constant-partition certificate from the original actual parent and child coefficients. -/
def comparison (split : Split parent within) :
    Basic.PathModel.ConstantPartitionCertificate parent.cell
      (Basic.PathModel.comparisonBlock parent.cell split.children) := by
  let first := split.left.cell
  let last := split.right.cell
  have firstError : Basic.Canonical.normSq (split.left.center - parent.center) ≤
      (Basic.PathModel.comparisonCell parent.cell first).localAllowance := by
    rewrite [← Norm.Basic.normSq_eq_canonical]
    exact split.left_error_le.trans (Basic.PathModel.parentAllowance_le parent.cell first)
  have lastError : Basic.Canonical.normSq (split.right.center - parent.center) ≤
      (Basic.PathModel.comparisonCell parent.cell last).localAllowance := by
    rewrite [← Norm.Basic.normSq_eq_canonical]
    exact split.right_error_le.trans (Basic.PathModel.parentAllowance_le parent.cell last)
  exact
    { reference := parent.center
      parent_polynomial_eq := rfl
      errors := [split.left.center - parent.center, split.right.center - parent.center]
      comparison := .cons split.left.center _ rfl rfl firstError
        (.cons split.right.center _ rfl rfl lastError .nil)
      displacement_eq := split.displacement_eq }

/-- The actual ordered children form a compatible constant refinement of the original parent chart cell. -/
def compatible (split : Split parent within) :
    Basic.PathModel.CompatibleConstantPathRefinement [parent.cell] split.children.cells :=
  .cons split.comparison .nil

/-- Reweight the same completed split while retaining both full actual source queries and paid root samples. -/
@[expose] def reweight (split : Split parent within) {nextDifferential : OddPowerDifferential targetRadicand}
    (nextData : Waist.Differential.Bounds.Data site parameter nextDifferential) :
    Split (parent.reweight nextData) within :=
  { left := split.left.reweight nextData
    rightSource := split.rightSource
    right := split.right.reweight nextData }

/-- Reweighting a computed split gives the whole original split factory with its new differential.

The same midpoint Reading and both paid cofactor observations are retained.
Only the original scalar coefficients and allowances are recomputed.
-/
theorem reweight_build (parent : Cells.Model data source accuracy)
    (within : ∀ time, span.Contains time → FixedRootBoxPath.Inside time)
    {nextDifferential : OddPowerDifferential targetRadicand}
    (nextData : Waist.Differential.Bounds.Data site parameter nextDifferential) :
    (build parent within).reweight nextData = build (parent.reweight nextData) within := (rfl)

end Split

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement
