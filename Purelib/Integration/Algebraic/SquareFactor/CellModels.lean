module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Rat.Interval.Radius
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
public import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Riemann.Branches.SquareRootSheets
public import Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Integration.Polynomial.Gaussian

public section

/-!
# Constant integration cells for the transported differential

This numerical layer consumes a retained root window and a residual-certified
center from the continuation layer.  It constructs an ordinary integration
cell and proves a uniform error bound for every admitted root candidate in
that same window.  It neither chooses roots independently nor claims that an
empty observation list supplies uniform semantics.  The named/owner-backed
query and refinement layers must supply the root-window membership evidence.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.CellModels

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput
open Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat in
/-- The rational carrier for cell parameters and error allowances. -/
abbrev Coordinate := Fraction.Rational
/-- The rational Gaussian box carrier for retained root enclosures. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original Gaussian polynomial integration-cell carrier. -/
abbrev CellModel := Purelib.Integration.Polynomial.Gaussian.Cell.Basic.CellModel

open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
set_option genInjectivity false in
/-- A retained rational parameter interval with containment in the original unit interval.

The same ordered interval and refinement witness retain both endpoints inside the original unit parameter domain. -/
structure Span where
  /-- The retained original parameter interval. -/ interval : Data.Rat.Interval.Bounds
  /-- The retained parameter interval refines the original unit interval. -/ within : interval.Refines
    PathInput.unitInterval

constructive_injectivity Span

namespace Span

open Purelib.Integration.Algebraic.SquareFactor in
/-- The retained parameter span's upper endpoint minus its lower endpoint. -/
@[expose] def width (span : CellModels.Span) : Coordinate := span.interval.upper - span.interval.lower

open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The ordered retained parameter span has nonnegative width.

The original interval ordering supplies the direct scalar nonnegativity of its same upper-minus-lower width. -/
theorem width_nonnegative (span : CellModels.Span) : 0 ≤ span.width :=
  Fraction.Order.Arithmetic.sub_nonneg_direct span.interval.valid

open Purelib.Integration.Algebraic.SquareFactor in
/-- Map a local fraction affinely onto the retained original parameter span. -/
@[expose] def parameter (span : CellModels.Span) (fraction : CellModels.Coordinate) : Coordinate :=
  span.interval.lower + span.width * fraction

open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- An in-unit local fraction maps into the retained parameter span. -/
theorem parameter_inside (span : CellModels.Span) {fraction : CellModels.Coordinate}
    (inside : PathInput.unitInterval.Contains fraction) : span.interval.Contains (span.parameter fraction) := by
  constructor
  · exact le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.mul_nonneg_direct span.width_nonnegative inside.1)
  · calc
      span.parameter fraction ≤ span.interval.lower + span.width * 1 :=
        add_le_add (show span.interval.lower ≤ span.interval.lower from le_rfl)
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            inside.2 span.width_nonnegative)
      _ = span.interval.upper := by unfold CellModels.Span.width; ring1

open Purelib.Integration.Algebraic.SquareFactor.CellModels.Span in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Every point of the retained span remains inside the original unit interval. -/
theorem inside_unit (span : CellModels.Span) {parameter : CellModels.Coordinate}
    (inside : span.interval.Contains parameter) : PathInput.unitInterval.Contains parameter :=
  ⟨span.within.1.trans inside.1, inside.2.trans span.within.2⟩

open Purelib.Integration.Algebraic.SquareFactor in
/-- The retained span's lower endpoint lies in the original unit interval. -/
theorem lower_inside_unit (span : CellModels.Span) : PathInput.unitInterval.Contains span.interval.lower :=
  span.inside_unit ⟨le_rfl, span.interval.valid⟩

open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The mapped parameter's squared displacement from the lower endpoint is at most the retained width squared. -/
theorem parameter_sub_lower_sq_le (span : CellModels.Span) {fraction : CellModels.Coordinate}
    (inside : PathInput.unitInterval.Contains fraction) :
    (span.parameter fraction - span.interval.lower) ^ 2 ≤ span.width ^ 2 := by
  have bound := Interval.Radius.sub_sq_le_sampleRadiusSq span.interval
    (sample := span.interval.lower) (span.parameter_inside inside)
  rw [Interval.Radius.sampleRadiusSq_lower_eq_widthSq] at bound
  exact bound

end Span

variable {polynomial : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {request :
  Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request}
  {prepared : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Prepared polynomial request} {segment :
    Purelib.Integration.Algebraic.SquareFactor.PathInput.Segment}

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.Branches in
set_option genInjectivity false in
/-- A retained root enclosure and residual-certified starting root with cached coefficient and local variation
allowance.

The model is indexed by the exact original path data and parameter span; the coefficient and allowance retain their
defining equations. -/
structure Model (data : PathInput.Data prepared segment) (span : CellModels.Span) where
  /-- The retained original root enclosure. -/ rootBox : CellModels.Box
  /-- The original root reading at the span's lower endpoint. -/ centerRoot : SquareFactor.Gaussian
  /-- The original center root lies in its retained root box. -/ centerRootInside : rootBox.Contains centerRoot
  /-- The center root meets the original lower-endpoint square-residual target. -/ centerResidual :
    Data.Gaussian.Norm.Basic.normSq (centerRoot * centerRoot -
      prepared.reduction.radicand.eval (segment.point span.interval.lower)) ≤
    SquareRootSheets.residualTarget
      (prepared.reduction.radicand.eval (segment.point span.interval.lower))
  /-- The cached coefficient at the original span lower endpoint and center root. -/ center : SquareFactor.Gaussian
  /-- The cached center equals the exact coefficient readback of the original path data. -/ center_eq : center =
    CoefficientBounds.coefficient data span.interval.lower centerRoot
  /-- The retained local coefficient-variation allowance. -/ allowance : CellModels.Coordinate
  /-- The allowance is the sum of parameter-width and root-box-diagonal contributions. -/ allowance_eq : allowance =
    CoefficientBounds.parameterSlope data * span.width ^ 2 + CoefficientBounds.rootSlope data * rootBox.diagonalSq
  /-- The retained local allowance is nonnegative. -/ allowanceNonnegative : 0 ≤ allowance

constructive_injectivity Model

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.Branches in
/-- Build the coefficient model from the original safe path, span, root box and residual-certified root.

The local allowance combines parameter-slope times squared span width and root-slope times squared box diagonal,
retaining both contributions. -/
@[expose] def make {data : PathInput.Data prepared segment} (safe : data.Safe) (span : CellModels.Span)
    (rootBox : CellModels.Box) (centerRoot : SquareFactor.Gaussian) (centerRootInside : rootBox.Contains centerRoot)
    (centerResidual : Data.Gaussian.Norm.Basic.normSq (centerRoot * centerRoot -
        prepared.reduction.radicand.eval (segment.point span.interval.lower)) ≤
      SquareRootSheets.residualTarget
        (prepared.reduction.radicand.eval (segment.point span.interval.lower))) : CellModels.Model data span :=
  { rootBox, centerRoot, centerRootInside, centerResidual
    center := CoefficientBounds.coefficient data span.interval.lower centerRoot
    center_eq := rfl
    allowance := CoefficientBounds.parameterSlope data * span.width ^ 2 + CoefficientBounds.rootSlope data *
      rootBox.diagonalSq
    allowance_eq := rfl
    allowanceNonnegative := add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (CoefficientBounds.parameterSlope_nonnegative safe)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (CoefficientBounds.rootSlope_nonnegative safe)
        rootBox.diagonalSq_nonneg) }

namespace Model

variable {data : Purelib.Integration.Algebraic.SquareFactor.PathInput.Data prepared segment} {span :
  Purelib.Integration.Algebraic.SquareFactor.CellModels.Span}

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Polynomial.Ascending in
/-- Read the retained coefficient model as a constant Gaussian polynomial integration cell.

The original span endpoints determine the cell endpoints, its cached coefficient and allowance are reused, and its
observation list is empty. -/
@[expose] def cell (model : CellModels.Model data span) : CellModels.CellModel where
  start := segment.point span.interval.lower
  finish := segment.point span.interval.upper
  polynomial := Gaussian.Basic.constant model.center
  localAllowance := model.allowance
  localAllowance_nonneg := model.allowanceNonnegative
  observations := []

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The retained constant cell sample equals its exact span displacement times the cached coefficient. -/
theorem integralSample (model : CellModels.Model data span) :
    model.cell.integralSample =
      (segment.point span.interval.upper - segment.point span.interval.lower) * model.center :=
  Cell.Basic.CellModel.integralSample_constant _ _ rfl

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- The cell's local affine point equals the original segment evaluated at the mapped span parameter. -/
theorem point_eq (model : CellModels.Model data span) (fraction : CellModels.Coordinate) :
    model.cell.start + Cast.Path.ofCoordinate fraction * model.cell.displacement =
      segment.point (span.parameter fraction) := by
  apply Basic.ext <;>
    simp only [CellModels.Model.cell, Basic.CellModel.displacement,
      PathInput.Segment.point, PathInput.Segment.direction, Affine.line, CellModels.Span.parameter,
        CellModels.Span.width,
      Cast.ofCoordinate_re, Cast.ofCoordinate_im,
      Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Polynomial.Ascending in
open Purelib.Riemann.Branches in
/-- An in-box residual-certified root at an in-span parameter gives a coefficient reading within the retained cell
allowance.

The comparison uses the original center root, root box and separate parameter and root movement bounds. -/
theorem candidate_error_le (model : CellModels.Model data span) (safe : data.Safe)
    {fraction : CellModels.Coordinate} (inside : PathInput.unitInterval.Contains fraction)
    {root : SquareFactor.Gaussian} (rootInside : model.rootBox.Contains root)
    (residual : Data.Gaussian.Norm.Basic.normSq (root * root -
        prepared.reduction.radicand.eval (segment.point (span.parameter fraction))) ≤
      SquareRootSheets.residualTarget
        (prepared.reduction.radicand.eval (segment.point (span.parameter fraction)))) :
    Data.Gaussian.Norm.Basic.normSq (CoefficientBounds.coefficient data (span.parameter fraction) root -
      Gaussian.Evaluation.eval model.cell.polynomial ⟨fraction, 0⟩) ≤ model.cell.localAllowance := by
  have bound := CoefficientBounds.normSq_coefficient_sub_le_generated safe
    (span.inside_unit (span.parameter_inside inside)) span.lower_inside_unit
    (span.parameter_sub_lower_sq_le inside)
    (Box.normSq_sub_le_diagonalSq model.centerRootInside rootInside)
    residual model.centerResidual
  rw [CoefficientBounds.variation_eq_linear, ← model.center_eq, ← model.allowance_eq] at bound
  simpa only [CellModels.Model.cell, Gaussian.Evaluation.eval_constant] using bound

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Polynomial.Ascending in
open Purelib.Riemann.Branches in
/-- Build a local observation from the supplied residual-certified root and the retained model caches.

The original local fraction, actual coefficient reading and its difference from the cached center are retained with an
exact decomposition and error bound. -/
@[expose] def observation (model : CellModels.Model data span) (safe : data.Safe)
    (fraction : CellModels.Coordinate) (inside : PathInput.unitInterval.Contains fraction)
    (root : SquareFactor.Gaussian) (rootInside : model.rootBox.Contains root)
    (residual : Data.Gaussian.Norm.Basic.normSq (root * root -
        prepared.reduction.radicand.eval (segment.point (span.parameter fraction))) ≤
      SquareRootSheets.residualTarget
        (prepared.reduction.radicand.eval (segment.point (span.parameter fraction)))) :
    Basic.LocalObservation model.cell.polynomial model.cell.localAllowance :=
  { parameter := fraction
    integrandReading := CoefficientBounds.coefficient data (span.parameter fraction) root
    error := CoefficientBounds.coefficient data (span.parameter fraction) root - model.center
    decomposition := by rw [CellModels.Model.cell, Gaussian.Evaluation.eval_constant]
    error_le := by
      have bound := model.candidate_error_le safe inside rootInside residual
      rw [Norm.Basic.normSq_eq_canonical] at bound
      simpa only [CellModels.Model.cell, Gaussian.Evaluation.eval_constant] using bound }

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Polynomial.Ascending in
open Purelib.Riemann.Branches in
/-- A positive original square-factor margin transports the retained local error bound to the original differential
coefficient. -/
theorem original_candidate_error_le (model : CellModels.Model data span) (safe : data.Safe)
    (originalDomain : 0 < data.squareFactor.lowerBound)
    {fraction : CellModels.Coordinate} (inside : PathInput.unitInterval.Contains fraction)
    {root : SquareFactor.Gaussian} (rootInside : model.rootBox.Contains root)
    (residual : Data.Gaussian.Norm.Basic.normSq (root * root -
        prepared.reduction.radicand.eval (segment.point (span.parameter fraction))) ≤
      SquareRootSheets.residualTarget
        (prepared.reduction.radicand.eval (segment.point (span.parameter fraction)))) :
    Data.Gaussian.Norm.Basic.normSq (request.originalNumerator prepared.reduction (segment.point (span.parameter
      fraction)) /
        SquareFactor.coordinate prepared.reduction (segment.point (span.parameter fraction)) root -
      Gaussian.Evaluation.eval model.cell.polynomial ⟨fraction, 0⟩) ≤ model.cell.localAllowance := by
  have parameterInside := span.inside_unit (span.parameter_inside inside)
  have rootNonzero : root ≠ 0 := by
    intro zero
    have positive := (CoefficientBounds.rootLower_positive safe).trans_le (CoefficientBounds.rootLower_le safe
      parameterInside residual)
    rw [zero, Norm.Basic.normSq_zero] at positive
    exact (lt_irrefl _ positive).elim
  have bound := model.candidate_error_le safe inside rootInside residual
  rw [CoefficientBounds.coefficient_eq,
    data.coefficient_transport originalDomain parameterInside root rootNonzero] at bound
  exact bound

end Model

end Purelib.Integration.Algebraic.SquareFactor.CellModels
