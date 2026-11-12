module
import Purelib.Data.List.Membership
import Purelib.Algebra.NatCast
import Purelib.Algebra.Semiring.Normalization
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Affine
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Uniform
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
import Purelib.Integration.Algebraic.SquareFactor.PathContinuation
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
public import Purelib.Integration.Algebraic.SquareFactor.OwnedCells
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Algebraic.SquareFactor.CellModels
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Quantitative bounds for the retained dyadic integration path

The exact squared displacement of each uniform leaf cancels the two finite
cell-count factors in the Gaussian path allowance.  The resulting bound is
the original segment's squared displacement times one local error budget,
not a bound which deteriorates as more cells are added.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.MeshBounds

open Purelib.Data.Gaussian.Norm.Basic (normSq_eq_canonical)
open Purelib.Integration.Polynomial.Gaussian.Path

open Purelib.Riemann
open Purelib.Riemann.Branches

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput
open Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
open Purelib.Integration.Algebraic.SquareFactor.PathContinuation
open Purelib.Integration.Algebraic.SquareFactor.OwnedCells
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat in
/-- The rational carrier for dyadic mesh bounds. -/
abbrev Coordinate := Fraction.Rational
/-- The original certified subdivision endpoint carrier. -/
abbrev Endpoint := ClearSheetContinuation.Subdivision.Endpoint
/-- The original ordered subdivision parameter-edge carrier. -/
abbrev ParameterEdge := ClearSheetContinuation.Subdivision.ParameterEdge

open Purelib.Algebra in
open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Dividing the initial scale by four advances the quarter-radius depth by one. -/
private theorem quarterRadius_div_four (scale : Coordinate) (depth : Nat) :
    Geometric.Basic.quarterRadius (scale / 4) depth =
      Geometric.Basic.quarterRadius scale (depth + 1) := by
  have scaleDiv : scale / 4 = scale * (1 / 4 : Coordinate) := by
    rw [Field.ExplicitField.div_eq_mul_inv, Field.ExplicitField.div_eq_mul_inv,
      Fraction.Field.one_mul]
  rw [Geometric.Basic.quarterRadius_eq_mul_pow,
    Geometric.Basic.quarterRadius_eq_mul_pow, scaleDiv, pow_succ]
  ring1

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Every retained dyadic edge has the original squared interval width scaled by the exact quarter radius. -/
theorem dyadic_width_sq (depth : Nat) (left right : Endpoint) (edge : ParameterEdge)
    (member : edge ∈ ClearSheetContinuation.Subdivision.dyadicEdges depth left right) :
    (edge.right.parameter - edge.left.parameter) ^ 2 =
      Geometric.Basic.quarterRadius ((right.parameter - left.parameter) ^ 2) depth := by
  induction depth generalizing left right with
  | zero =>
      have equal : edge = ⟨left, right⟩ := Data.List.Membership.mem_singleton.mp member
      cases equal
      rw [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
        Fraction.Field.mul_one_direct]
  | succ depth ih =>
      rcases Data.List.Membership.mem_append.mp member with member | member
      · rw [ih _ _ member]
        have halfWidth :
            (ClearSheetContinuation.midpoint left.parameter right.parameter - left.parameter) ^ 2 =
              (right.parameter - left.parameter) ^ 2 / 4 := by
          unfold ClearSheetContinuation.midpoint
          apply Fraction.Field.mul_right_cancel_of_ne
            (show (4 : Coordinate) ≠ 0 by decide)
          calc
            ((left.parameter + right.parameter) / 2 - left.parameter) ^ 2 * 4 =
                ((left.parameter + right.parameter) / 2 * 2 - left.parameter * 2) ^ 2 := by ring1
            _ = (right.parameter - left.parameter) ^ 2 := by
              rw [Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
              ring1
            _ = ((right.parameter - left.parameter) ^ 2 / 4) * 4 :=
              (Fraction.Field.div_mul_cancel_of_ne _ 4 (by decide)).symm
        change Geometric.Basic.quarterRadius
          ((ClearSheetContinuation.midpoint left.parameter right.parameter - left.parameter) ^ 2) depth = _
        rw [halfWidth, quarterRadius_div_four]
      · rw [ih _ _ member]
        have halfWidth :
            (right.parameter - ClearSheetContinuation.midpoint left.parameter right.parameter) ^ 2 =
              (right.parameter - left.parameter) ^ 2 / 4 := by
          unfold ClearSheetContinuation.midpoint
          apply Fraction.Field.mul_right_cancel_of_ne
            (show (4 : Coordinate) ≠ 0 by decide)
          calc
            (right.parameter - (left.parameter + right.parameter) / 2) ^ 2 * 4 =
                (right.parameter * 2 - (left.parameter + right.parameter) / 2 * 2) ^ 2 := by ring1
            _ = (right.parameter - left.parameter) ^ 2 := by
              rw [Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
              ring1
            _ = ((right.parameter - left.parameter) ^ 2 / 4) * 4 :=
              (Fraction.Field.div_mul_cancel_of_ne _ 4 (by decide)).symm
        change Geometric.Basic.quarterRadius
          ((right.parameter - ClearSheetContinuation.midpoint left.parameter right.parameter) ^ 2) depth = _
        rw [halfWidth, quarterRadius_div_four]

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Squared movement along an affine segment is squared direction norm times squared parameter displacement. -/
theorem pointMovement (segment : Segment) (left right : Coordinate) :
    Norm.Basic.normSq (segment.point right - segment.point left) =
      Norm.Basic.normSq segment.direction * (right - left) ^ 2 := by
  simp only [Segment.point, Affine.line, Norm.Basic.normSq, Basic.sub_re, Basic.sub_im,
    Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im, Cast.ofCoordinate_re,
    Cast.ofCoordinate_im]
  ring1

variable {polynomial : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {request :
  Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request}
  {prepared : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Prepared polynomial request} {segment :
    Purelib.Integration.Algebraic.SquareFactor.PathInput.Segment}
  {data : Purelib.Integration.Algebraic.SquareFactor.PathInput.Data prepared segment} {safe : data.Safe}

open Purelib.Integration.Algebraic.SquareFactor in
/-- The retained cell root enclosure meets its exact original step's strict diameter request. -/
theorem rootBox_diagonal_lt (cell : Cell safe) :
    cell.model.rootBox.diagonalSq < cell.edge.step.rootDiameter := by
  rw [cell.model_eq]
  change cell.edge.cached.preparedOwner.track.initial.box.diagonalSq < _
  rw [cell.edge.cached.preparedOwner_eq]
  exact PreparedSheetContinuation.prepared_diagonal_lt _ _ _ _

open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The retained cell allowance is bounded by parameter variation plus the original root-diameter contribution. -/
theorem cell_allowance_le (cell : Cell safe) :
    cell.model.cell.localAllowance ≤
      CoefficientBounds.parameterSlope data * cell.edge.span.width ^ 2 + CoefficientBounds.rootSlope data *
        cell.edge.step.rootDiameter := by
  change cell.model.allowance ≤ _
  rw [cell.model.allowance_eq]
  exact add_le_add (le_refl (CoefficientBounds.parameterSlope data * cell.edge.span.width ^ 2))
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (rootBox_diagonal_lt cell).le (CoefficientBounds.rootSlope_nonnegative safe))

open Purelib.Integration.Algebraic.SquareFactor in
/-- Every retained request created at a fixed diameter keeps that exact diameter. -/
private theorem request_diameter (diameter : Coordinate) (positive : 0 < diameter)
    (endpoints : List Endpoint) (step : PreparedSheetContinuation.StepRequest)
    (member : step ∈ PreparedSheetContinuation.Subdivision.requestsAtDiameter diameter positive endpoints) :
    step.rootDiameter = diameter := by
  induction endpoints with
  | nil => exact List.not_mem_nil member |>.elim
  | cons endpoint endpoints ih =>
      rcases Data.List.Membership.mem_cons.mp member with equal | member
      · cases equal; rfl
      · exact ih member

namespace CompiledRun

variable {sheet : Fin 2} {rootDiameter : Coordinate} {positive : 0
  < rootDiameter} {minimumDepth : Nat}
  (compiled : CompiledRun safe sheet rootDiameter positive
    minimumDepth)

section
open Purelib.Integration.Algebraic.SquareFactor
/-- The retained mesh's exact run is accepted by the original dyadic checker at its selected depth. -/
theorem accepted :
    PreparedSheetContinuation.Subdivision.tryDyadic (PathContinuation.clearSegment safe) (PathContinuation.within safe)
      PathContinuation.first PathContinuation.last (PathContinuation.initialOwner safe sheet) compiled.depth
      rootDiameter positive = some compiled.run := compiled.mesh.accepted

/-- The compiled parameter edges are exactly the selected unit-interval dyadic edges. -/
theorem parameterEdges :
    compiled.cells.map (fun cell => (⟨cell.edge.left, cell.edge.step.endpoint⟩ : ParameterEdge)) =
      ClearSheetContinuation.Subdivision.dyadicEdges compiled.depth PathContinuation.first last := by
  rw [compiled.cells_eq, OwnedCells.compileSubdivision_parameterEdges]
  exact PreparedSheetContinuation.Subdivision.tryDyadic_parameterEdges _ _ _ _ _ _ _ _ (accepted
    compiled)

/-- The compiled requests are exactly the original dyadic requests at the retained root diameter. -/
theorem requests : compiled.cells.map (fun cell => cell.edge.step) =
    PreparedSheetContinuation.Subdivision.dyadicRequests compiled.depth
      PathContinuation.first PathContinuation.last rootDiameter positive := by
  rw [compiled.cells_eq, OwnedCells.compileSubdivision_requests]
  exact PreparedSheetContinuation.Subdivision.tryDyadic_requests _ _ _ _ _ _ _ _ (accepted
    compiled)

end

open Purelib.Approximation.Rational in
open Purelib.Data.List in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Every retained compiled cell has squared parameter width equal to the unit quarter radius at the selected depth. -/
theorem width_sq (cell : Cell safe) (member : cell ∈ compiled.cells) :
    cell.edge.span.width ^ 2 = Geometric.Basic.quarterRadius 1
      compiled.depth := by
  have edgeMember : (⟨cell.edge.left, cell.edge.step.endpoint⟩ : ParameterEdge) ∈
      compiled.cells.map (fun child => (⟨child.edge.left, child.edge.step.endpoint⟩ : ParameterEdge)) :=
    Map.mem_map.mpr ⟨cell, member, rfl⟩
  rw [parameterEdges compiled] at edgeMember
  have width := dyadic_width_sq _ PathContinuation.first PathContinuation.last _ edgeMember
  have unitWidth : (last.parameter - first.parameter) ^ 2 = (1 :
    Coordinate) := by decide
  rw [unitWidth] at width
  exact width

open Purelib.Data.List in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Every retained compiled cell keeps the original requested root diameter. -/
theorem diameter (cell : Cell safe) (member : cell ∈ compiled.cells) :
    cell.edge.step.rootDiameter = rootDiameter := by
  have stepMember : cell.edge.step ∈ compiled.cells.map (fun child => child.edge.step) :=
    Map.mem_map.mpr ⟨cell, member, rfl⟩
  rw [requests compiled] at stepMember
  exact request_diameter rootDiameter positive _ _ stepMember

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Every retained compiled cell's squared displacement is the direction-norm quarter radius at the selected depth. -/
theorem displacement_sq (cell : Cell safe) (member : cell ∈ compiled.cells) :
    Norm.Basic.normSq cell.model.cell.displacement =
      Geometric.Basic.quarterRadius (Norm.Basic.normSq segment.direction)
        compiled.depth := by
  change Norm.Basic.normSq (segment.point cell.edge.span.interval.upper -
    segment.point cell.edge.span.interval.lower) = _
  rw [pointMovement]
  change Norm.Basic.normSq segment.direction * cell.edge.span.width ^ 2 = _
  rw [width_sq compiled cell member, Geometric.Basic.quarterRadius_eq_mul_pow,
    Geometric.Basic.quarterRadius_eq_mul_pow, Fraction.Field.one_mul]

open Purelib.Integration.Algebraic.SquareFactor.MeshBounds.CompiledRun in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Bound the retained compiled path allowance using the original direction norm, selected depth and root-diameter
request.

The parameter and root contributions retain their distinct coefficient slopes and the exact selected mesh's cell count.
-/
theorem aggregateAllowance_le :
    compiled.pathModel.aggregateAllowance ≤ Norm.Basic.normSq segment.direction *
      (CoefficientBounds.parameterSlope data * Geometric.Basic.quarterRadius 1
        compiled.depth + CoefficientBounds.rootSlope data * rootDiameter) := by
  apply Basic.PathModel.uniform_aggregateAllowance_le compiled.pathModel
    compiled.depth _ _ (Norm.Basic.normSq_nonneg segment.direction)
  · rw [compiled.cellCount]
    exact compiled.mesh.stepCount
  · intro model member
    rcases Map.mem_map.mp member with ⟨cell, cellMember, rfl⟩
    refine ⟨(displacement_sq compiled cell cellMember).le, ?_⟩
    have bound := cell_allowance_le cell
    rw [width_sq compiled cell cellMember, diameter compiled cell cellMember] at bound
    exact bound

end CompiledRun

end Purelib.Integration.Algebraic.SquareFactor.MeshBounds
