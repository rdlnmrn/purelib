module
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.ComparisonAllowance

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Algebraic.SquareFactor.CellModels
import Purelib.Integration.Algebraic.SquareFactor.ChildCells
import Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
import Purelib.Integration.Algebraic.SquareFactor.MeshBounds
import Purelib.Integration.Algebraic.SquareFactor.OwnedCells
import Purelib.Integration.Algebraic.SquareFactor.PathContinuation
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
public import Purelib.Integration.Algebraic.SquareFactor.ChildMeshes
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Rat.Interval.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Mesh-size-independent comparison bounds for direct children

The child block retains the exact uniform physical geometry.  Its finite
Cauchy--Schwarz count cancels squared displacement decay, so the comparison
pays only for the parent's uncertainty and the new children's uncertainty.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.ChildBounds

open Purelib.Riemann
open Purelib.Riemann.Branches Purelib.Integration.Algebraic.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.ChildMeshes (Block)

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput
open Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
open Purelib.Integration.Algebraic.SquareFactor.PathContinuation
open Purelib.Integration.Algebraic.SquareFactor.OwnedCells
open Purelib.Integration.Algebraic.SquareFactor.ChildCells

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat in
/-- The rational carrier for child refinement allowances. -/
abbrev Coordinate := Fraction.Rational

variable {polynomial : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {request :
  Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request}
  {prepared : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Prepared polynomial request} {segment :
    Purelib.Integration.Algebraic.SquareFactor.PathInput.Segment}
  {data : Purelib.Integration.Algebraic.SquareFactor.PathInput.Data prepared segment} {safe : data.Safe}

namespace Block

variable {parent : Purelib.Integration.Algebraic.SquareFactor.OwnedCells.Cell safe} {diameter :
  Purelib.Integration.Algebraic.SquareFactor.ChildBounds.Coordinate} {depth : Nat}
  (block : Purelib.Integration.Algebraic.SquareFactor.ChildMeshes.Block parent diameter depth)

/-- The retained child block has exactly two to the power of its original depth cells. -/
theorem cellCount : block.cells.length = 2 ^ depth := by
  rw [block.cells_eq, block.mesh.cellCount]

open Purelib.Approximation.Rational in
open Purelib.Data.List in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.Branches in
/-- Each retained child's squared parameter width is the original parent's width scaled by the depth's quarter radius.
-/
theorem width_sq (cell : OwnedCells.Cell safe) (member : cell ∈ block.cells) :
    cell.edge.span.width ^ 2 =
      Geometric.Basic.quarterRadius (parent.edge.span.width ^ 2) depth := by
  have edgeMember : (⟨cell.edge.left, cell.edge.step.endpoint⟩ : ClearSheetContinuation.Subdivision.ParameterEdge) ∈
      block.cells.map (fun child =>
        (⟨child.edge.left, child.edge.step.endpoint⟩ : ClearSheetContinuation.Subdivision.ParameterEdge)) :=
    Map.mem_map.mpr ⟨cell, member, rfl⟩
  rw [block.cells_eq, block.mesh.parameterEdges] at edgeMember
  have bound := MeshBounds.dyadic_width_sq _ _ _ _ edgeMember
  simpa only [ChildCells.endpointAt, PathContinuation.first, PathContinuation.last, OwnedCells.Edge.parameter,
    PreparedSheetContinuation.parameterAt_zero,
    PreparedSheetContinuation.parameterAt_one, CellModels.Span.width, OwnedCells.Edge.span] using bound

open Purelib.Integration.Algebraic.SquareFactor in
/-- Each retained child keeps the exact original block diameter request. -/
theorem diameter_eq (cell : OwnedCells.Cell safe) (member : cell ∈ block.cells) : cell.edge.step.rootDiameter = diameter
  := by
  rw [block.cells_eq] at member
  exact block.mesh.diameters cell member

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Each retained child's squared displacement is the original parent displacement norm scaled by the quarter radius. -/
theorem displacement_sq (cell : OwnedCells.Cell safe) (member : cell ∈ block.cells) :
    Data.Gaussian.Norm.Basic.normSq cell.model.cell.displacement =
      Geometric.Basic.quarterRadius (Data.Gaussian.Norm.Basic.normSq parent.model.cell.displacement)
        depth := by
  change Data.Gaussian.Norm.Basic.normSq (segment.point cell.edge.span.interval.upper - segment.point
    cell.edge.span.interval.lower) =
    Geometric.Basic.quarterRadius
      (Data.Gaussian.Norm.Basic.normSq (segment.point parent.edge.span.interval.upper - segment.point
        parent.edge.span.interval.lower)) _
  rw [MeshBounds.pointMovement, MeshBounds.pointMovement]
  change Data.Gaussian.Norm.Basic.normSq segment.direction * cell.edge.span.width ^ 2 =
    Geometric.Basic.quarterRadius (Data.Gaussian.Norm.Basic.normSq segment.direction * parent.edge.span.width ^ 2) _
  rw [ChildBounds.Block.width_sq block cell member, Geometric.Basic.quarterRadius_eq_mul_pow,
    Geometric.Basic.quarterRadius_eq_mul_pow]
  ring1

open Purelib.Approximation.Rational in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The child-block local allowance bound, retaining separate parameter-width and root-diameter contributions. -/
@[expose] def localBound (_block : ChildMeshes.Block parent diameter depth) : Coordinate :=
  CoefficientBounds.parameterSlope data * Geometric.Basic.quarterRadius (parent.edge.span.width ^ 2)
    depth + CoefficientBounds.rootSlope data * diameter

open Purelib.Integration.Algebraic.SquareFactor in
/-- Each retained child cell's local allowance meets the original block's explicit local bound. -/
theorem cell_allowance_le (cell : OwnedCells.Cell safe) (member : cell ∈ block.cells) :
    cell.model.cell.localAllowance ≤ (ChildBounds.Block.localBound block) := by
  have bound := MeshBounds.cell_allowance_le cell
  rw [ChildBounds.Block.width_sq block cell member, ChildBounds.Block.diameter_eq block cell member] at bound
  exact bound

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The retained child path's aggregate allowance is bounded by the original parent displacement norm times the local
bound. -/
theorem aggregateAllowance_le : block.pathModel.aggregateAllowance ≤
    Data.Gaussian.Norm.Basic.normSq parent.model.cell.displacement * (ChildBounds.Block.localBound block) := by
  apply MeshBounds.uniform_aggregateAllowance_le block.pathModel
    depth _ _ (Norm.Basic.normSq_nonneg parent.model.cell.displacement)
  · rw [ChildMeshes.Block.pathModel, Purelib.Data.List.Map.length_map,
      ChildBounds.Block.cellCount block]
  · intro model member
    rcases Map.mem_map.mp member with ⟨cell, cellMember, rfl⟩
    exact ⟨(ChildBounds.Block.displacement_sq block cell cellMember).le, ChildBounds.Block.cell_allowance_le block cell
      cellMember⟩

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The retained comparison path's aggregate allowance meets the original parent-and-child local budget.

The bound preserves the factor of two and the separate original parent allowance and child local bound. -/
theorem comparisonAllowance_le :
    (Basic.PathModel.comparisonBlock parent.model.cell block.pathModel).aggregateAllowance ≤
      Data.Gaussian.Norm.Basic.normSq parent.model.cell.displacement * (2 * (parent.model.cell.localAllowance +
        (ChildBounds.Block.localBound block))) := by
  apply MeshBounds.uniform_aggregateAllowance_le
    (Basic.PathModel.comparisonBlock parent.model.cell block.pathModel) depth
    _ _ (Norm.Basic.normSq_nonneg parent.model.cell.displacement)
  · rw [Basic.PathModel.comparisonBlock, Purelib.Data.List.Map.length_map,
      ChildMeshes.Block.pathModel,
      Purelib.Data.List.Map.length_map, ChildBounds.Block.cellCount block]
  · intro model member
    rcases Map.mem_map.mp member with ⟨child, childMember, rfl⟩
    rcases Map.mem_map.mp childMember with ⟨cell, cellMember, rfl⟩
    refine ⟨(ChildBounds.Block.displacement_sq block cell cellMember).le, ?_⟩
    change 2 * (parent.model.cell.localAllowance + cell.model.cell.localAllowance) ≤ _
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (le_refl parent.model.cell.localAllowance) (ChildBounds.Block.cell_allowance_le block cell
        cellMember)) (by decide)

open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The retained child-minus-parent integral sample meets the explicit original parent-and-child comparison budget. -/
theorem integral_difference_le_budget :
    Data.Gaussian.Norm.Basic.normSq (block.pathModel.integralSample - parent.model.cell.integralSample) ≤
      Data.Gaussian.Norm.Basic.normSq parent.model.cell.displacement * (2 * (parent.model.cell.localAllowance +
        (ChildBounds.Block.localBound block))) :=
  block.integral_difference_le.trans (ChildBounds.Block.comparisonAllowance_le block)

end Block

end Purelib.Integration.Algebraic.SquareFactor.ChildBounds
