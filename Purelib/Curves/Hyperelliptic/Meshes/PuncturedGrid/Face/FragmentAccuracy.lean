module
import Purelib.Algebra.NatCast
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Monotonicity
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Bounds

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums
public import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Budget

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration.Polynomial.Rectangle.Accuracy

open Purelib.Polynomial.Dense.Gaussian.Bounds.Box

open Purelib.Riemann.Comparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedParentSplitting

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings

public section

/-!
# Requested accuracy of actual prepared mesh-fragment sums

The fixed enclosing-face majorants dominate every retained fragment. One
computed residual index pays their analytic errors; ownership has its own
computed tolerance. The estimate includes the complete fragment count.
-/

section

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts SegmentPiece SegmentSplit)
open Purelib.Riemann.Integration.PreparedParentSplitting (ParentSplits PreparedSplitMesh)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment (FragmentAccuracy)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums (FragmentReadings SplitReadings FragmentSum)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest RequestedParents)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest IndicesAbove)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg)
open Purelib.Approximation.Rational.Budget.Aggregate (countCoordinate countCoordinate_eq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {sheet : Fin 2} {columns rows : Nat} {geometry : Geometry
    columns rows}
  {patch : RectangularPatch models.bounds (models.frame.owners sheet)
    geometry}
  {differential : Differential genus} {bounds :
    FragmentBounds patch differential}
  {globalBounds : PrimitiveOverlapBounds face.clearance
    (Purelib.Riemann.Readings.PreparedPrimitiveSamples.differentialNumerator differential)}
  {fragments : Nat} {tolerance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentAccuracy

/-- At any later model stage, the original retained residual is bounded by the minimum-stage quarter-radius. -/
private theorem uniform_residual {polynomial : InverseRootPolynomial.Polynomial} {box : InverseRootPolynomial.Box}
  (model : InverseRootPolynomial.Model polynomial box)
    {minimum index : Nat} (later : minimum ≤ index) :
    Geometric.Basic.quarterRadius model.bound index ≤ Geometric.Basic.quarterRadius (1 / 16) minimum :=
  (quarterRadius_antitone model.bound_nonnegative later).trans (by
    simp only [Geometric.Basic.quarterRadius_eq_mul_pow]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct model.bound_small
      (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) minimum))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentAccuracy

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings.FragmentBounds

/-- Every local cached numerator bound is dominated by the same enclosing face calculation; the inverse ceiling is
unchanged by restriction. -/
theorem product_le (bounds
  : FragmentReadings.FragmentBounds patch differential)
    (globalBounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance
      (PreparedPrimitiveSamples.differentialNumerator differential))
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    bounds.numerator column row * bounds.inverse ≤ globalBounds.numeratorUpper * globalBounds.inverseUpper := by
  have numeratorLe : bounds.numerator column row ≤ globalBounds.numeratorUpper := by
    rw [bounds.numerator_eq, globalBounds.numeratorUpper_eq]
    exact (Polynomial.Dense.Gaussian.Bounds.Box.Monotonicity.denseHornerNormBounds_le_of_refines _ (patch.cell_refines
      column row)).1
  have inverseEq : bounds.inverse = globalBounds.inverseUpper := bounds.inverse_eq.trans
    globalBounds.inverseUpper_eq.symm
  rw [inverseEq]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct numeratorLe globalBounds.inverseUpper_positive.le

/-- The original requested fragment charge is less than half its retained per-fragment budget. -/
theorem charge_accurate
  (bounds : FragmentReadings.FragmentBounds patch differential)
    (budget : Fragment.FragmentAccuracy globalBounds columns fragments tolerance)
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} (piece :
      RectangularSegmentSplitting.SegmentPiece geometry (parent.edge.point 0) (parent.edge.point 1))
    {count : Nat} {target : InverseRootPolynomial.Coordinate} (request : UniformPreparedRequests.LocalRequest parent
      count target)
    (later : budget.minimumIndex ≤ request.request.index) :
    2 * bounds.charge piece request budget.grid.index < budget.perFragment / 2 := by
  let residual := Geometric.Basic.quarterRadius (1 / 16) budget.minimumIndex
  have residualNonnegative : 0 ≤ residual := Geometric.Basic.quarterRadius_nonneg (by decide +kernel) _
  have left := Face.FragmentAccuracy.uniform_residual (patch.transported.cell
    piece.column piece.row).model
    (budget.grid_ge.trans (Nat.le_add_right _ 2))
  have right := Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentAccuracy.uniform_residual
    request.neighborhood.base.model later
  have productNonnegative : 0 ≤ bounds.numerator piece.column piece.row * bounds.inverse :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (bounds.atCell piece.column piece.row).numeratorUpper_nonnegative
      (bounds.atCell piece.column piece.row).inverseUpper_positive.le
  have globalNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    globalBounds.numeratorUpper_nonnegative globalBounds.inverseUpper_positive.le
  have movement := Rational.Box.normSq_sub_le_diagonalSq
    ((patch.cell_refines piece.column piece.row).contains piece.last_inside)
    ((patch.cell_refines piece.column piece.row).contains piece.first_inside)
  have weightBound := Fraction.Order.Arithmetic.mul_le_mul_direct (bounds.product_le globalBounds piece.column
    piece.row)
    movement (Data.Gaussian.Norm.Basic.normSq_nonneg _) globalNonnegative
  have factorBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add left right)
    (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 12)
  have bound := Fraction.Order.Arithmetic.mul_le_mul_direct factorBound weightBound
    (Fraction.Order.Arithmetic.mul_nonneg_direct productNonnegative (Data.Gaussian.Norm.Basic.normSq_nonneg _))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg residualNonnegative residualNonnegative))
  have charged : bounds.charge piece request budget.grid.index ≤
      24 * residual * (globalBounds.numeratorUpper * globalBounds.inverseUpper) * face.cell.box.diagonalSq := by
    exact (by
        unfold FragmentReadings.FragmentBounds.charge;
        ring1 : bounds.charge piece request budget.grid.index = _).trans_le
      (bound.trans_eq (by change 12 * (residual + residual) * _ = _; ring1))
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct charged (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)).trans_lt
    ((by ring1 : 2 * (24 * residual * (globalBounds.numeratorUpper * globalBounds.inverseUpper) *
      face.cell.box.diagonalSq) =
      48 * residual * (globalBounds.numeratorUpper * globalBounds.inverseUpper) * face.cell.box.diagonalSq).trans_lt
        budget.analytic_accurate)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings.FragmentBounds

end

variable {budget : FragmentAccuracy globalBounds columns
  fragments tolerance}
  {primitives : Primitives
    (Purelib.Riemann.Branches.RectangularSheetGauge.Transitions.oriented (patch.sheets.refine
    budget.grid.index).transitions (patch.sheets.refine budget.grid.index).gauge)
    (Purelib.Riemann.Readings.PreparedPrimitiveSamples.differentialNumerator differential)}
  {anchors : PrimitiveAnchors primitives} {offsets :
    LinearAlgebra.Grid.Offsets anchors.edges}
  {cuts : GridCuts geometry} {meshParents : List
    (CenteredEdge curve differential)} {extra : List
    Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}
  {mesh : PreparedSplitMesh cuts meshParents extra}
  {readings : SharedPrimitiveValues anchors offsets
    mesh.mesh.surface} {count : Nat} {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings

/-- The retained fragment charges meet their original count-weighted budget.

Each cached charge obeys the same per-fragment ceiling. The original finite
list or split count adds those ceilings without changing any selected reading. -/
theorem chargeSum_le
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {request :
      UniformPreparedRequests.LocalRequest parent count target}
    {pieces : List (RectangularSegmentSplitting.SegmentPiece geometry (parent.edge.point 0) (parent.edge.point 1))}
    (entries : FragmentSums.FragmentReadings (gridRequest := budget.grid) bounds readings request pieces)
    (later : budget.minimumIndex ≤ request.request.index) :
    entries.chargeSum ≤ Aggregate.countCoordinate pieces.length * budget.perFragment := by
  rw [Aggregate.countCoordinate_eq]
  induction entries with
  | nil => change (0 : InverseRootPolynomial.Coordinate) ≤ 0 * budget.perFragment; rw [Fraction.Field.zero_mul_direct]
  | @cons piece pieces reading tail ih =>
      have charged : reading.charge < budget.perFragment := by
        rw [reading.charge_eq]
        exact (Fraction.Order.Arithmetic.add_lt_add_direct budget.ownership_accurate (bounds.charge_accurate budget
          piece request later)).trans_eq (by
          rw [show budget.perFragment / 2 + budget.perFragment / 2 = (budget.perFragment / 2) * 2 by ring1]
          exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
      exact (add_le_add charged.le ih).trans_eq (by
        simp only [List.length_cons, NatCast.add, Nat.cast_one]
        ring1)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings

/-- The retained fragment charges meet their original count-weighted budget.

Each cached charge obeys the same per-fragment ceiling. The original finite
list or split count adds those ceilings without changing any selected reading. -/
theorem chargeSum_le {parents :
  List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {splits : PreparedParentSplitting.ParentSplits
  cuts parents}
    {requests : UniformPreparedRequests.RequestedParents count target parents}
    (entries : FragmentSums.SplitReadings (gridRequest := budget.grid) bounds readings splits requests)
    (later : PreparedControlledPrimitiveRequests.IndicesAbove budget.minimumIndex requests) :
    entries.chargeSum ≤ Aggregate.countCoordinate splits.pieceCount * budget.perFragment := by
  induction entries with
  | nil => change (0 : InverseRootPolynomial.Coordinate) ≤ Aggregate.countCoordinate 0 * budget.perFragment
           rw [Aggregate.countCoordinate_eq, Nat.cast_zero, Fraction.Field.zero_mul_direct]
  | @cons parent parents split splits request requests entries tail ih =>
      exact (add_le_add (entries.chargeSum_le later.1) (ih later.2)).trans_eq (by
        simp only [ParentSplits.pieceCount, Aggregate.countCoordinate_eq, NatCast.add, split.count_eq]
        ring1)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentSum

/-- The original requested fragment sum pays the full retained tolerance using its exact fragment count and stage
floors. -/
theorem bound_lt {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {splits : PreparedParentSplitting.ParentSplits cuts
  parents}
    {requests : UniformPreparedRequests.RequestedParents count target parents}
    (summary : FragmentSums.FragmentSum (gridRequest := budget.grid) bounds readings splits requests)
    (countEq : splits.pieceCount = fragments) (later : PreparedControlledPrimitiveRequests.IndicesAbove
      budget.minimumIndex requests) :
    summary.bound < tolerance := by
  rw [summary.bound_eq, summary.fragmentCount_eq, summary.chargeSum_eq]
  have estimate := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (summary.entries.chargeSum_le later)
    ((Fraction.Cast.Order.natCast_le_direct (Nat.zero_le splits.pieceCount)).trans_eq (Aggregate.countCoordinate_eq
      _).symm)
  exact estimate.trans_lt (countEq ▸ budget.full_count_accurate)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentSum

end
