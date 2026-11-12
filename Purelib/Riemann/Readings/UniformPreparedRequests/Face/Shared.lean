module

public import Purelib.Riemann.Readings.UniformPreparedRequests.Face.Pieces
public import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Paths.RectangularSegmentSplitting.Comparison
import Purelib.Algebra.NatCast
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Tactic.Ring

import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

/-! # Shared mesh readings on the actual contained fragment of a retained request

The retained sample, Entry, domain and split determine the signed analytic
comparison. Mesh membership supplies actual endpoint readings and their
ownership payment; both original residuals and the complete piece count remain.
-/

public section

namespace Purelib.Riemann.Readings.UniformPreparedRequests.LocalRequest

open Purelib
open Purelib.Algebra.FiniteSum.Rational
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels (CommonMesh)
open Purelib.LinearAlgebra.Grid (Offsets)
open Purelib.Riemann.Branches.RectangularSheetGauge
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Integration.PreparedParentSplitting.Geometry (allCells_mem)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Integration.RectangularSharedPrimitives.GridPrimitiveAccuracy (shared_local_increment_bound)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentPiece SegmentSplit)
open Purelib.Riemann.Readings.RectangularExteriorBoundary
open Purelib.Riemann.Integration.RectangularSharedPrimitives.SharedPrimitiveValues (atPoint atPoint_coordinate)
open Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {target : Coordinate}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {bank : BranchCellBank curve branches higher}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}
variable {face : Riemann.Meshes.PuncturedGridFaces.RegularFace bank}
variable {models : FaceModels frames face} {first last : Gaussian}

/-- One actual mesh-reading increment pays ownership and both original analytic residuals on the same retained piece.

The supplied sample and Entry derive the original sign. Point-bank inclusion
supplies actual selected-cell mesh lookups, and both unchanged polynomial
models pay their own residuals on the literal oriented endpoints.
-/
theorem faceSharedPiece_increment_le
    (request : LocalRequest parent count target)
    (sample : ContinuedNeighborhood.Point request.neighborhood first) (entry : Entry models first sample.owner)
    (domain : PeriodDomain models entry.sheet) (split : SegmentSplit domain.cuts first last)
    (fraction : Coordinate) (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1)
    (pointEq : parent.edge.point fraction = first)
    (firstInside : request.neighborhood.box.Contains first) (lastInside : request.neighborhood.box.Contains last)
    (bounds : FragmentBounds domain.patch differential)
    {globalBounds : PrimitiveOverlapBounds face.clearance (PreparedPrimitiveSamples.differentialNumerator differential)}
    {tolerance : Coordinate} (accuracy : GridPrimitiveAccuracy globalBounds domain.steps tolerance)
    {primitives : Primitives (Transitions.oriented (domain.patch.sheets.refine
      accuracy.index).transitions (domain.patch.sheets.refine accuracy.index).gauge)
      (PreparedPrimitiveSamples.differentialNumerator differential)}
    {anchors : PrimitiveAnchors primitives} {offsets : Offsets anchors.edges}
    {points : List Gaussian} (mesh : CommonMesh domain.geometry (Geometry.allCells domain.geometry) points)
    (included : ∀ point ∈ split.points, point ∈ points)
    (readings : SharedPrimitiveValues anchors offsets mesh.surface)
    (piece : SegmentPiece domain.geometry first last) (member : piece ∈ split.pieces) :
    normSq (((atPoint readings) piece.lastPoint -
      (atPoint readings) piece.firstPoint) -
      (request.request.model.primitive.value.eval piece.lastPoint -
        request.request.model.primitive.value.eval piece.firstPoint)) ≤
      32 * accuracy.globalBound + 2 * request.facePieceCharge domain bounds piece accuracy.index := by
  have ends := split.points_mem member
  let firstVertex := mesh.lookup piece.firstPoint (included _ ends.1) piece.column piece.row
    (allCells_mem domain.geometry _ _) piece.first_inside
  let lastVertex := mesh.lookup piece.lastPoint (included _ ends.2) piece.column piece.row
    (allCells_mem domain.geometry _ _) piece.last_inside
  have firstEq : mesh.surface.mesh.coordinate firstVertex.index = piece.firstPoint := firstVertex.coordinate_eq
  have lastEq : mesh.surface.mesh.coordinate lastVertex.index = piece.lastPoint := lastVertex.coordinate_eq
  have ownership := shared_local_increment_bound
    accuracy readings domain.patch.cell_refines piece.column piece.row firstVertex.index lastVertex.index
    (firstEq.symm ▸ piece.first_inside) (lastEq.symm ▸ piece.last_inside)
  rw [← atPoint_coordinate readings firstVertex.index,
    ← atPoint_coordinate readings lastVertex.index, firstEq, lastEq] at ownership
  rw [← Norm.Basic.normSq_eq_canonical] at ownership
  have analytic := request.facePiece_increment_le sample entry domain split fraction fractionInside pointEq
    firstInside lastInside bounds piece member primitives
  have identity : ((atPoint readings) piece.lastPoint -
      (atPoint readings) piece.firstPoint) -
      (request.request.model.primitive.value.eval piece.lastPoint -
        request.request.model.primitive.value.eval piece.firstPoint) =
      (((atPoint readings) piece.lastPoint -
        (atPoint readings) piece.firstPoint) -
        (primitives.value piece.column piece.row piece.lastPoint -
          primitives.value piece.column piece.row piece.firstPoint)) +
      ((primitives.value piece.column piece.row piece.lastPoint -
        primitives.value piece.column piece.row piece.firstPoint) -
        (request.request.model.primitive.value.eval piece.lastPoint -
          request.request.model.primitive.value.eval piece.firstPoint)) := by ring1
  rw [identity]
  exact (Bounds.normSq_add_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add ownership analytic) (by decide)).trans_eq
      (by ring1))

/-- Split the finite charge sum into ownership and analytic contributions.

Each original occurrence contributes the fixed ownership and analytic factors.
The equality separates their complete ordered sum without changing the entries. -/
private theorem charge_sum {α : Type} (items : List α) (charges : α → Coordinate) (constant :
  Coordinate) :
    Squares.coordinateSum (items.map fun item => 32 * constant + 2 * charges item) =
      32 * Aggregate.countCoordinate items.length * constant + 2 * Squares.coordinateSum (items.map charges) := by
  simp only [Aggregate.countCoordinate_eq]
  induction items with
  | nil => change (0 : Coordinate) = 32 * 0 * constant + 2 * 0; ring1
  | cons head tail ih =>
      simp only [List.map_cons, Squares.coordinateSum, List.length_cons, Algebra.NatCast.add, Nat.cast_one, ih]
      ring1

/-- The actual retained split pays the complete shared-reading discrepancy with its full piece count.

The supplied point-bank membership is used for every original selected cell.
Constants remain in one shared reading owner, and the original request's
polynomial telescopes on its own retained oriented split.
-/
theorem faceSharedSplit_increment_le
    (request : LocalRequest parent count target)
    (sample : ContinuedNeighborhood.Point request.neighborhood first) (entry : Entry models first sample.owner)
    (domain : PeriodDomain models entry.sheet) (split : SegmentSplit domain.cuts first last)
    (fraction : Coordinate) (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1)
    (pointEq : parent.edge.point fraction = first)
    (firstInside : request.neighborhood.box.Contains first) (lastInside : request.neighborhood.box.Contains last)
    (bounds : FragmentBounds domain.patch differential)
    {globalBounds : PrimitiveOverlapBounds face.clearance (PreparedPrimitiveSamples.differentialNumerator differential)}
    {tolerance : Coordinate} (accuracy : GridPrimitiveAccuracy globalBounds domain.steps tolerance)
    {primitives : Primitives (Transitions.oriented (domain.patch.sheets.refine
      accuracy.index).transitions (domain.patch.sheets.refine accuracy.index).gauge)
      (PreparedPrimitiveSamples.differentialNumerator differential)}
    {anchors : PrimitiveAnchors primitives} {offsets : Offsets anchors.edges}
    {points : List Gaussian} (mesh : CommonMesh domain.geometry (Geometry.allCells domain.geometry) points)
    (included : ∀ point ∈ split.points, point ∈ points)
    (readings : SharedPrimitiveValues anchors offsets mesh.surface) :
    normSq (((atPoint readings) last - (atPoint readings) first) -
      (request.request.model.primitive.value.eval last - request.request.model.primitive.value.eval first)) ≤
      Aggregate.countCoordinate split.count * (32 * Aggregate.countCoordinate split.count * accuracy.globalBound +
        2 * Squares.coordinateSum (split.pieces.map fun piece =>
          request.facePieceCharge domain bounds piece accuracy.index)) := by
  let charges := fun (piece : SegmentPiece domain.geometry first last) =>
    32 * accuracy.globalBound + 2 * request.facePieceCharge domain bounds piece accuracy.index
  have original := split.increment_difference_map_le (atPoint readings)
    request.request.model.primitive.value.eval charges
    (fun piece member => request.faceSharedPiece_increment_le sample entry domain split fraction fractionInside pointEq
      firstInside lastInside bounds accuracy mesh included readings piece member)
  exact original.trans_eq (by
    dsimp only [charges]
    rw [charge_sum, split.count_eq, Aggregate.countCoordinate_eq])

end Purelib.Riemann.Readings.UniformPreparedRequests.LocalRequest

end
