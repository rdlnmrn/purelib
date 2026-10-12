module

import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Riemann.Readings.PreparedPrimitiveRequestWeakening
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks

import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap

public section

/-!
# Requested cancellation of actual opposite-sheet face-corner increments

Both original four-corner caches are compared through every piece of the
retained two-grid split. The proof pays cell ownership, all fragment counts,
the actual local primitive residuals, and both final corner-owner changes.
Auxiliary point evaluations below occur only in erased proofs.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeCancellation

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
open Purelib.Riemann.Comparison
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.RectangularPrimitiveGluing
open Purelib.Riemann.Normalization
open Purelib.Riemann.Paths
open Purelib.Riemann.Readings

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomains)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests (PairedEdgeRequest)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank}

/-- The two retained one-in-256 ownership allowances, scaled by thirty-two, pay one quarter of the original amount. -/
private theorem scale_256 (amount : InverseRootPolynomial.Coordinate) : 32 * (amount / 256 + amount / 256) = amount / 4
  := by
  apply Fraction.Field.mul_right_cancel_of_ne (by decide : (4 : InverseRootPolynomial.Coordinate) ≠ 0)
  rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
  calc
    _ = (amount / 256) * 256 := by ring1
    _ = amount := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)

/-- Two quarter allowances, scaled by two, recover exactly the original rational amount. -/
private theorem quarters (amount : InverseRootPolynomial.Coordinate) : 2 * (amount / 4 + amount / 4) = amount := by
  rw [show 2 * (amount / 4 + amount / 4) = (amount / 4) * 4 by ring1]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

/-- Read the retained aligned primitive at its located face cell, returning zero outside the original face. -/
private def value {models : BranchCellBank.FaceModels frames face} {sheet : Fin 2} {domain : Periods.PeriodDomain models
  sheet}
    {differential : Differentials.Basic.Differential genus} {index : Nat} (data : PrimitiveData.DomainPrimitives domain
      differential index) (point : InverseRootPolynomial.Gaussian) : Gaussian :=
  if inside : face.cell.box.Contains point then
    let located := PeriodDomain.locate domain point inside
    data.anchors.alignedValue data.offsets located.column located.row point
  else 0

/-- The actual point reading differs from any retained containing-cell reading by at most four times the grid overlap
bound. -/
private theorem value_bound {models : BranchCellBank.FaceModels frames face} {sheet : Fin 2} {domain :
  Periods.PeriodDomain models sheet}
    {differential : Differentials.Basic.Differential genus}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)} {target : InverseRootPolynomial.Coordinate}
    (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds domain.steps target) (data :
      PrimitiveData.DomainPrimitives domain differential request.index)
    (column row : Fin (domain.steps + 1)) (point : InverseRootPolynomial.Gaussian) (inside : (domain.geometry.box column
      row).Contains point) :
    Data.Gaussian.Norm.Basic.normSq
      (value data point -
      data.anchors.alignedValue data.offsets column row point) ≤ 4 * request.globalBound := by
  have contained := (domain.patch.cell_refines column row).contains inside
  rw [value, dif_pos contained]
  have scalar := request.overlap_bound data.anchors data.offsets domain.patch.cell_refines
    (PeriodDomain.locate domain point contained).column column
    (PeriodDomain.locate domain point contained).row row
    (PeriodDomain.locate domain point contained).inside inside
  simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using scalar

/-- The actual endpoint increment differs from the retained cell primitive increment by at most sixteen times the grid
overlap bound. -/
private theorem increment_bound {models : BranchCellBank.FaceModels frames face} {sheet : Fin 2} {domain :
  Periods.PeriodDomain models sheet}
    {differential : Differentials.Basic.Differential genus}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)} {target : InverseRootPolynomial.Coordinate}
    (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds domain.steps target) (data :
      PrimitiveData.DomainPrimitives domain differential request.index)
    (column row : Fin (domain.steps + 1)) (first last : InverseRootPolynomial.Gaussian)
    (firstInside : (domain.geometry.box column row).Contains first) (lastInside : (domain.geometry.box column
      row).Contains last) :
    Data.Gaussian.Norm.Basic.normSq
      ((value data last -
      value data first) -
      (data.primitives.value column row last - data.primitives.value column row first)) ≤ 16 * request.globalBound := by
  have firstBound := value_bound request data
    column row first firstInside
  have lastBound := value_bound request data
    column row last lastInside
  have identity : (value data last -
    value data first) -
      (data.primitives.value column row last - data.primitives.value column row first) =
      (value data last - data.anchors.alignedValue
        data.offsets column row last) -
        (value data first -
          data.anchors.alignedValue data.offsets column row first) := by
    simp only [PrimitiveAnchors.alignedValue]
    ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct lastBound firstBound) (by decide)).trans_eq (by ring1))

/-- The original cached corner increment differs from the located point-reading increment by the paid grid-owner
allowance. -/
private theorem corners_bound {models : BranchCellBank.FaceModels frames face} {sheet : Fin 2} {domain :
  Periods.PeriodDomain models sheet}
    {differential : Differentials.Basic.Differential genus}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)} {target : InverseRootPolynomial.Coordinate}
    (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds domain.steps target) (data :
      PrimitiveData.DomainPrimitives domain differential request.index)
    (first last : Fin 4) :
    Data.Gaussian.Norm.Basic.normSq ((data.corners.values last - data.corners.values first) -
      (value data (FaceCorners.point face.cell.box
        last) - value data (FaceCorners.point
        face.cell.box first))) ≤
        16 * request.globalBound := by
  have corner (which : Fin 4) : Data.Gaussian.Norm.Basic.normSq
    (value data (FaceCorners.point face.cell.box
    which) - data.corners.values which) ≤
      4 * request.globalBound := by
    rw [data.corners.value_eq, data.corners.point_eq]
    exact value_bound request data _ _ _
      ((data.corners.point_eq which) ▸ (data.corners.owners which).contains)
  have identity : (data.corners.values last - data.corners.values first) -
      (value data (FaceCorners.point face.cell.box
        last) - value data (FaceCorners.point
        face.cell.box first)) =
      (value data (FaceCorners.point face.cell.box
        first) - data.corners.values first) -
        (value data (FaceCorners.point
          face.cell.box last) - data.corners.values last) := by ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (corner first) (corner last)) (by decide)).trans_eq (by ring1))

variable {domains : FaceDomains frames face}
  {differential : Differential genus} {start finish :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian} {target :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

/-- The sum of actual opposite-sheet increments on one retained split piece satisfies its paid local target. -/
private theorem piece_accurate (request : PairedEdgeRequests.PairedEdgeRequest domains differential start finish target)
    {leftIndex rightIndex : Nat}
    (first : PrimitiveData.DomainPrimitives (domains.domain 0) differential leftIndex)
    (second : PrimitiveData.DomainPrimitives (domains.domain 1) differential rightIndex)
    (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex)
    (piece : RectangularPairedSegments.PairedSegmentPiece (domains.domain 0).geometry (domains.domain 1).geometry)
    (member : piece ∈ request.split.pieces) :
    Data.Gaussian.Norm.Basic.normSq
      ((value first piece.last -
      value first piece.first) +
      (value second piece.last -
        value second piece.first)) <
        request.perPiece := by
  let leftGrid := GridPrimitiveAccuracy.atIndex
    request.leftGrid leftIndex (request.left_later.trans leftLater)
  let rightGrid := GridPrimitiveAccuracy.atIndex
    request.rightGrid rightIndex (request.right_later.trans rightLater)
  let leftIncrement := first.primitives.value piece.leftColumn piece.leftRow piece.last -
    first.primitives.value piece.leftColumn piece.leftRow piece.first
  let rightIncrement := second.primitives.value piece.rightColumn piece.rightRow piece.last -
    second.primitives.value piece.rightColumn piece.rightRow piece.first
  let leftError := (value first piece.last -
    value first piece.first) - leftIncrement
  let rightError := (value second piece.last -
    value second piece.first) - rightIncrement
  have leftOwnership : Data.Gaussian.Norm.Basic.normSq leftError ≤ 16 * leftGrid.globalBound :=
    increment_bound leftGrid first _ _ _ _
      piece.leftFirst piece.leftLast
  have rightOwnership : Data.Gaussian.Norm.Basic.normSq rightError ≤ 16 * rightGrid.globalBound :=
    increment_bound rightGrid second _ _ _ _
      piece.rightFirst piece.rightLast
  have ownership : Data.Gaussian.Norm.Basic.normSq (leftError + rightError) ≤ 32 * (leftGrid.globalBound +
    rightGrid.globalBound) :=
    (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct leftOwnership rightOwnership) (by decide)).trans_eq (by ring1))
  have analytic : Data.Gaussian.Norm.Basic.normSq (leftIncrement + rightIncrement) < request.perPiece / 4 :=
    request.locals.accurate first second (request.locals_later.trans leftLater)
      (request.locals_later.trans rightLater) piece member
  have ownershipSmall : 32 * (leftGrid.globalBound + rightGrid.globalBound) < request.perPiece / 4 := by
    have bound := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 32)
      (Fraction.Order.Arithmetic.add_lt_add_direct leftGrid.accurate rightGrid.accurate)
    exact bound.trans_eq (scale_256 _)
  have identity : (value first piece.last -
    value first piece.first) +
      (value second piece.last -
        value second piece.first) =
      (leftError + rightError) + (leftIncrement + rightIncrement) := by
    dsimp only [leftError, rightError]
    ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
      (Fraction.Order.Arithmetic.add_lt_add_direct (ownership.trans_lt ownershipSmall) analytic)).trans_eq
        (quarters _))

/-- The actual opposite-sheet whole-edge increments cancel within one quarter of the original target after summing every
retained piece.

The original split supplies the retained entries and count. The finite sum uses those same increments, so its bound
depends on the stored list length. -/
private theorem values_accurate (request : PairedEdgeRequests.PairedEdgeRequest domains differential start finish
  target)
    {leftIndex rightIndex : Nat}
    (first : PrimitiveData.DomainPrimitives (domains.domain 0) differential leftIndex)
    (second : PrimitiveData.DomainPrimitives (domains.domain 1) differential rightIndex)
    (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex) :
    Data.Gaussian.Norm.Basic.normSq
      ((value first finish -
      value first start) +
      (value second finish -
      value second start)) < target / 4 := by
  let values := request.split.pieces.map fun piece =>
    (value first piece.last -
      value first piece.first) +
      (value second piece.last -
      value second piece.first)
  have telescope : Data.Gaussian.Norm.Sum.Basic.gaussianSum values =
    (value first finish -
    value first start) +
    (value second finish -
    value second start) := by
    have same := request.split.telescope (fun point =>
      value first point +
      value second point)
    have mapped : values = request.split.pieces.map
        (fun piece => (value first piece.last +
          value second piece.last) -
          (value first piece.first +
          value second piece.first)) := by
      have mapped (pieces : List (RectangularPairedSegments.PairedSegmentPiece (domains.domain 0).geometry
        (domains.domain 1).geometry)) :
          (pieces.map fun piece => (value first
            piece.last - value first piece.first)
            +
            (value second piece.last -
              value second piece.first)) =
          pieces.map (fun piece => (value first
            piece.last + value second piece.last)
            -
            (value first piece.first +
              value second piece.first)) := by
        induction pieces with
        | nil => rfl
        | cons piece rest ih =>
            exact congrArg₂ List.cons (by ring1) ih
      exact mapped request.split.pieces
    rw [mapped, same]
    ring1
  rw [← telescope]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ (Fraction.Order.Field.div_pos_direct request.positive (by decide))
  intro element member
  obtain ⟨piece, present, equal⟩ := Map.mem_map.mp member
  rw [← equal]
  have accurate := (piece_accurate request first
    second leftLater rightLater piece present).le
  have count : values.length = request.split.count := by rw [Map.length_map, ← request.split.count_eq]
  rw [count, ← request.perPiece_eq]
  exact accurate

/-- Whole-edge cancellation for the original corner banks used by lifted triangles and cut-period comparisons.

No fragment, sign, transport, or analytic certificate is supplied beyond the automatically built request. -/
theorem corners_accurate (request : PairedEdgeRequests.PairedEdgeRequest domains differential start finish target)
    {leftIndex rightIndex : Nat}
    (first : PrimitiveData.DomainPrimitives (domains.domain 0) differential leftIndex)
    (second : PrimitiveData.DomainPrimitives (domains.domain 1) differential rightIndex)
    (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex)
    (firstCorner lastCorner : Fin 4)
    (firstEq : FaceCorners.point face.cell.box firstCorner = start)
    (lastEq : FaceCorners.point face.cell.box lastCorner = finish) :
    Data.Gaussian.Norm.Basic.normSq ((first.corners.values lastCorner - first.corners.values firstCorner) +
      (second.corners.values lastCorner - second.corners.values firstCorner)) < target := by
  let leftGrid := GridPrimitiveAccuracy.atIndex
    request.leftGrid leftIndex (request.left_later.trans leftLater)
  let rightGrid := GridPrimitiveAccuracy.atIndex
    request.rightGrid rightIndex (request.right_later.trans rightLater)
  let leftError := (first.corners.values lastCorner - first.corners.values firstCorner) -
    (value first finish -
    value first start)
  let rightError := (second.corners.values lastCorner - second.corners.values firstCorner) -
    (value second finish -
    value second start)
  have leftBound : Data.Gaussian.Norm.Basic.normSq leftError ≤ 16 * leftGrid.globalBound := by
    have bound := corners_bound leftGrid first
      firstCorner lastCorner
    rw [firstEq, lastEq] at bound
    exact bound
  have rightBound : Data.Gaussian.Norm.Basic.normSq rightError ≤ 16 * rightGrid.globalBound := by
    have bound := corners_bound rightGrid second
      firstCorner lastCorner
    rw [firstEq, lastEq] at bound
    exact bound
  have ownership : Data.Gaussian.Norm.Basic.normSq (leftError + rightError) ≤ 32 * (leftGrid.globalBound +
    rightGrid.globalBound) :=
    (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct leftBound rightBound) (by decide)).trans_eq (by ring1))
  have small : 32 * (leftGrid.globalBound + rightGrid.globalBound) < target / 4 := by
    have bound := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 32)
      (Fraction.Order.Arithmetic.add_lt_add_direct leftGrid.accurate rightGrid.accurate)
    apply (bound.trans_eq (scale_256 _)).trans_le
    apply (Fraction.Order.Field.divide_le_self request.perPiece_positive.le (by decide)).trans
    rw [request.perPiece_eq]
    exact Aggregate.perTerm_le
      (Fraction.Order.Field.div_pos_direct request.positive (by decide)).le _
  have analytic := values_accurate request first
    second leftLater rightLater
  have identity : (first.corners.values lastCorner - first.corners.values firstCorner) +
      (second.corners.values lastCorner - second.corners.values firstCorner) =
      (leftError + rightError) + ((value first
        finish - value first start) +
        (value second finish -
        value second start)) := by
    dsimp only [leftError, rightError]
    ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
      (Fraction.Order.Arithmetic.add_lt_add_direct (ownership.trans_lt small) analytic)).trans_eq
        (quarters _))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeCancellation

end
