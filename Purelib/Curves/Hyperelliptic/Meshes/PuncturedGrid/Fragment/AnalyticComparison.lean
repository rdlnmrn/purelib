module
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings
import Purelib.Riemann.Comparison.RectangularSharedPrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Readings.UniformPreparedRequests.Face.Pieces
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitSigns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PrimitiveComparison
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveNegation

open Purelib.Data.Gaussian.Norm

/-!
# Original period requests across every analytic cell of a grid fragment

The assigned face domain supplies the complete geometric split. Its finite
cell chain propagates the original request's sign, so each local primitive
comparison is automatic and retains the original polynomial index.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison

open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)

open Purelib
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
open Purelib.Data.Rat
open Purelib.Riemann.Branches.RectangularSheetGauge
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.RectangularPrimitiveModels
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.OwnerSeededInverseRoot
open Purelib.Riemann.Paths
open Purelib.Riemann.Readings

public section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentPiece)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition line_one line_zero)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {source :
    Differential genus}
  {axes : PrimitiveAxes base.bank.grid}
    {parent : CenteredEdge curve source}
  {cuts : List Data.Rat.Fraction.Rational} {partition : Partition 0 1 cuts}
    {interval : Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}
  {fragment : RegularPrimitiveFragment axes
    parent partition interval}
  {domains : DomainBanks.FaceDomainBank frames
    base.faces.regulars}
  {count : Nat} {target : InverseRootPolynomial.Coordinate} {request :
    LocalRequest parent count target}

/-- Both actual retained fragment endpoints lie in the original period request's continuation neighborhood. -/
theorem neighborhood_endpoints (_assigned : SheetEntry fragment domains request) :
    request.neighborhood.box.Contains fragment.located.first ∧ request.neighborhood.box.Contains fragment.located.last
      := by
  rw [fragment.located.first_eq, fragment.located.last_eq]
  exact PrimitiveSplits.endpoints_inside partition fragment.located.member request

/-- Every emitted analytic piece keeps the sign of the assigned original query. The intervening cells require no
supplied root or sign certificates. -/
theorem piece_nearest (assigned : SheetEntry fragment domains request)
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first
      fragment.located.last)
    (member : piece ∈ assigned.split.pieces) (leftIndex rightIndex : Nat) :
    Basic.normSq (((assigned.domain.patch.transported.cell piece.column
      piece.row).model.refine (leftIndex + 2)).value.eval piece.firstPoint -
      (request.neighborhood.base.refine rightIndex).value.eval piece.firstPoint) ≤
    Basic.normSq (((assigned.domain.patch.transported.cell piece.column
      piece.row).model.refine (leftIndex + 2)).value.eval piece.firstPoint +
      (request.neighborhood.base.refine rightIndex).value.eval piece.firstPoint) :=
  request.facePiece_nearest assigned.sample assigned.entry assigned.domain assigned.split interval.lower
    assigned.fractionInside fragment.located.first_eq.symm (AnalyticComparison.neighborhood_endpoints assigned).1
    (AnalyticComparison.neighborhood_endpoints assigned).2 piece member leftIndex rightIndex

/-- The analytic charge uses cached majorants and the retained request index, not a newly prepared integrator or root
approximation. -/
@[expose] def pieceCharge (assigned : SheetEntry fragment domains request)
    (bounds : FragmentBounds assigned.domain.patch source)
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first
      fragment.located.last) (index : Nat) : Fraction.Rational :=
  12 * (Geometric.Basic.quarterRadius (assigned.domain.patch.transported.cell piece.column piece.row).model.bound (index
    + 2) +
    Geometric.Basic.quarterRadius request.neighborhood.base.model.bound request.request.index) *
      (bounds.numerator piece.column piece.row * bounds.inverse) * Basic.normSq
        (piece.lastPoint - piece.firstPoint)

/-- The SAME two original inverse models on one actual retained analytic piece. -/
@[expose] def PieceTransition (assigned : SheetEntry fragment domains request)
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last)
    (index : Nat) : Type :=
  EdgeTransition ((assigned.domain.patch.transported.cell piece.column piece.row).model.refine (index + 2))
    (request.neighborhood.base.refine request.request.index) piece.firstPoint piece.lastPoint

/-- Assemble a signed piece comparison from the actual given model caches and their whole refinement factories. -/
private def packPieceTransition (assigned : SheetEntry fragment domains request)
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last)
    (member : piece ∈ assigned.split.pieces) (leftIndex rightIndex : Nat)
    (ends : request.neighborhood.box.Contains piece.firstPoint ∧ request.neighborhood.box.Contains piece.lastPoint)
    (left : Model curve.polynomial (assigned.domain.geometry.box piece.column piece.row))
    (leftFactory : left = (assigned.domain.patch.transported.cell piece.column piece.row).model.refine (leftIndex + 2))
    (right : Model curve.polynomial request.neighborhood.base.box)
    (rightFactory : right = request.neighborhood.base.refine rightIndex) :
    EdgeTransition left right piece.firstPoint piece.lastPoint := by
  have leftValue := congrArg
    (fun model : Model curve.polynomial (assigned.domain.geometry.box piece.column piece.row) =>
      model.value.eval piece.firstPoint) leftFactory
  have rightValue := congrArg
    (fun model : Model curve.polynomial request.neighborhood.base.box =>
      model.value.eval piece.firstPoint) rightFactory
  have near : Basic.normSq (left.value.eval piece.firstPoint - right.value.eval piece.firstPoint) ≤
      Basic.normSq (left.value.eval piece.firstPoint + right.value.eval piece.firstPoint) :=
    Eq.mpr (congrArg₂ (fun left right : Gaussian =>
      Basic.normSq (left - right) ≤ Basic.normSq (left + right)) leftValue rightValue)
      (piece_nearest assigned piece member leftIndex rightIndex)
  exact ⟨piece.first_inside, piece.last_inside, request.neighborhood.box_refines.contains ends.1,
    request.neighborhood.box_refines.contains ends.2,
    ⟨left.value.eval piece.firstPoint, rfl, right.value.eval piece.firstPoint, rfl,
      ⟨false, right.value.eval piece.firstPoint, rfl, by
        simpa only [Basic.normSq_eq_canonical] using near⟩⟩⟩

/-- Compare the SAME actual supplied inverse models at their independent retained stages.

The whole model factory equations retain their owners. The original
sample/Entry split derives the signed relation; no coordinate or sheet
label supplies it, and neither given inverse model is refined again.
-/
def pieceTransitionOn (assigned : SheetEntry fragment domains request)
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last)
    (member : piece ∈ assigned.split.pieces) (leftIndex rightIndex : Nat)
    (left : Model curve.polynomial (assigned.domain.geometry.box piece.column piece.row))
    (leftFactory : left = (assigned.domain.patch.transported.cell piece.column piece.row).model.refine (leftIndex + 2))
    (right : Model curve.polynomial request.neighborhood.base.box)
    (rightFactory : right = request.neighborhood.base.refine rightIndex) :
    EdgeTransition left right piece.firstPoint piece.lastPoint :=
  packPieceTransition assigned piece member leftIndex rightIndex
    (SplitSigns.piece_neighborhood piece
      (AnalyticComparison.neighborhood_endpoints assigned).1 (AnalyticComparison.neighborhood_endpoints assigned).2)
    left leftFactory right rightFactory

/-- The actual given-model comparison retains the original sample-derived positive sign. -/
theorem pieceTransitionOn_sign (assigned : SheetEntry fragment domains request)
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last)
    (member : piece ∈ assigned.split.pieces) (leftIndex rightIndex : Nat)
    (left : Model curve.polynomial (assigned.domain.geometry.box piece.column piece.row))
    (leftFactory : left = (assigned.domain.patch.transported.cell piece.column piece.row).model.refine (leftIndex + 2))
    (right : Model curve.polynomial request.neighborhood.base.box)
    (rightFactory : right = request.neighborhood.base.refine rightIndex) :
    (pieceTransitionOn assigned piece member leftIndex rightIndex left leftFactory right rightFactory).sign = 1 := by
  unfold pieceTransitionOn packPieceTransition
  rfl

/-- Derive the original positive-sign transition from the retained fragment sample and actual ordered split.

This is the same endpoint-containment and nearest-sign construction used
by the whole-piece comparison. Both model owners, their original indices
and the full sample are retained; no root or sign relation is supplied.
-/
def pieceTransition (assigned : SheetEntry fragment domains request)
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last)
    (member : piece ∈ assigned.split.pieces) (index : Nat) : PieceTransition assigned piece index := by
  have ends := SplitSigns.piece_neighborhood piece
    (AnalyticComparison.neighborhood_endpoints assigned).1 (AnalyticComparison.neighborhood_endpoints assigned).2
  let cell := assigned.domain.patch.transported.cell piece.column piece.row
  let left := cell.model.refine (index + 2)
  let right := request.neighborhood.base.refine request.request.index
  exact packPieceTransition assigned piece member index request.request.index ends left rfl right rfl

/-- The original producer retains its complete former constructor, model order, scalar values and selected sign. -/
theorem pieceTransition_factory (assigned : SheetEntry fragment domains request)
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last)
    (member : piece ∈ assigned.split.pieces) (index : Nat) :
    pieceTransition assigned piece member index = (show PieceTransition assigned piece index from by
      have ends := SplitSigns.piece_neighborhood piece
        (AnalyticComparison.neighborhood_endpoints assigned).1 (AnalyticComparison.neighborhood_endpoints assigned).2
      let cell := assigned.domain.patch.transported.cell piece.column piece.row
      let left := cell.model.refine (index + 2)
      let right := request.neighborhood.base.refine request.request.index
      exact ⟨piece.first_inside, piece.last_inside, request.neighborhood.box_refines.contains ends.1,
        request.neighborhood.box_refines.contains ends.2,
        ⟨left.value.eval piece.firstPoint, rfl, right.value.eval piece.firstPoint, rfl,
          ⟨false, right.value.eval piece.firstPoint, rfl, by
            have scalar := AnalyticComparison.piece_nearest assigned piece member index request.request.index
            simpa only [Basic.normSq_eq_canonical] using scalar⟩⟩⟩
      ) := by
  unfold pieceTransition packPieceTransition
  rfl

/-- The original sample-derived transition keeps its certified positive sign throughout the same piece. -/
theorem pieceTransition_sign (assigned : SheetEntry fragment domains request)
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last)
    (member : piece ∈ assigned.split.pieces) (index : Nat) :
    (pieceTransition assigned piece member index).sign = 1 := by
  unfold pieceTransition
  rfl

/-- The original transition retained once with its complete factory identity. -/
@[expose] def TransitionCache (assigned : SheetEntry fragment domains request)
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last)
    (member : piece ∈ assigned.split.pieces) (index : Nat) : Type :=
  {actual : PieceTransition assigned piece index // actual = pieceTransition assigned piece member index}

/-- Construct the SAME original sample-derived transition once and retain the whole result. -/
def buildPieceTransition (assigned : SheetEntry fragment domains request)
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last)
    (member : piece ∈ assigned.split.pieces) (index : Nat) : TransitionCache assigned piece member index :=
  let actual := pieceTransition assigned piece member index
  ⟨actual, rfl⟩

/-- Compare arbitrary oriented partial increments on the SAME retained analytic piece.

The two actual primitive polynomials and their coefficient equations are
unchanged. Both old remainder bounds remain in pieceCharge, multiplied
by the exact squared difference of the displayed partial parameters.
-/
theorem piece_partial_increment_le (assigned : SheetEntry fragment domains request)
    (bounds : FragmentBounds assigned.domain.patch source)
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last)
    (member : piece ∈ assigned.split.pieces) {index : Nat}
    (transition : TransitionCache assigned piece member index)
    (primitives : Primitives (Transitions.oriented (assigned.domain.patch.sheets.refine
      index).transitions (assigned.domain.patch.sheets.refine index).gauge)
      (PreparedPrimitiveSamples.differentialNumerator source))
    {first last : InverseRootPolynomial.Coordinate}
    (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    Basic.normSq ((primitives.value piece.column piece.row
        (Geometry.Rational.Affine.line piece.firstPoint (piece.lastPoint - piece.firstPoint) first) -
      primitives.value piece.column piece.row
        (Geometry.Rational.Affine.line piece.firstPoint (piece.lastPoint - piece.firstPoint) last)) -
      (request.request.model.primitive.value.eval
        (Geometry.Rational.Affine.line piece.firstPoint (piece.lastPoint - piece.firstPoint) first) -
      request.request.model.primitive.value.eval
        (Geometry.Rational.Affine.line piece.firstPoint (piece.lastPoint - piece.firstPoint) last))) ≤
      AnalyticComparison.pieceCharge assigned bounds piece index * (first - last) ^ 2 := by
  have estimate := EdgeTransition.primitive_increment_le (pairs := 0)
    transition.val (bounds.atCell piece.column piece.row)
    (primitives.dense piece.column piece.row) (request.request.model.primitive.onBox request.neighborhood.base.box)
    (assigned.domain.patch.primitive_coefficient_eq (pairs := 0)
      (entered := TracedPath.build
        (Polynomial.Geometry.ClearPath.nil (polynomial := curve.polynomial)
          (ambient := fragment.face.located.face.cell.box) fragment.face.located.face.cell.box.anchor)
        (.nil fragment.face.located.face.cell.box.anchor) _)
      fragment.face.located.face.cell.box.contains_anchor source
      (Branches.BranchIsolation.degreePositive curve)
      (LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank _
        (fragment.face.located.face.cell.anchor_mem fragment.face.located.face.member)).toLoop
      primitives piece.column piece.row)
    request.request.model.coefficient_eq firstInside lastInside
  rewrite [PrimitiveOverlapBounds.weight_zero] at estimate
  have sign : transition.val.sign = 1 :=
    (congrArg EdgeTransition.sign transition.property).trans (pieceTransition_sign assigned piece member index)
  rewrite [sign, Data.Gaussian.Basic.one_mul] at estimate
  simp only [← Basic.normSq_eq_canonical] at estimate
  have scalar := estimate.trans_eq (by
    change 12 *
      (((assigned.domain.patch.transported.cell piece.column piece.row).model.refine (index + 2)).bound +
        (request.neighborhood.base.refine request.request.index).bound) *
      (bounds.numerator piece.column piece.row * bounds.inverse) * Basic.normSq
        (piece.lastPoint - piece.firstPoint) * (first - last) ^ 2 =
      AnalyticComparison.pieceCharge assigned bounds piece index * (first - last) ^ 2
    dsimp only [AnalyticComparison.pieceCharge, SeededNeighborhood.refine]
    rw [Model.refine_bound, Model.refine_bound])
  simpa only [Primitives.dense, Primitives.value,
    Polynomial.Dense.Gaussian.Primitive.Certificate.DensePrimitive.onBox] using scalar

/-- All geometric and sheet conditions come from the actual assigned fragment. Only the shared face primitive cache and
its cached bounds are read.

The retained primitive comparison uses the original face clearance, selected root signs and coefficient equality. Its
unit-interval factor reduces by a scalar rational identity. -/
theorem piece_increment_le (assigned : SheetEntry fragment domains request)
    (bounds : FragmentBounds assigned.domain.patch source)
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first
      fragment.located.last)
    (member : piece ∈ assigned.split.pieces) {index : Nat}
    (primitives : Primitives (Transitions.oriented (assigned.domain.patch.sheets.refine
      index).transitions (assigned.domain.patch.sheets.refine index).gauge)
      (PreparedPrimitiveSamples.differentialNumerator source)) :
    Basic.normSq ((primitives.value piece.column piece.row piece.lastPoint -
      primitives.value piece.column piece.row piece.firstPoint) -
      (request.request.model.primitive.value.eval piece.lastPoint - request.request.model.primitive.value.eval
        piece.firstPoint)) ≤
      AnalyticComparison.pieceCharge assigned bounds piece index := by
  exact request.facePiece_increment_le assigned.sample assigned.entry assigned.domain assigned.split interval.lower
    assigned.fractionInside fragment.located.first_eq.symm (AnalyticComparison.neighborhood_endpoints assigned).1
    (AnalyticComparison.neighborhood_endpoints assigned).2 bounds piece member primitives

/-- The second split preserves the exact primitive increment of the original request, independently of the number of
crossed analytic cells. -/
theorem original_telescope (assigned : SheetEntry fragment domains request) :
    Sum.Basic.gaussianSum (assigned.split.pieces.map fun piece =>
      request.request.model.primitive.value.eval piece.lastPoint - request.request.model.primitive.value.eval
        piece.firstPoint) =
        request.request.model.primitive.value.eval fragment.located.last -
          request.request.model.primitive.value.eval fragment.located.first :=
  assigned.split.telescope request.request.model.primitive.value.eval

end

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison
