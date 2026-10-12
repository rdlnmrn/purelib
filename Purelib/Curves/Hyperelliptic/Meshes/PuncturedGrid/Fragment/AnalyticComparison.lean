module
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.GluedPrimitives
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
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitSigns
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

/-!
# Original period requests across every analytic cell of a grid fragment

The assigned face domain supplies the complete geometric split. Its finite
cell chain propagates the original request's sign, so each local primitive
comparison is automatic and retains the original polynomial index.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.FaceModels (primitiveOnBase)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.GluedPrimitives (primitive_coefficient_eq)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition line_one line_zero)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {source :
    Differential genus}
  {axes : PrimitiveAxes base.bank.grid}
    {parent : CenteredEdge curve source}
  {partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)}
    {interval : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}
  {fragment : RegularPrimitiveFragment axes
    parent partition interval}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    base.faces.regulars}
  {count : Nat} {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {request :
    LocalRequest parent count target}

/-- Both actual retained fragment endpoints lie in the original period request's continuation neighborhood. -/
theorem neighborhood_endpoints (_assigned : RegularPrimitiveFragment.SheetEntry fragment domains request) :
    request.neighborhood.box.Contains fragment.located.first ∧ request.neighborhood.box.Contains fragment.located.last
      := by
  rw [fragment.located.first_eq, fragment.located.last_eq]
  exact PrimitiveSplits.endpoints_inside partition fragment.located.member request

/-- Every emitted analytic piece keeps the sign of the assigned original query. The intervening cells require no
supplied root or sign certificates. -/
theorem piece_nearest (assigned : RegularPrimitiveFragment.SheetEntry fragment domains request)
    (piece : RectangularSegmentSplitting.SegmentPiece assigned.domain.geometry fragment.located.first
      fragment.located.last)
    (member : piece ∈ assigned.split.pieces) (leftIndex rightIndex : Nat) :
    Data.Gaussian.Norm.Basic.normSq (((assigned.domain.patch.transported.cell piece.column
      piece.row).model.refine (leftIndex + 2)).value.eval piece.firstPoint -
      (request.neighborhood.base.refine rightIndex).value.eval piece.firstPoint) ≤
    Data.Gaussian.Norm.Basic.normSq (((assigned.domain.patch.transported.cell piece.column
      piece.row).model.refine (leftIndex + 2)).value.eval piece.firstPoint +
      (request.neighborhood.base.refine rightIndex).value.eval piece.firstPoint) :=
  SplitSigns.split_nearest assigned.domain.patch source assigned.split request.neighborhood
    (AnalyticComparison.neighborhood_endpoints assigned).1 (AnalyticComparison.neighborhood_endpoints assigned).2
      leftIndex rightIndex
    (fun column row inside => PrimitiveComparison.nearest assigned (assigned.domain.patch.transported.cell column row)
      inside leftIndex (rightIndex + 2))
    piece member

/-- The analytic charge uses cached majorants and the retained request index, not a newly prepared integrator or root
approximation. -/
@[expose] def pieceCharge (assigned : RegularPrimitiveFragment.SheetEntry fragment domains request)
    (bounds : FragmentReadings.FragmentBounds assigned.domain.patch source)
    (piece : RectangularSegmentSplitting.SegmentPiece assigned.domain.geometry fragment.located.first
      fragment.located.last) (index : Nat) : Fraction.Rational :=
  12 * (Geometric.Basic.quarterRadius (assigned.domain.patch.transported.cell piece.column piece.row).model.bound (index
    + 2) +
    Geometric.Basic.quarterRadius request.neighborhood.base.model.bound request.request.index) *
      (bounds.numerator piece.column piece.row * bounds.inverse) * Data.Gaussian.Norm.Basic.normSq
        (piece.lastPoint - piece.firstPoint)

/-- All geometric and sheet conditions come from the actual assigned fragment. Only the shared face primitive cache and
its cached bounds are read.

The retained primitive comparison uses the original face clearance, selected root signs and coefficient equality. Its
unit-interval factor reduces by a scalar rational identity. -/
theorem piece_increment_le (assigned : RegularPrimitiveFragment.SheetEntry fragment domains request)
    (bounds : FragmentReadings.FragmentBounds assigned.domain.patch source)
    (piece : RectangularSegmentSplitting.SegmentPiece assigned.domain.geometry fragment.located.first
      fragment.located.last)
    (member : piece ∈ assigned.split.pieces) {index : Nat}
    (primitives : RectangularPrimitiveModels.Primitives (Transitions.oriented (assigned.domain.patch.sheets.refine
      index).transitions (assigned.domain.patch.sheets.refine index).gauge)
      (PreparedPrimitiveSamples.differentialNumerator source)) :
    Data.Gaussian.Norm.Basic.normSq ((primitives.value piece.column piece.row piece.lastPoint -
      primitives.value piece.column piece.row piece.firstPoint) -
      (request.request.model.primitive.value.eval piece.lastPoint - request.request.model.primitive.value.eval
        piece.firstPoint)) ≤
      AnalyticComparison.pieceCharge assigned bounds piece index := by
  have ends := SplitSigns.piece_neighborhood piece
    (AnalyticComparison.neighborhood_endpoints assigned).1 (AnalyticComparison.neighborhood_endpoints assigned).2
  let cell := assigned.domain.patch.transported.cell piece.column piece.row
  let left := cell.model.refine (index + 2)
  let right := request.neighborhood.base.refine request.request.index
  let edge : InverseModelEdgeTransition.EdgeTransition left right piece.firstPoint piece.lastPoint :=
    ⟨piece.first_inside, piece.last_inside, request.neighborhood.box_refines.contains ends.1,
      request.neighborhood.box_refines.contains ends.2,
      ⟨left.value.eval piece.firstPoint, rfl, right.value.eval piece.firstPoint, rfl,
        ⟨false, right.value.eval piece.firstPoint, rfl, by
          have scalar := AnalyticComparison.piece_nearest assigned piece member index request.request.index
          simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using scalar⟩⟩⟩
  have estimate := EdgeTransition.primitive_increment_le edge (bounds.atCell piece.column piece.row)
    (primitives.dense piece.column piece.row) (FaceModels.primitiveOnBase request.request.model)
    (GluedPrimitives.primitive_coefficient_eq source primitives piece.column piece.row)
      request.request.model.coefficient_eq
    (first := 1) (last := 0) ⟨by decide, le_rfl⟩ ⟨le_rfl, by decide⟩
  have sign : edge.sign = 1 := rfl
  rw [sign, Data.Gaussian.Basic.one_mul, InverseModelEdgeTransition.line_one, InverseModelEdgeTransition.line_zero]
    at estimate
  simp only [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  have scalar := estimate.trans_eq (by
    change 12 * (left.bound + right.bound) * (bounds.numerator piece.column piece.row * bounds.inverse) *
      Data.Gaussian.Norm.Basic.normSq (piece.lastPoint - piece.firstPoint) * (1 - 0) ^ 2 =
        AnalyticComparison.pieceCharge assigned bounds piece index
    have unit : (1 : InverseRootPolynomial.Coordinate) - 0 = 1 := by ring1
    rw [unit, one_pow, Fraction.Field.mul_one_direct]
    dsimp only [left, right, cell, AnalyticComparison.pieceCharge, SeededNeighborhood.refine]
    rw [Model.refine_bound, Model.refine_bound])
  simpa only [Primitives.dense, Primitives.value,
    FaceModels.primitiveOnBase] using scalar

/-- The second split preserves the exact primitive increment of the original request, independently of the number of
crossed analytic cells. -/
theorem original_telescope (assigned : RegularPrimitiveFragment.SheetEntry fragment domains request) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (assigned.split.pieces.map fun piece =>
      request.request.model.primitive.value.eval piece.lastPoint - request.request.model.primitive.value.eval
        piece.firstPoint) =
        request.request.model.primitive.value.eval fragment.located.last -
          request.request.model.primitive.value.eval fragment.located.first :=
  assigned.split.telescope request.request.model.primitive.value.eval

end

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison
