module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContinuedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SheetGauge
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitSigns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.ClearBoxRootTransport
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CellNegation
public import Purelib.Riemann.Integration.PreparedQueryNegation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
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
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

section

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Integration.Observation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Geometry.Rectangle.Partition

open Purelib.Polynomial.Geometry.ClearPath

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation

open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial

open Purelib.Riemann.Integration.PreparedQueryNegation

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.ContinuedInverseRoot

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.ClearBoxPathWinding

open Purelib.Riemann.Paths.ClearBoxPaths

open Purelib.Riemann.Paths.PreparedPathTrace

open Purelib.Riemann.Paths.RectangularSegmentSplitting

open Purelib.Riemann.RootContinuation.ClearBoxRootTransport

open Purelib.Riemann.RootContinuation.RootOwnerFrames

public section

/-!
# Original fragment owners remain on their assigned sheet at the endpoint

Finite sign propagation includes the last point of the analytic split.
Opposite face occurrences have incompatible signs, so a proof-only endpoint
entry is on the original sheet. The conclusion concerns the original
parent's actual query owner, including reversed and stationary fragments.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EndpointSheets.FaceModels

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts SegmentPiece SegmentSplit)
open Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts (point)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial (RootAligned)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitSigns (piece_neighborhood)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SheetGauge (cells_nearest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CellNegation (opposite_cells_nearest)
open Purelib.Riemann.Normalization.InverseModelOverlap (SignAlignment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContinuedComparison (trace_aligned)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {sheet : Fin 2} {columns rows : Nat} {geometry : Geometry
    columns rows}
  {first last : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian} {count : Nat}

section
open Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
/-- Every retained cell containing the actual endpoint agrees in nearest sign with the supplied original continuation
neighborhood. -/
private def EndpointNearest (patch : RectangularFaceModels.RectangularPatch models.bounds (models.frame.owners sheet)
  geometry)
    (neighborhood : ContinuedInverseRoot.ContinuedNeighborhood curve.polynomial count) (point :
      InverseRootPolynomial.Gaussian) : Prop :=
  ∀ column row, (geometry.box column row).Contains point →
    Data.Gaussian.Norm.Basic.normSq (((patch.transported.cell column row).model.refine 2).value.eval point -
      (neighborhood.base.refine 2).value.eval point) ≤
    Data.Gaussian.Norm.Basic.normSq (((patch.transported.cell column row).model.refine 2).value.eval point +
      (neighborhood.base.refine 2).value.eval point)

/-- Propagate nearest-sign agreement through every interval of the exact retained increasing segment walk. -/
private theorem endpoint_walk (patch : RectangularFaceModels.RectangularPatch models.bounds (models.frame.owners sheet)
  geometry)
    (differential : Differentials.Basic.Differential genus) (neighborhood : ContinuedInverseRoot.ContinuedNeighborhood
      curve.polynomial count)
    (firstInside : neighborhood.box.Contains first) (lastInside : neighborhood.box.Contains last)
    {available : List PreparedAxisPartitions.Interval} :
    ∀ (pieces : List (RectangularSegmentSplitting.SegmentPiece geometry first last)) {lower upper :
      InverseRootPolynomial.Coordinate}
      (walk : AxisWalks.IncreasingWalk available lower upper),
      pieces.map SegmentPiece.interval = walk.edges →
        EndpointNearest patch neighborhood
        (point first last lower) →
      EndpointNearest patch neighborhood
        (point first last upper)
  | [], _, _, .nil _, _, initial => initial
  | [], _, _, .cons _ _ _, ordered, _ => by cases ordered
  | _ :: _, _, _, .nil _, ordered, _ => by cases ordered
  | head :: tail, _, _, .cons interval _ walk, ordered, initial => by
      have equations := List.cons.inj ordered
      have firstEq : head.firstPoint = point first last interval.lower := by rw [head.first_eq, equations.1]
      have lastEq : head.lastPoint = point first last interval.upper := by rw [head.last_eq, equations.1]
      have atFirst := initial head.column head.row (firstEq ▸ head.first_inside)
      dsimp only [id_eq] at atFirst
      rw [← firstEq] at atFirst
      have contained := SplitSigns.piece_neighborhood head firstInside lastInside
      have atLast := Model.nearest_finish ((patch.transported.cell head.column head.row).model.refine 2)
        (neighborhood.base.refine 2) head.first_inside head.last_inside
        (neighborhood.box_refines.contains contained.1) (neighborhood.box_refines.contains contained.2) atFirst
      have next : EndpointNearest patch
        neighborhood (point first last interval.upper) := by
        rw [← lastEq]
        intro column row inside
        exact ((Model.overlapRefine (patch.transported.cell column row).model) 0).nearest_trans
          ((Model.overlapRefine (patch.transported.cell head.column head.row).model) 0)
          ((Model.overlapRefine neighborhood.base.model) 0) inside head.last_inside
          (neighborhood.box_refines.contains contained.2)
          (SheetGauge.cells_nearest _ _ differential inside head.last_inside 0 0) atLast
      exact endpoint_walk patch
        differential neighborhood firstInside lastInside tail walk equations.2 next

/-- Nearest-sign agreement at the actual split start extends to every retained cell containing its actual final
endpoint. -/
theorem split_finish_nearest (patch : RectangularFaceModels.RectangularPatch models.bounds (models.frame.owners sheet)
  geometry)
    (differential : Differentials.Basic.Differential genus) {cuts : RectangularSegmentSplitting.GridCuts geometry}
      (split : RectangularSegmentSplitting.SegmentSplit cuts first last)
    (neighborhood : ContinuedInverseRoot.ContinuedNeighborhood curve.polynomial count)
    (firstInside : neighborhood.box.Contains first) (lastInside : neighborhood.box.Contains last)
    (initial : ∀ column row, (geometry.box column row).Contains first →
      Data.Gaussian.Norm.Basic.normSq (((patch.transported.cell column row).model.refine 2).value.eval first -
        (neighborhood.base.refine 2).value.eval first) ≤
      Data.Gaussian.Norm.Basic.normSq (((patch.transported.cell column row).model.refine 2).value.eval first +
        (neighborhood.base.refine 2).value.eval first))
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (inside : (geometry.box column row).Contains last) :
    Data.Gaussian.Norm.Basic.normSq (((patch.transported.cell column row).model.refine 2).value.eval last -
      (neighborhood.base.refine 2).value.eval last) ≤
    Data.Gaussian.Norm.Basic.normSq (((patch.transported.cell column row).model.refine 2).value.eval last +
      (neighborhood.base.refine 2).value.eval last) := by
  have started : EndpointNearest patch
    neighborhood (point first last 0) := by
    rw [PreparedSegmentCuts.point_zero]
    exact initial
  have finished := endpoint_walk patch
    differential neighborhood firstInside lastInside split.pieces split.partition.walk
    (split.intervals_eq.trans split.partition.walk_edges.symm) started
  rw [PreparedSegmentCuts.point_one] at finished
  exact finished column row inside

end

open Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
/-- A reached actual owner fixes the sign of any retained containing cell. -/
theorem Entry.point_nearest {point : InverseRootPolynomial.Gaussian} {neighborhood :
  ContinuedInverseRoot.ContinuedNeighborhood curve.polynomial count}
    (sample : ContinuedNeighborhood.Point neighborhood point) (entry : FaceModels.Entry models point sample.owner)
    {inner : InverseRootPolynomial.Box} (cell : TransportedFaceInverseModels.TransportedCell models.bounds
      (models.frame.owners entry.sheet) inner)
    (differential : Differentials.Basic.Differential genus) (inside : inner.Contains point) (pointInside :
      neighborhood.box.Contains point) :
    Data.Gaussian.Norm.Basic.normSq ((cell.model.refine 2).value.eval point - (neighborhood.base.refine
      2).value.eval point) ≤
      Data.Gaussian.Norm.Basic.normSq ((cell.model.refine 2).value.eval point + (neighborhood.base.refine
        2).value.eval point) := by
  obtain ⟨ownerTrace, winding⟩ := entry.reached
  let route := Route.build face.clearance face.cell.box.anchor point face.cell.box.contains_anchor
    (cell.geometry.refines.contains inside)
  let traced := TracedPath.build route.path route.within (models.frame.owners entry.sheet)
  let frame := OwnerFrame.build sample.owner.parameterNonzero
  have equivalent := TracedPath.equivalentOfOwnerPathSelections
    (BranchCellBank.referenceAt bank _ (face.cell.anchor_mem face.member)).toLoop route.within traced ownerTrace frame
    (frame.select traced.finishOwner) (frame.select sample.owner)
    ((Route.winding face.clearance (BranchIsolation.degreePositive curve) route face.cell.box.contains_anchor).trans
      winding.symm)
  have aligned : InverseRootPolynomial.RootAligned ((Model.overlapRefine cell.model) 0) point
    (OwnerTraceReadings.ownerName traced.finishOwner) :=
    ContinuedComparison.trace_aligned cell differential traced (Polynomial.Geometry.ClearPath.InBox.ofWithin route.path
      route.within
      face.cell.box.contains_anchor)
      frame inside 0
  exact aligned neighborhood pointInside sample equivalent 0

/-- The two possible face sheets are distinguished by finite residual and nearest-sign certificates at one common point.
-/
theorem sheet_eq_of_nearest {leftSheet rightSheet : Fin 2} {leftBox rightBox : InverseRootPolynomial.Box}
    (left : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners leftSheet) leftBox)
    (right : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners rightSheet) rightBox)
    (differential : Differentials.Basic.Differential genus) {point : InverseRootPolynomial.Gaussian}
    (leftInside : leftBox.Contains point) (rightInside : rightBox.Contains point)
    (nearest : Data.Gaussian.Norm.Basic.normSq ((left.model.refine 2).value.eval point - (right.model.refine
      2).value.eval point) ≤
      Data.Gaussian.Norm.Basic.normSq ((left.model.refine 2).value.eval point + (right.model.refine
        2).value.eval point)) : leftSheet = rightSheet := by
  have cases : rightSheet = leftSheet ∨ rightSheet = BranchCutLifts.otherSheet leftSheet := by
    have firstBound := leftSheet.isLt
    have lastBound := rightSheet.isLt
    have alternatives : rightSheet.val = leftSheet.val ∨ rightSheet.val = 1 - leftSheet.val := by omega
    exact alternatives.elim (fun equal => Or.inl (Fin.ext equal)) (fun equal => Or.inr (Fin.ext equal))
  rcases cases with equal | equal
  · exact equal.symm
  · subst rightSheet
    have opposite := CellNegation.opposite_cells_nearest left right differential leftInside rightInside 0 0
    let positive : InverseModelOverlap.SignAlignment ((left.model.refine 2).value.eval point) ((right.model.refine
      2).value.eval point) :=
      ⟨false, _, rfl, by
        simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at nearest
        exact nearest⟩
    let negative : InverseModelOverlap.SignAlignment ((left.model.refine 2).value.eval point) ((right.model.refine
      2).value.eval point) :=
      ⟨true, -((right.model.refine 2).value.eval point), rfl, by
        rw [show (left.model.refine 2).value.eval point - -((right.model.refine 2).value.eval point) =
          (left.model.refine 2).value.eval point + (right.model.refine 2).value.eval point by ring1]
        simpa only [← Data.Gaussian.Basic.sub_eq_add_neg, Data.Gaussian.Norm.Basic.normSq_eq_canonical] using opposite⟩
    have leftResidual : Data.Gaussian.Basic.Canonical.normSq (1 - curve.polynomial.eval point * ((left.model.refine
      2).value.eval point) ^ 2) ≤
        (left.model.refine 2).bound := by
      rw [← (left.model.refine 2).residual_eq]
      exact (left.model.refine 2).residualBound _ leftInside
    have rightResidual : Data.Gaussian.Basic.Canonical.normSq (1 - curve.polynomial.eval point * ((right.model.refine
      2).value.eval point) ^ 2) ≤
        (right.model.refine 2).bound := by
      rw [← (right.model.refine 2).residual_eq]
      exact (right.model.refine 2).residualBound _ rightInside
    have impossible : false = true := positive.flip_unique negative leftResidual rightResidual
      (left.model.refine 2).bound_small (right.model.refine 2).bound_small
    cases impossible

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EndpointSheets.FaceModels

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EndpointSheets.SheetEntry

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseModelOverlap (SignAlignment)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

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
  {domains : FaceDomainBank frames
    base.faces.regulars}
  {count : Nat} {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {request :
    LocalRequest parent count target}

/-- The endpoint classification is confined to this proof. Its sheet is forced to agree with the already retained
initial classification. -/
theorem finish_point_reached (assigned : RegularPrimitiveFragment.SheetEntry fragment domains request)
    (sample : ContinuedNeighborhood.Point request.neighborhood fragment.located.last) :
    PreparedFaceTracePrefixes.Reached fragment.face.located.face.cell.box ((RegularPrimitiveFragment.domainCache
      fragment domains).models.frame.owners assigned.entry.sheet) sample.owner := by
  let models := (RegularPrimitiveFragment.domainCache fragment domains).models
  have lastInside : fragment.face.located.face.cell.box.Contains fragment.located.last := by
    rw [fragment.face.located.cell_eq]
    exact fragment.last_inside
  let finalEntry := EdgePoint.entry fragment.source.last models lastInside sample.owner
  let finalDomain := (RegularPrimitiveFragment.domainCache fragment domains).domain finalEntry.sheet
  let firstCell := PeriodDomain.locate assigned.domain fragment.located.last lastInside
  let lastCell := PeriodDomain.locate finalDomain fragment.located.last lastInside
  have firstNearest := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EndpointSheets.FaceModels.split_finish_nearest
    assigned.domain.patch source assigned.split request.neighborhood
    (AnalyticComparison.neighborhood_endpoints assigned).1 (AnalyticComparison.neighborhood_endpoints assigned).2
    (fun column row inside => PrimitiveComparison.nearest assigned (assigned.domain.patch.transported.cell column row)
      inside 0 2)
    firstCell.column firstCell.row firstCell.inside
  have lastNearest := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EndpointSheets.FaceModels.Entry.point_nearest
    sample finalEntry
    (finalDomain.patch.transported.cell lastCell.column lastCell.row) source lastCell.inside
      (AnalyticComparison.neighborhood_endpoints assigned).2
  have reverseNearest : Data.Gaussian.Norm.Basic.normSq ((request.neighborhood.base.refine 2).value.eval
    fragment.located.last -
      ((finalDomain.patch.transported.cell lastCell.column lastCell.row).model.refine 2).value.eval
        fragment.located.last) ≤
      Data.Gaussian.Norm.Basic.normSq ((request.neighborhood.base.refine 2).value.eval fragment.located.last +
        ((finalDomain.patch.transported.cell lastCell.column lastCell.row).model.refine 2).value.eval
          fragment.located.last) := by
    rw [show (request.neighborhood.base.refine 2).value.eval fragment.located.last -
      ((finalDomain.patch.transported.cell lastCell.column lastCell.row).model.refine 2).value.eval
        fragment.located.last =
      -(((finalDomain.patch.transported.cell lastCell.column lastCell.row).model.refine 2).value.eval
        fragment.located.last -
        (request.neighborhood.base.refine 2).value.eval fragment.located.last) by ring1,
      Data.Gaussian.Norm.Basic.normSq_neg,
      show (request.neighborhood.base.refine 2).value.eval fragment.located.last +
        ((finalDomain.patch.transported.cell lastCell.column lastCell.row).model.refine 2).value.eval
          fragment.located.last =
        ((finalDomain.patch.transported.cell lastCell.column lastCell.row).model.refine 2).value.eval
          fragment.located.last +
          (request.neighborhood.base.refine 2).value.eval fragment.located.last by ring1]
    exact lastNearest
  have common := ((Model.overlapRefine (assigned.domain.patch.transported.cell firstCell.column firstCell.row).model)
    0).nearest_trans
    ((Model.overlapRefine request.neighborhood.base.model) 0)
    ((Model.overlapRefine (finalDomain.patch.transported.cell lastCell.column lastCell.row).model) 0)
    firstCell.inside (request.neighborhood.box_refines.contains (AnalyticComparison.neighborhood_endpoints assigned).2)
      lastCell.inside
    firstNearest reverseNearest
  have same := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EndpointSheets.FaceModels.sheet_eq_of_nearest
    (assigned.domain.patch.transported.cell firstCell.column firstCell.row)
    (finalDomain.patch.transported.cell lastCell.column lastCell.row) source firstCell.inside lastCell.inside common
  exact same.symm ▸ finalEntry.reached

/-- The original program's final query has the retained face sheet. The auxiliary endpoint sample and its classification
are erased proof data. -/
theorem finish_query_reached (assigned : RegularPrimitiveFragment.SheetEntry fragment domains request)
    (inside : 0 ≤ interval.upper ∧ interval.upper ≤ 1) :
    PreparedFaceTracePrefixes.Reached fragment.face.located.face.cell.box
      ((RegularPrimitiveFragment.domainCache fragment domains).models.frame.owners assigned.entry.sheet)
      (PreparedEdge.ownerAtPoint parent.edge interval.upper inside fragment.located.last fragment.located.last_eq.symm)
        := by
  let sample := ContinuedNeighborhood.Point.acquire request.neighborhood fragment.located.last
    (AnalyticComparison.neighborhood_endpoints assigned).2
  have joined : Nonempty (Gaussian.Equivalence.NamedEquivalent
      (OwnerTraceReadings.ownerName
        (PreparedEdge.ownerAtPoint parent.edge interval.upper inside fragment.located.last
          fragment.located.last_eq.symm))
      (OwnerTraceReadings.ownerName sample.owner)) := by
    rw [PreparedEdge.ownerAtPoint_name]
    rcases request with ⟨patch, neighborhood, neighborhoodEq, requested, finishInside⟩
    subst neighborhood
    exact ⟨patch.point_equivalent_at count interval.upper inside fragment.located.last_eq.symm
      (AnalyticComparison.neighborhood_endpoints assigned).2 sample⟩
  obtain ⟨equivalent⟩ := joined
  exact (finish_point_reached assigned
    sample).append (Reached.ofEquivalent equivalent.symm)

/-- The corresponding incoming query uses the same retained face sheet. -/
theorem first_query_reached (assigned : RegularPrimitiveFragment.SheetEntry fragment domains request) :
    PreparedFaceTracePrefixes.Reached fragment.face.located.face.cell.box
      ((RegularPrimitiveFragment.domainCache fragment domains).models.frame.owners assigned.entry.sheet)
      (PreparedEdge.ownerAtPoint parent.edge interval.lower assigned.fractionInside fragment.located.first
        fragment.located.first_eq.symm) := by
  obtain ⟨equivalent⟩ := assigned.original
  have joined : Gaussian.Equivalence.NamedEquivalent
      (OwnerTraceReadings.ownerName
        (PreparedEdge.ownerAtPoint parent.edge interval.lower assigned.fractionInside fragment.located.first
          fragment.located.first_eq.symm))
      (OwnerTraceReadings.ownerName assigned.sample.owner) := by
    rw [PreparedEdge.ownerAtPoint_name]
    exact equivalent
  exact assigned.entry.reached.append (Reached.ofEquivalent joined.symm)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EndpointSheets.SheetEntry

end
