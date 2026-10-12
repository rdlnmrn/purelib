module
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement
public import Purelib.Riemann.RootContinuation.NewtonOmittedHoleBank
import Purelib.Riemann.RootContinuation.NewtonRequestedExteriorSides
public import Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceBank
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedSideBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterCornerReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.PairedIncrementComparison
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Word.Pairing
public import Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CorrectionReindex
import Purelib.Riemann.RootContinuation.NewtonRetainedExteriorBound
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Vector.Dependent
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Integration.Path.JoinedTrace
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.NewtonRequestedCutComparison
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCutBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineTransport
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Mathlib.Order.MinMax
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-! The requested retained component bound pays the original fine-side
remainder after its actual joining polygon is restored. Endpoint errors
are paid on the same numerical bank; no joining term is discarded. -/
universe u v
namespace Purelib.Riemann.RootContinuation.NewtonRequestedExteriorRemainder

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation (occurrenceAt)
open Purelib.Riemann.RootContinuation.NewtonRequestedExteriorSides (ComponentTotalError ComponentPhysicalTotal
  ComponentPhysicalArea RetainedExteriorSideEstimate)
open Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth (ExteriorSourceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece (blocks
  blocks_flatten)
open Purelib.Integration.Path.PairedIncrementArea (area total total_bound)
open Purelib.Integration.Path.PairedIncrementComparison (area_difference_bound total_differences)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (PerimeterEndpointRequest)
open Purelib.Riemann.Integration.RectangularCenteredPerimeter (Centered)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (faceValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (maximum maximum_nonnegative
  le_maximum)
open Purelib.Riemann.Periods
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {first second : Fin genus}
  {target radius : Rational} {floor : Nat}

open Purelib.Topology.Polygon in
/-- The final centered primitive pair of the retained bilinear sample. -/
@[expose] def endpointDifference {count : Nat}
    {values : Fin (count + 1) → Stokes.PrimitivePoint}
    (sample : CenteredBilinearPath.Sample values) :
    Stokes.PrimitivePoint :=
  sample.centered (Fin.last count)

open Purelib.Data.Gaussian in
open Purelib.Riemann.Meshes in
open Purelib.Riemann.Paths in
open Purelib.Topology.Polygon in
/-- Select the retained endpoint difference for the specified original perimeter side. -/
@[expose] def sideEndpointDifference
    {columns rows : Nat} {geometry : RectangularInverseModels.Geometry columns rows}
    {cuts : RectangularSegmentSplitting.GridCuts geometry} {box : InverseRootPolynomial.Box}
    {mesh : RectangularObservationMesh.ObservationMesh cuts box}
    {traces : PerimeterTraces mesh}
    {values : Fin (columns + 1) → Fin (rows + 1) → Basic.Canonical → Stokes.PrimitivePoint}
    (samples : Centered traces values) : GridSide → Stokes.PrimitivePoint
  | .bottom => endpointDifference samples.bottom
  | .right => endpointDifference samples.right
  | .top => endpointDifference samples.top
  | .left => endpointDifference samples.left

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Riemann.Meshes in
open Purelib.Riemann.Paths in
open Purelib.Topology.Polygon in
/-- The total of the retained side's ordered increment blocks equals its endpoint difference. -/
private theorem side_total_eq_endpoints
    {columns rows : Nat} {geometry : RectangularInverseModels.Geometry columns rows}
    {cuts : RectangularSegmentSplitting.GridCuts geometry} {box : InverseRootPolynomial.Box}
    {mesh : RectangularObservationMesh.ObservationMesh cuts box}
    {traces : PerimeterTraces mesh}
    {values : Fin (columns + 1) → Fin (rows + 1) → Basic.Canonical → Stokes.PrimitivePoint}
    (samples : Centered traces values) (side : GridSide) :
    PairedIncrementArea.total (Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece.blocks samples
      side).flatten =
      sideEndpointDifference samples side := by
  rw [Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece.blocks_flatten]
  cases side with
  | bottom =>
    exact (CenteredPathIncrements.Sample.increments_total samples.bottom).trans (samples.bottom.centered_eq _).symm
  | right =>
    exact (CenteredPathIncrements.Sample.increments_total samples.right).trans (samples.right.centered_eq _).symm
  | top => exact (CenteredPathIncrements.Sample.increments_total samples.top).trans (samples.top.centered_eq _).symm
  | left => exact (CenteredPathIncrements.Sample.increments_total samples.left).trans (samples.left.centered_eq _).symm

open Purelib.Integration.Path.PairedIncrementArea (area) in
open Purelib.Curves.Hyperelliptic in
open Purelib.Topology.Polygon in
/-- The joining area of one original exterior component's signed endpoint differences.

The ordered occurrence list, source orientation and retained perimeter sample cache determine every paired increment;
the two differential readings remain separate. -/
@[expose] def ComponentJoiningArea (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index) :
      Gaussian :=
  let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
  let occurrence := fun outer : Fin component.prepared.occurrences.length =>
    Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences outer
  let samples := fun outer => ((prepared.traces.samples cache first second).samples.get
    (occurrence outer).sideOccurrence.position).get (occurrence outer).sideOccurrence.sheet
  area (List.ofFn (fun outer =>
    let value := sideEndpointDifference (samples outer)
      (occurrence outer).sideOccurrence.side
    if (occurrence outer).sourceForward then value else Stokes.PrimitivePoint.zero.sub value))

open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.RootIsolation in
open Purelib.Topology.Polygon in
/-- The oriented difference of the original side's normalized corner readings. -/
private def cornerDifference {bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher}
    {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : List (RegularFace bank)}
    {domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces} {index : Nat} (cache :
      Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains index)
    (first second : Fin genus) (position : Fin faces.length) (sheet : Fin 2) (side : GridSide) :
    Stokes.PrimitivePoint :=
  let corners := Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cache.normalize first
    second position sheet
  match side with
  | .bottom => (corners 1).sub (corners 0)
  | .right => (corners 2).sub (corners 1)
  | .top => (corners 2).sub (corners 3)
  | .left => (corners 3).sub (corners 0)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Topology.Polygon in
/-- Endpoint errors bounded by four times the tolerance give a sixteen-times bound on their retained difference. -/
private theorem endpoint_difference_bound {count : Nat}
    {values : Fin (count + 1) → Stokes.PrimitivePoint}
    (sample : CenteredBilinearPath.Sample values)
    {first last : Stokes.PrimitivePoint} {error : Fraction.Rational}
    (initial : Bounded ((values 0).sub first) (4 * error))
    (final : Bounded ((values (Fin.last count)).sub last) (4 * error)) :
    Bounded ((endpointDifference sample).sub (last.sub first)) (16 * error) := by
  have scalar {a b : Basic.Canonical}
      (ha : Basic.Canonical.normSq a ≤ 4 * error)
      (hb : Basic.Canonical.normSq b ≤ 4 * error) :
      Basic.Canonical.normSq (a - b) ≤ 16 * error := by
    have squared : Basic.Canonical.normSq (a - b) ≤
        2 * (Basic.Canonical.normSq a + Basic.Canonical.normSq b) := by
      simpa only [Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using
        (Norm.Bounds.normSq_sub_le_two a b)
    exact squared.trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct ha hb)
        (by decide : (0 : Fraction.Rational) ≤ 2)).trans_eq (by ring1))
  have estimate : Bounded (((values (Fin.last count)).sub last).sub ((values 0).sub first)) (16 * error) :=
    ⟨scalar final.1 initial.1, scalar final.2 initial.2⟩
  have same : ((values (Fin.last count)).sub last).sub ((values 0).sub first) =
      (endpointDifference sample).sub (last.sub first) := by
    unfold endpointDifference
    rw [sample.centered_eq]
    apply congrArg₂ Stokes.PrimitivePoint.mk <;>
      dsimp only [Stokes.PrimitivePoint.sub, -eq_self, -iff_self] <;> ring1
  exact same ▸ estimate

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Rectangle in
/-- A retained side endpoint difference approximates its original normalized corner difference.

The stage must cover the allocated endpoint request. The estimate uses the same face, sheet, side and cached trace at
both endpoints, with squared error at most sixteen times its tolerance. -/
private theorem side_endpoint_difference_bound
    {base : FramedPuncturedGrid curve branches higher} {lifted : LiftedPuncturedGrid base}
    {domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
    {cuts : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {depth : Nat} {fixed : (sheet :
      Fin 2) → Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet}
    {requestTarget endpointTarget : Fraction.Rational}
    {request : Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
      Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet depth) fixed requestTarget}
    (allocated : Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest fixed first second
      endpointTarget)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains index) (later :
      allocated.index ≤ index)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2)
    (traces : PerimeterTraces
      ((request.entries.get sheet).meshes.entries.get position))
    (samples : Centered traces (Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize first second
      position sheet)) (side : GridSide) :
    Bounded ((sideEndpointDifference samples side).sub
      (cornerDifference cache first second position sheet side)) (16 * allocated.tolerance) := by
  let li := Accuracy.FragmentIndex.GridPrimitiveAccuracy.atIndex (allocated.grids.row sheet position first) index
    ((allocated.grids.row_index_le sheet position first).trans (allocated.grids_le.trans later))
  let lj := Accuracy.FragmentIndex.GridPrimitiveAccuracy.atIndex (allocated.grids.row sheet position second) index
    ((allocated.grids.row_index_le sheet position second).trans (allocated.grids_le.trans later))
  cases side with
  | bottom =>
    apply endpoint_difference_bound samples.bottom
    · constructor
      · have estimate := Meshes.PuncturedGrid.PerimeterCornerReadings.perimeter_bottom_first_bound li
          (cache.normalize.atDomain position sheet first) traces
        rw [traces.bottom.leftReadings_value] at estimate
        rw [Norm.Basic.normSq_eq_canonical] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          li.accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
      · have estimate := Meshes.PuncturedGrid.PerimeterCornerReadings.perimeter_bottom_first_bound lj
          (cache.normalize.atDomain position sheet second) traces
        rw [traces.bottom.leftReadings_value] at estimate
        rw [Norm.Basic.normSq_eq_canonical] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          lj.accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
    · constructor
      · have estimate := Meshes.PuncturedGrid.PerimeterCornerReadings.perimeter_bottom_last_bound li
          (cache.normalize.atDomain position sheet first) traces
        rw [traces.bottom.leftReadings_value] at estimate
        rw [Norm.Basic.normSq_eq_canonical] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          li.accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
      · have estimate := Meshes.PuncturedGrid.PerimeterCornerReadings.perimeter_bottom_last_bound lj
          (cache.normalize.atDomain position sheet second) traces
        rw [traces.bottom.leftReadings_value] at estimate
        rw [Norm.Basic.normSq_eq_canonical] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          lj.accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
  | right =>
    apply endpoint_difference_bound samples.right
    · constructor
      · have estimate := Meshes.PuncturedGrid.PerimeterCornerReadings.perimeter_right_first_bound li
          (cache.normalize.atDomain position sheet first) traces
        rw [traces.right.leftReadings_value] at estimate
        rw [Norm.Basic.normSq_eq_canonical] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          li.accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
      · have estimate := Meshes.PuncturedGrid.PerimeterCornerReadings.perimeter_right_first_bound lj
          (cache.normalize.atDomain position sheet second) traces
        rw [traces.right.leftReadings_value] at estimate
        rw [Norm.Basic.normSq_eq_canonical] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          lj.accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
    · constructor
      · have estimate := Meshes.PuncturedGrid.PerimeterCornerReadings.perimeter_right_last_bound li
          (cache.normalize.atDomain position sheet first) traces
        rw [traces.right.leftReadings_value] at estimate
        rw [Norm.Basic.normSq_eq_canonical] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          li.accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
      · have estimate := Meshes.PuncturedGrid.PerimeterCornerReadings.perimeter_right_last_bound lj
          (cache.normalize.atDomain position sheet second) traces
        rw [traces.right.leftReadings_value] at estimate
        rw [Norm.Basic.normSq_eq_canonical] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          lj.accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
  | top =>
    apply endpoint_difference_bound samples.top
    · constructor
      · have estimate := Meshes.PuncturedGrid.PerimeterCornerReadings.perimeter_top_first_bound li
          (cache.normalize.atDomain position sheet first) traces
        rw [traces.top.leftReadings_value] at estimate
        rw [Norm.Basic.normSq_eq_canonical] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          li.accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
      · have estimate := Meshes.PuncturedGrid.PerimeterCornerReadings.perimeter_top_first_bound lj
          (cache.normalize.atDomain position sheet second) traces
        rw [traces.top.leftReadings_value] at estimate
        rw [Norm.Basic.normSq_eq_canonical] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          lj.accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
    · constructor
      · have estimate := Meshes.PuncturedGrid.PerimeterCornerReadings.perimeter_top_last_bound li
          (cache.normalize.atDomain position sheet first) traces
        rw [traces.top.leftReadings_value] at estimate
        rw [Norm.Basic.normSq_eq_canonical] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          li.accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
      · have estimate := Meshes.PuncturedGrid.PerimeterCornerReadings.perimeter_top_last_bound lj
          (cache.normalize.atDomain position sheet second) traces
        rw [traces.top.leftReadings_value] at estimate
        rw [Norm.Basic.normSq_eq_canonical] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          lj.accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
  | left =>
    apply endpoint_difference_bound samples.left
    · constructor
      · have estimate := Meshes.PuncturedGrid.PerimeterCornerReadings.perimeter_left_first_bound li
          (cache.normalize.atDomain position sheet first) traces
        rw [traces.left.leftReadings_value] at estimate
        rw [Norm.Basic.normSq_eq_canonical] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          li.accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
      · have estimate := Meshes.PuncturedGrid.PerimeterCornerReadings.perimeter_left_first_bound lj
          (cache.normalize.atDomain position sheet second) traces
        rw [traces.left.leftReadings_value] at estimate
        rw [Norm.Basic.normSq_eq_canonical] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          lj.accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
    · constructor
      · have estimate := Meshes.PuncturedGrid.PerimeterCornerReadings.perimeter_left_last_bound li
          (cache.normalize.atDomain position sheet first) traces
        rw [traces.left.leftReadings_value] at estimate
        rw [Norm.Basic.normSq_eq_canonical] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          li.accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))
      · have estimate := Meshes.PuncturedGrid.PerimeterCornerReadings.perimeter_left_last_bound lj
          (cache.normalize.atDomain position sheet second) traces
        rw [traces.left.leftReadings_value] at estimate
        rw [Norm.Basic.normSq_eq_canonical] at estimate
        exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          lj.accurate.le (by decide : (0 : Fraction.Rational) ≤ 4))

open Purelib.Topology.Polygon in
/-- Orient a primitive pair by its retained forward flag. -/
private def signedPoint (forward : Bool) (value : Stokes.PrimitivePoint) :=
  if forward then value else Stokes.PrimitivePoint.zero.sub value

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- Reversing both primitive coordinates preserves their common squared-norm bound. -/
private theorem signed_bounded (forward : Bool) {value : Stokes.PrimitivePoint} {bound : Fraction.Rational}
    (bounded : Bounded value bound) : Bounded (signedPoint forward value) bound := by
  cases forward with
  | true => exact bounded
  | false =>
    simpa only [PrimitiveAreaBounds.PrimitivePoint.Bounded, signedPoint, if_neg (by decide : false ≠ true),
      Stokes.PrimitivePoint.zero,
      Stokes.PrimitivePoint.sub, zero_sub, Basic.Canonical.normSq_neg, -eq_self, -iff_self] using bounded

open Purelib.Topology.Polygon in
/-- Taking an oriented difference commutes with the retained sign operation. -/
private theorem signed_difference (forward : Bool) (a b : Stokes.PrimitivePoint) :
    (signedPoint forward a).sub (signedPoint forward b) = signedPoint forward (a.sub b) := by
  cases forward with
  | true => rfl
  | false =>
    change (Stokes.PrimitivePoint.zero.sub a).sub (Stokes.PrimitivePoint.zero.sub b) =
      Stokes.PrimitivePoint.zero.sub (a.sub b)
    apply congrArg₂ Stokes.PrimitivePoint.mk <;>
      dsimp only [Stokes.PrimitivePoint.zero,
        Stokes.PrimitivePoint.sub, -eq_self, -iff_self] <;> ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Topology.Polygon in
/-- The difference of two primitive pairs bounded by one constant is bounded by four times that constant. -/
private theorem point_sub_bound {a b : Stokes.PrimitivePoint} {bound : Fraction.Rational}
    (ha : Bounded a bound) (hb : Bounded b bound) : Bounded (a.sub b) (4 * bound) := by
  have scalar {x y : Basic.Canonical}
      (hx : Basic.Canonical.normSq x ≤ bound)
      (hy : Basic.Canonical.normSq y ≤ bound) :
      Basic.Canonical.normSq (x - y) ≤ 4 * bound := by
    have squared : Basic.Canonical.normSq (x - y) ≤
        2 * (Basic.Canonical.normSq x + Basic.Canonical.normSq y) := by
      simpa only [Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using
        (Norm.Bounds.normSq_sub_le_two x y)
    exact squared.trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct hx hy)
        (by decide : (0 : Fraction.Rational) ≤ 2)).trans_eq (by ring1))
  constructor
  · exact scalar ha.1 hb.1
  · exact scalar ha.2 hb.2

open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.RootIsolation in
open Purelib.Topology.Surface in
/-- An original located side source reads the exact difference of its normalized corner values. -/
private theorem side_source_increment
    {bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher} {frames :
      RootIsolation.SquareRoot.Grid.RootFrames bank.grid}
    {vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges : SquareRoot.Grid.RootEdgeBank
      frames}
    {faces : PuncturedFaces bank} {mesh : LiftedMesh vertices edges faces}
    {domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} {index : Nat} {cache :
      Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains index}
    {basis : Fin genus} (readings : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get basis)
      mesh)
    (position : Fin faces.regulars.length) (sheet : Fin 2) (side : GridSide) :
    (Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource (mesh.locateFace position
      sheet) side).increment readings.values =
      (cache.atDomain position sheet basis).corners.values (Meshes.PuncturedGrid.Face.Corners.FaceCorners.quad.edge
        side.kind).finish -
      (cache.atDomain position sheet basis).corners.values (Meshes.PuncturedGrid.Face.Corners.FaceCorners.quad.edge
        side.kind).start := by
  unfold Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource
    Sewing.SewnPrimitiveContacts.SourceEdge.increment
  rw [readings.values_eq]
  exact Meshes.PuncturedGrid.TrianglePrimitiveReadings.FaceCorners.triangle_increment _ _

open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.RootIsolation in
open Purelib.Topology.Polygon in
open Purelib.Topology.Surface in
/-- The actual oriented side-source increment equals the signed original corner difference. -/
private theorem occurrence_increment
    {bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher} {frames :
      RootIsolation.SquareRoot.Grid.RootFrames bank.grid}
    {vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges : SquareRoot.Grid.RootEdgeBank
      frames}
    {faces : PuncturedFaces bank} {mesh : LiftedMesh vertices edges faces}
    {domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} {index : Nat} {cache :
      Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains index}
    (left : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get first) mesh) (right :
      Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get second) mesh)
    (occurrence : Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SideOccurrence mesh) :
    (⟨occurrence.source.increment left.values, occurrence.source.increment right.values⟩ :
      Stokes.PrimitivePoint) =
      signedPoint (match occurrence.side with
        | .bottom | .right => !occurrence.backward
        | .top | .left => occurrence.backward)
        (cornerDifference cache first second occurrence.position occurrence.sheet occurrence.side) := by
  rcases occurrence with ⟨position, sheet, side, backward⟩
  have li := side_source_increment left position sheet side
  have ri := side_source_increment right position sheet side
  cases backward with
  | false =>
    change (⟨(Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource (mesh.locateFace
      position sheet) side).increment left.values,
      (Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource (mesh.locateFace position
        sheet) side).increment right.values⟩ :
      Stokes.PrimitivePoint) = _
    rw [li, ri]
    cases side <;> apply congrArg₂ Stokes.PrimitivePoint.mk <;>
      simp only [cornerDifference, Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair,
        Stokes.PrimitivePoint.sub, Stokes.PrimitivePoint.zero,
        Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics.normalize_corner_increment, -eq_self, -iff_self]
          <;>
      dsimp [GridSide.kind, Meshes.PuncturedGrid.Face.Corners.FaceCorners.quad,
        Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral.edge] <;> ring1
  | true =>
    have reversed (source : Sewing.SewnPrimitiveContacts.SourceEdge mesh.triangles.length)
        (values : Data.Vector (Sewing.PrimitiveSewing.PrimitiveValues 3) mesh.triangles.length) :
        (⟨source.source, source.last, source.first⟩ : Sewing.SewnPrimitiveContacts.SourceEdge
          mesh.triangles.length).increment values =
          -source.increment values := by
      unfold Sewing.SewnPrimitiveContacts.SourceEdge.increment
      ring1
    refine (congrArg₂ Stokes.PrimitivePoint.mk
      (reversed (Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource (mesh.locateFace
        position sheet) side) left.values)
      (reversed (Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource (mesh.locateFace
        position sheet) side) right.values)).trans ?_
    rw [li, ri]
    cases side <;> apply congrArg₂ Stokes.PrimitivePoint.mk <;>
      simp only [cornerDifference, Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair,
        Stokes.PrimitivePoint.sub, Stokes.PrimitivePoint.zero,
        Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics.normalize_corner_increment, -eq_self, -iff_self]
          <;>
      dsimp [GridSide.kind, Meshes.PuncturedGrid.Face.Corners.FaceCorners.quad,
        Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral.edge] <;> ring1

open Purelib.Integration.Path.PairedIncrementArea (area) in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
open Purelib.Topology.Surface in
/-- Pointwise errors control the difference of two finite paired-increment areas.

For count entries, the squared area error is bounded by sixteen times count to the fourth power times the pointwise
error and twice the sum of the magnitude and error bounds. -/
private theorem polygon_difference_bound {count : Nat}
    (fine coarse : Fin count → Stokes.PrimitivePoint) {error magnitude : Fraction.Rational}
    (errorNonnegative : 0 ≤ error) (magnitudeNonnegative : 0 ≤ magnitude)
    (accurate : ∀ i, Bounded ((fine i).sub (coarse i)) error)
    (bounded : ∀ i, Bounded (coarse i) magnitude) :
    Data.Gaussian.Norm.Basic.normSq (area (List.ofFn fine) -
      area (List.ofFn coarse)) ≤
      16 * (count : Fraction.Rational)^4 * error * (2 * (magnitude + error)) := by
  have boundNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    (by decide : (0 : Fraction.Rational) ≤ 2) (add_nonneg magnitudeNonnegative errorNonnegative)
  have magnitudeLe : magnitude ≤ 2 * (magnitude + error) :=
    (le_add_of_nonneg_right errorNonnegative).trans
      ((le_add_of_nonneg_right (add_nonneg magnitudeNonnegative errorNonnegative)).trans_eq (by ring1))
  have estimate := PairedIncrementComparison.area_difference_bound
    (List.ofFn (fun i => (fine i, coarse i))) errorNonnegative boundNonnegative
    (by
      intro pair member
      obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      exact accurate i)
    (by
      intro pair member
      obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      exact Boundary.HandleAreaBounds.PrimitivePoint.perturbation_bounded (bounded i) (accurate i))
    (by
      intro pair member
      obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      exact ⟨(bounded i).1.trans magnitudeLe, (bounded i).2.trans magnitudeLe⟩)
  simp only [OfFn.Basic.map_ofFn, Data.List.OfFn.Basic.length_ofFn, -eq_self, -iff_self] at estimate
  exact estimate

open Purelib.Integration.Path.PairedIncrementArea (area) in
open Purelib.Curves.Hyperelliptic in
open Purelib.Topology.Polygon in
/-- The joining area of the original component's actual paired boundary-source increments. -/
@[expose] def ComponentBoundaryJoiningArea
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {index : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) : Gaussian
      :=
  let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
  area (List.ofFn (fun outer : Fin component.prepared.occurrences.length =>
    let source := (Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      component.prepared.occurrences outer).sideOccurrence.source
    (⟨source.increment readings.left.values, source.increment readings.right.values⟩ :
      Stokes.PrimitivePoint)))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- The explicit squared-error allowance for one original component's joining area.

Its fourth-power occurrence factor multiplies the allocated endpoint tolerance and the retained bounds for both
differential magnitudes. -/
@[expose] def ComponentJoiningError
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {endpointTarget : Fraction.Rational}
    (allocated : Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest prepared.paid.cut.fixed first
      second endpointTarget) : Fraction.Rational :=
  16 * (((prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences.length :
    Fraction.Rational)^4) * (16 * allocated.tolerance) *
    (2 * (4 * (allocated.firstMagnitude.bound + allocated.secondMagnitude.bound) + 16 * allocated.tolerance))

open Purelib.Integration.Path.PairedIncrementArea (area) in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
/-- The retained component joining area approximates its actual boundary-source joining area.

At a stage covering the same allocated endpoint request, the squared difference is bounded by the component's explicit
joining error, preserving all original occurrences and source signs. -/
theorem component_joining_boundary_bound
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {endpointTarget : Fraction.Rational}
    (allocated : Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest prepared.paid.cut.fixed first
      second endpointTarget)
    {index : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache)
    (later : allocated.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (ComponentJoiningArea prepared componentIndex cache -
      ComponentBoundaryJoiningArea prepared componentIndex readings) ≤
      ComponentJoiningError prepared componentIndex allocated := by
  let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
  let occurrence := fun outer : Fin component.prepared.occurrences.length =>
    Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences outer
  let fine := fun outer => signedPoint (occurrence outer).sourceForward
    (sideEndpointDifference (((prepared.traces.samples cache
      first second).samples.get
      (occurrence outer).sideOccurrence.position).get (occurrence outer).sideOccurrence.sheet)
      (occurrence outer).sideOccurrence.side)
  let coarse := fun outer => signedPoint (occurrence outer).sourceForward
    (cornerDifference cache first second (occurrence outer).sideOccurrence.position
      (occurrence outer).sideOccurrence.sheet (occurrence outer).sideOccurrence.side)
  have accurate (outer) : Bounded ((fine outer).sub (coarse outer)) (16 * allocated.tolerance) := by
    exact (signed_difference _ _ _).symm ▸ signed_bounded _ (side_endpoint_difference_bound allocated cache later
      (occurrence outer).sideOccurrence.position (occurrence outer).sideOccurrence.sheet _ _ (occurrence
        outer).sideOccurrence.side)
  have bounded (outer) : Bounded (coarse outer)
      (4 * (allocated.firstMagnitude.bound + allocated.secondMagnitude.bound)) := by
    apply signed_bounded
    have corners := Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.normalized_corner_pair_bound
      allocated.firstMagnitude allocated.secondMagnitude
      (allocated.first_le.trans later) (allocated.second_le.trans later) cache
      (occurrence outer).sideOccurrence.position (occurrence outer).sideOccurrence.sheet
    cases (occurrence outer).sideOccurrence.side <;> exact point_sub_bound (corners _) (corners _)
  have estimate := polygon_difference_bound fine coarse
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) allocated.positive.le)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg allocated.firstMagnitude.nonnegative allocated.secondMagnitude.nonnegative)) accurate bounded
  have sourceEq : ComponentBoundaryJoiningArea prepared componentIndex readings =
      area (List.ofFn coarse) := by
    apply congrArg area
    apply OfFn.Basic.ofFn_congr
    intro outer
    exact occurrence_increment readings.left readings.right (occurrence outer).sideOccurrence
  exact (congrArg (fun area => Data.Gaussian.Norm.Basic.normSq (ComponentJoiningArea prepared componentIndex cache -
    area))
    sourceEq).trans_le estimate

open Purelib.Data.Gaussian in
open Purelib.Data.List in

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- The squared component-count factor times the largest retained component joining error. -/
@[expose] def JoiningBoundaryError
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {endpointTarget : Fraction.Rational}
    (allocated : Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest prepared.paid.cut.fixed first
      second endpointTarget) : Fraction.Rational :=
  let count : Rational := prepared.exterior.prepared.components.length
  count * (count * maximum id
    (List.ofFn (fun i => ComponentJoiningError prepared i allocated)))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The sum of retained joining areas approximates the sum of actual boundary joining areas.

The common cache stage covers the allocated endpoint request; the finite sum estimate uses the exact component count and
maximum component error. -/
theorem joining_boundary_bound
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {endpointTarget : Fraction.Rational}
    (allocated : Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest prepared.paid.cut.fixed first
      second endpointTarget)
    {index : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) (later :
      allocated.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun i => ComponentJoiningArea
      prepared i
      cache)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun i => ComponentBoundaryJoiningArea prepared i readings)))
        ≤
      JoiningBoundaryError prepared allocated := by
  have estimate := Norm.Sum.Bounds.normSq_sum_le
    (List.ofFn (fun i => ComponentJoiningArea prepared i cache - ComponentBoundaryJoiningArea prepared i readings))
    (maximum id
      (List.ofFn (fun i => ComponentJoiningError prepared i allocated))) (by
        intro value member
        obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
        exact (component_joining_boundary_bound prepared i allocated readings later).trans
          (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum id (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨i,
            rfl⟩)))
  have differences := Data.Gaussian.Norm.Sum.Basic.gaussianSum_map_sub
    (List.ofFn (fun i : Fin prepared.exterior.prepared.components.length => i))
    (fun i => ComponentJoiningArea prepared i cache)
    (fun i => ComponentBoundaryJoiningArea prepared i readings)
  rw [Data.List.OfFn.Basic.map_ofFn, Data.List.OfFn.Basic.map_ofFn, Data.List.OfFn.Basic.map_ofFn] at differences
  dsimp only [Function.comp_def] at differences
  rw [Data.List.OfFn.Basic.length_ofFn, differences] at estimate
  exact estimate

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks in
open Purelib.Data.Rat in
/-- The component-count square times the maximum sixteen-times fourth-power occurrence count. -/
@[expose] def joiningWeight (prepared : BoundaryPreparation preparation first second target radius floor) :
  Fraction.Rational :=
  let count : Rational := prepared.exterior.prepared.components.length
  count * (count * maximum id
    (List.ofFn (fun i : Fin prepared.exterior.prepared.components.length =>
      16 * (((prepared.exterior.prepared.components[i.val]'i.isLt).prepared.occurrences.length :
        Fraction.Rational)^4))))

open Purelib.Data.Rat in
/-- The allocated small endpoint tolerance pays the fourth-power joining coefficient.

The assumptions bound four times the tolerance by one and pay the magnitude-weighted allowance; the conclusion retains
the original count-dependent factor. -/
private theorem joining_scale (count : Nat) {magnitude tolerance allowance : Fraction.Rational}
    (nonnegative : 0 ≤ tolerance) (small : 4 * tolerance ≤ 1)
    (paid : 128 * (magnitude + 1) * tolerance ≤ allowance) :
    16 * (count : Fraction.Rational)^4 * (16 * tolerance) * (2 * (4 * magnitude + 16 * tolerance)) ≤
      (16 * (count : Fraction.Rational)^4) * allowance := by
  have coefficientNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 16)
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4)
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small (by
      decide : (0 : Fraction.Rational) ≤ 4)
  have factor : 2 * (4 * magnitude + 16 * tolerance) ≤ 8 * (magnitude + 1) := by
    have estimate := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (le_refl (4 * magnitude)) scaled) (by
          decide : (0 : Fraction.Rational) ≤ 2)
    exact (le_of_eq (by ring1)).trans (estimate.trans_eq (by ring1))
  have estimate := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct factor
    (Fraction.Order.Arithmetic.mul_nonneg_direct coefficientNonnegative
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 16) nonnegative))
  exact estimate.trans ((le_of_eq (by ring1)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid coefficientNonnegative))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks in
open Purelib.Data.Rat in
/-- A nonnegative bound on every listed rational also bounds their zero-based maximum. -/
private theorem maximum_bounded (values : List Fraction.Rational) {bound : Fraction.Rational}
    (nonnegative : 0 ≤ bound) (bounded : ∀ value ∈ values, value ≤ bound) :
    maximum id values ≤ bound := by
  induction values with
  | nil => exact nonnegative
  | cons head tail ih =>
    exact Fraction.Order.Basic.max_le (bounded head List.mem_cons_self)
      (ih (fun value member => bounded value (List.mem_cons_of_mem head member)))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- The retained component-count joining weight is nonnegative. -/
theorem joining_weight_nonnegative
    (prepared : BoundaryPreparation preparation first second target radius floor) : 0 ≤ joiningWeight prepared :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
      (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- The aggregate joining error is bounded by its exact weight times the positive endpoint target. -/
theorem joining_error_le_weight
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {endpointTarget : Fraction.Rational}
    (allocated : Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest prepared.paid.cut.fixed first
      second endpointTarget)
    (positive : 0 < endpointTarget) :
    JoiningBoundaryError prepared allocated ≤ joiningWeight prepared * endpointTarget := by
  let coefficients := List.ofFn (fun i : Fin prepared.exterior.prepared.components.length =>
    16 * (((prepared.exterior.prepared.components[i.val]'i.isLt).prepared.occurrences.length : Fraction.Rational)^4))
  let weight := maximum id coefficients
  have nonnegative : 0 ≤ weight := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _
  have each (i : Fin prepared.exterior.prepared.components.length) :
      ComponentJoiningError prepared i allocated ≤ weight * endpointTarget :=
    (joining_scale _ allocated.positive.le allocated.small allocated.paid).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum id (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨i, rfl⟩))
          positive.le)
  have maximum := maximum_bounded (List.ofFn (fun i => ComponentJoiningError prepared i allocated))
    (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative positive.le) (by
      intro value member
      obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      exact each i)
  have countNonnegative : (0 : Fraction.Rational) ≤ prepared.exterior.prepared.components.length :=
    Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have estimate := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct maximum countNonnegative) countNonnegative
  exact estimate.trans_eq (by dsimp only [joiningWeight, weight, coefficients, -eq_self, -iff_self]; ring1)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- An original side-remainder request whose aggregate joining error is also paid.

The subtype retains the same prepared exterior, endpoint owner and requested allowance together with the additional
bound on its joining error. -/
@[expose] def JoiningEndpointRequest
    (prepared : BoundaryPreparation preparation first second target radius floor) (requested : Fraction.Rational) :=
  { endpoints :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.SideRemainderRequest
      prepared.exterior.prepared prepared.paid.cut.fixed first second requested //
    JoiningBoundaryError prepared endpoints.endpoints ≤ requested }

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Allocate one endpoint request that pays both side remainders and the aggregate joining error.

The positive local target is the minimum of the original per-occurrence allowance and the joining-weight allowance. The
returned certificate reuses that allocation and its retained magnitude data. -/
@[expose] def prepareJoiningEndpoints
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (requested : Fraction.Rational) (positive : 0 < requested) : JoiningEndpointRequest prepared requested := by
  let count := prepared.exterior.prepared.occurrences.length
  let allowance := Budget.Aggregate.perTerm requested count
  let weight := joiningWeight prepared
  have weightNonnegative := joining_weight_nonnegative
    prepared
  let localTarget := min allowance (Budget.Weighted.allowance requested weight)
  have localPositive : 0 < localTarget := Fraction.Order.Basic.lt_min (Budget.Aggregate.perTerm_positive positive count)
    (Budget.Weighted.allowance_positive positive weightNonnegative)
  let allocated := Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest.build prepared.paid.cut.fixed
    first second localTarget localPositive
  let endpoints : Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest prepared.paid.cut.fixed first
    second allowance :=
    { allocated with paid := allocated.paid.trans (Fraction.Order.Basic.min_le_left _ _) }
  let sides :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.SideRemainderRequest
      prepared.exterior.prepared prepared.paid.cut.fixed first second requested :=
    ⟨positive, count, rfl, allowance, rfl, endpoints⟩
  refine ⟨sides, ?_⟩
  have bound := joining_error_le_weight prepared allocated
    localPositive
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Basic.min_le_right allowance (Budget.Weighted.allowance requested weight)) weightNonnegative).trans
    (Budget.Weighted.mul_allowance_le positive.le weightNonnegative)
  exact bound.trans paid

open Purelib.Data.Gaussian in
/-- The side-specific source sign equals the original boundary-orientation sign followed by optional reversal. -/
private theorem orientation (side : GridSide) (backward : Bool) (value : Basic.Canonical) :
    (if (match side with | .bottom | .right => !backward | .top | .left => backward)
      then value else -value) =
    (if backward then -(if side = .top ∨ side = .left then -value else value)
      else (if side = .top ∨ side = .left then -value else value)) := by
  cases side <;> cases backward
  all_goals first | rfl | exact (_root_.neg_neg value).symm

open Purelib.Data.Gaussian in
open Purelib.Data.List in

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.List in
open Purelib.Topology.Polygon in
/-- Original component source increments equal the ordered canonical edge valuations.

The equality preserves the exact component occurrence list, physical boundary membership and indexed edge identities for
both primitive readings. -/
private theorem component_boundary_values
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {index : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) :
    (List.ofFn (fun outer : Fin
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences.length =>
      let source := (Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
        (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences
          outer).sideOccurrence.source
      (⟨source.increment readings.left.values, source.increment readings.right.values⟩ : Stokes.PrimitivePoint))) =
        ((prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).program.indexed.map
          (fun edge => (⟨Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh
            readings.left.values edge,
            Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh readings.right.values edge⟩ :
              Stokes.PrimitivePoint))) := by
  let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
  let valuation := fun edge => (⟨Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh
    readings.left.values edge,
    Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh readings.right.values edge⟩ :
      Stokes.PrimitivePoint)
  let sourceValue := fun occurrence :
    Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    prepared.exterior.regular prepared.domains
      (PeriodMatrix.standardDifferential first) => (⟨occurrence.sideOccurrence.source.increment readings.left.values,
    occurrence.sideOccurrence.source.increment readings.right.values⟩ : Stokes.PrimitivePoint)
  have indexed : (component.prepared.occurrences.map (fun occurrence => valuation occurrence.placement.indexed)) =
      component.program.indexed.map valuation := by
    exact (Data.List.Map.map_map valuation (fun occurrence => occurrence.placement.indexed)
      (values := component.prepared.occurrences)).symm.trans
      (congrArg (List.map valuation) component.prepared.occurrences_eq)
  have values : component.prepared.occurrences.map sourceValue =
      component.prepared.occurrences.map (fun occurrence => valuation occurrence.placement.indexed) := by
    apply Map.map_congr_left
    intro occurrence member
    have componentMember : component ∈ prepared.exterior.prepared.components :=
      List.getElem_mem componentIndex.isLt
    have retained : occurrence ∈ prepared.exterior.prepared.occurrences := by
      rw [prepared.exterior.prepared.occurrences_eq]
      exact Flatten.mem_flatMap.mpr ⟨component, componentMember, member⟩
    have exterior : occurrence.placement.indexed ∈ prepared.lifted.exteriorBoundaries.flatten :=
      prepared.exterior.prepared.indexed_eq ▸ Map.mem_map_of_mem retained
    have physical : occurrence.placement.indexed ∈ prepared.lifted.boundaryLoops.flatten := by
      change _ ∈ (prepared.lifted.exteriorBoundaries ++ _).flatten
      rw [Data.List.Flatten.flatten_append]
      exact Data.List.Membership.mem_append.mpr (Or.inl exterior)
    have projected := (congrArg (fun source => source.project prepared.lifted.mesh.triangulation.faces)
      occurrence.side_source).trans occurrence.placement.location.sourceEdge_project
    have sourceMember := projected.symm ▸ physical
    have left := Meshes.PuncturedGrid.CanonicalPhysicalBoundary.canonical_physical_source
      occurrence.sideOccurrence.source sourceMember readings.left.values
    have right := Meshes.PuncturedGrid.CanonicalPhysicalBoundary.canonical_physical_source
      occurrence.sideOccurrence.source sourceMember readings.right.values
    exact congrArg₂ Stokes.PrimitivePoint.mk
      (left.symm.trans (congrArg (Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh
        readings.left.values) projected))
      (right.symm.trans (congrArg (Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh
        readings.right.values) projected))
  exact (OfFn.Basic.map_ofFn.symm.trans
    (congrArg (List.map sourceValue) (OfFn.Basic.ofFn_getElem component.prepared.occurrences))).trans
      (values.trans indexed)

open Purelib.Integration.Path.PairedIncrementArea (area) in
open Purelib.Curves.Hyperelliptic in
open Purelib.Topology.Polygon in
/-- The component boundary joining area equals the area of its exact canonical edge valuations. -/
private theorem component_joining_valuation
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {index : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) :
    ComponentBoundaryJoiningArea prepared componentIndex readings =
      area
        ((prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).program.indexed.map
          (fun edge => (⟨Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh
            readings.left.values edge,
            Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh readings.right.values edge⟩ :
              Stokes.PrimitivePoint))) :=
  congrArg area (component_boundary_values prepared componentIndex readings)

open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Pointwise primitive-pair errors bound the difference of their finite totals by the count square. -/
private theorem total_difference_bound {count : Nat}
    (fine coarse : Fin count → Stokes.PrimitivePoint) {error : Fraction.Rational}
    (nonnegative : 0 ≤ error) (accurate : ∀ i, Bounded ((fine i).sub (coarse i)) error) :
    Bounded ((PairedIncrementArea.total (List.ofFn fine)).sub
      (PairedIncrementArea.total (List.ofFn coarse))) ((count : Fraction.Rational)^2 * error) := by
  let pairs := List.ofFn (fun i => (fine i, coarse i))
  have bound := PairedIncrementArea.total_bound nonnegative
    (values := pairs.map (fun pair => pair.1.sub pair.2)) (by
      intro value member
      obtain ⟨pair, inPairs, rfl⟩ := Map.mem_map.mp member
      obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp inPairs
      exact accurate i) (count := count) (by rw [Data.List.Map.length_map, Data.List.OfFn.Basic.length_ofFn])
  rw [PairedIncrementComparison.total_differences, OfFn.Basic.map_ofFn, OfFn.Basic.map_ofFn] at bound
  exact bound

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Topology.Polygon in
/-- A bounded fine period and bounded fine-to-coarse error bound the coarse period.

Each coordinate's squared norm is bounded by twice the sum of the original fine bound and error bound. -/
private theorem period_transport_bound {fine coarse : Stokes.PrimitivePoint} {bound error : Fraction.Rational}
    (bounded : Bounded fine bound) (accurate : Bounded (fine.sub coarse) error) :
    Bounded coarse (2 * (bound + error)) := by
  have scalar (a b : Basic.Canonical)
      (ha : Basic.Canonical.normSq a ≤ bound)
      (hab : Basic.Canonical.normSq (a - b) ≤ error) :
      Basic.Canonical.normSq b ≤ 2 * (bound + error) := by
    have doubled : Basic.Canonical.normSq (a - (a - b)) ≤
        2 * (Basic.Canonical.normSq a + Basic.Canonical.normSq (a - b)) := by
      simpa only [Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using
        (Norm.Bounds.normSq_sub_le_two a (a - b))
    have estimate := doubled.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct ha hab) (by decide))
    rw [show a - (a - b) = b by ring1] at estimate
    exact estimate
  exact ⟨scalar _ _ bounded.1 accurate.1, scalar _ _ bounded.2 accurate.2⟩

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The intermediate bound on the original component's canonical primitive period.

It retains the source comparison, actual readings and endpoint allocation, combining the source total error with the
original occurrence-count squared endpoint error. -/
private def ComponentCanonicalPeriodEstimate
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (PeriodMatrix.standardDifferential second) requested minimum)
    {endpointTarget : Fraction.Rational}
    (allocated : Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest prepared.paid.cut.fixed first
      second endpointTarget)
    {index : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache)
    (allowance tolerance : Fraction.Rational) : Prop :=
    Bounded (PairedIncrementArea.total
      ((prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).program.indexed.map
        (fun edge => (⟨Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh readings.left.values
          edge,
          Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh readings.right.values edge⟩ :
            Stokes.PrimitivePoint))))
      (2 * (2 * (requested + ComponentTotalError prepared componentIndex comparison cache allowance tolerance) +
        ((prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences.length :
          Fraction.Rational)^2 *
          (16 * allocated.tolerance)))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.RootContinuation in
/-- Retained side estimates and endpoint accuracy bound the original component's canonical period.

The proof transports the exact retained physical total to the same ordered canonical edge valuations, keeping the source
error and endpoint error separate. -/
private theorem component_canonical_period_bound
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (PeriodMatrix.standardDifferential second) requested minimum)
    {endpointTarget : Fraction.Rational}
    (allocated : Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest prepared.paid.cut.fixed first
      second endpointTarget)
    {index : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache)
    {allowance tolerance : Fraction.Rational}
    (estimates : ∀ outer, RetainedExteriorSideEstimate prepared componentIndex comparison outer cache allowance
      tolerance)
    (later : allocated.index ≤ index) :
    ComponentCanonicalPeriodEstimate prepared componentIndex comparison allocated readings allowance tolerance := by
  unfold ComponentCanonicalPeriodEstimate
  let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
  let occurrence := fun outer : Fin component.prepared.occurrences.length =>
    Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences outer
  let fine := fun outer => signedPoint (occurrence outer).sourceForward
    (sideEndpointDifference (((prepared.traces.samples cache first second).samples.get
      (occurrence outer).sideOccurrence.position).get (occurrence outer).sideOccurrence.sheet)
      (occurrence outer).sideOccurrence.side)
  let coarse := fun outer => signedPoint (occurrence outer).sourceForward
    (cornerDifference cache first second (occurrence outer).sideOccurrence.position
      (occurrence outer).sideOccurrence.sheet (occurrence outer).sideOccurrence.side)
  have accurate (outer) : Bounded ((fine outer).sub (coarse outer)) (16 * allocated.tolerance) :=
    (signed_difference _ _ _).symm ▸ signed_bounded _ (side_endpoint_difference_bound allocated cache later
      (occurrence outer).sideOccurrence.position (occurrence outer).sideOccurrence.sheet _ _ (occurrence
        outer).sideOccurrence.side)
  have difference := total_difference_bound fine coarse
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) allocated.positive.le) accurate
  have physical : ComponentPhysicalTotal prepared componentIndex cache = PairedIncrementArea.total (List.ofFn fine) :=
    by
    apply congrArg PairedIncrementArea.total
    apply OfFn.Basic.ofFn_congr
    intro outer
    exact congrArg (signedPoint (occurrence outer).sourceForward) (side_total_eq_endpoints _ _)
  have bounded := NewtonRequestedExteriorSides.retained_exterior_component_total_bound prepared componentIndex
    comparison cache estimates
  have transported := period_transport_bound (physical ▸ bounded) difference
  have sources := OfFn.Basic.ofFn_congr (fun outer =>
    occurrence_increment readings.left readings.right (occurrence outer).sideOccurrence)
  have canonical := (component_boundary_values prepared componentIndex readings).symm.trans sources
  exact (congrArg PairedIncrementArea.total canonical).symm ▸ transported

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- The allocated endpoint target pays the original component's count-squared endpoint error. -/
private theorem component_endpoint_total_paid
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {endpointTarget : Fraction.Rational}
    (endpoints :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.SideRemainderRequest
      prepared.exterior.prepared prepared.paid.cut.fixed first second endpointTarget) :
    ((prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences.length :
      Fraction.Rational)^2 *
      (16 * endpoints.endpoints.tolerance) ≤ endpointTarget := by
  let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
  have countLe : component.prepared.occurrences.length ≤ endpoints.count := by
    rw [endpoints.count_eq, prepared.exterior.prepared.occurrences_eq]
    have member := Data.List.Map.mem_map_of_mem
      (f := fun component => component.prepared.occurrences)
      (List.getElem_mem componentIndex.isLt)
    have bound := Data.List.Flatten.length_le_flatten_of_mem member
    exact (congrArg List.length (Data.List.Flatten.flatMap_map id
      (fun component => component.prepared.occurrences) prepared.exterior.prepared.components)) ▸ bound
  have magnitude : (1 : Fraction.Rational) ≤ endpoints.endpoints.firstMagnitude.bound +
    endpoints.endpoints.secondMagnitude.bound + 1 :=
    le_add_of_nonneg_left (add_nonneg endpoints.endpoints.firstMagnitude.nonnegative
      endpoints.endpoints.secondMagnitude.nonnegative)
  have weight : (16 : Fraction.Rational) ≤ 128 *
      (endpoints.endpoints.firstMagnitude.bound + endpoints.endpoints.secondMagnitude.bound + 1) :=
    (by decide +kernel : (16 : Fraction.Rational) ≤ 128 * 1).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct magnitude (by
          decide +kernel : (0 : Fraction.Rational) ≤ 128))
  have small := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct weight
    endpoints.endpoints.positive.le).trans
    endpoints.endpoints.paid
  have allowancePositive : 0 < endpoints.allowance := endpoints.allowance_eq ▸
    Budget.Aggregate.perTerm_positive endpoints.positive endpoints.count
  have firstBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small
    (Fraction.Order.Arithmetic.sq_nonneg_direct (component.prepared.occurrences.length : Fraction.Rational))
  have countBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le component.prepared.occurrences.length))
      (Fraction.Cast.Order.natCast_le_direct countLe) 2) allowancePositive.le
  have paid := Budget.Aggregate.count_mul_perTerm_lt endpoints.positive endpoints.count
  rw [← endpoints.allowance_eq] at paid
  exact (firstBound.trans countBound).trans
    ((show (endpoints.count : Fraction.Rational)^2 * endpoints.allowance =
      (endpoints.count : Fraction.Rational) * ((endpoints.count : Fraction.Rational) * endpoints.allowance) by
        ring1).trans_le paid.le)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Both coordinates of the original component's canonical edge-valuation total satisfy the given squared bound. -/
@[expose] def ComponentCanonicalPeriodBound
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {index : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) (bound :
      Fraction.Rational) : Prop :=
  Bounded (PairedIncrementArea.total
    ((prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).program.indexed.map
      (fun edge => (⟨Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh readings.left.values
        edge,
        Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh readings.right.values edge⟩ :
          Stokes.PrimitivePoint)))) bound

open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- The original boundary preparation refined to the retained exterior source request's exact depth. -/
@[expose] def RefinedExteriorBoundary
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {requested : Fraction.Rational} {minimum : Nat}
    (result : ExteriorSourceRequest prepared requested minimum) :
    BoundaryPreparation preparation first second target radius floor :=
  NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Rat
/-- The endpoint request type for that exact retained exterior depth refinement. -/
@[expose] def ExteriorEndpointRequestAt
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {requested : Fraction.Rational} {minimum : Nat}
    (result : ExteriorSourceRequest prepared requested minimum)
    (endpointTarget : Fraction.Rational) : Type _ :=

    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.SideRemainderRequest
    (RefinedExteriorBoundary prepared result).exterior.prepared
    (RefinedExteriorBoundary prepared result).paid.cut.fixed first second endpointTarget

/-- The cut-pairing readings on the same original cache at the retained exterior depth refinement. -/
@[expose] def ExteriorReadingsAt
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {requested : Fraction.Rational} {minimum : Nat}
    (result : ExteriorSourceRequest prepared requested minimum)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index) :
      Type _ :=
  Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings
    (RefinedExteriorBoundary prepared result).paid.cut cache

end

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained source and endpoint requests bound every original component's canonical period.

At a stage covering both owners, each coordinate is bounded by twice the sum of the requested source allowance and
endpoint target. -/
theorem ExteriorSourceRequest.canonical_period_bound
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {requested : Fraction.Rational} {minimum : Nat}
    (result : ExteriorSourceRequest prepared requested minimum)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {endpointTarget : Fraction.Rational}
    (endpoints : ExteriorEndpointRequestAt prepared result
      endpointTarget)
    {index : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index}
    (readings : ExteriorReadingsAt prepared result cache)
    (later : result.index ≤ index) (endpointLater : endpoints.endpoints.index ≤ index) :
    ComponentCanonicalPeriodBound (RefinedExteriorBoundary
      prepared result) componentIndex readings
      (2 * (requested + endpointTarget)) := by
  have bounded := component_canonical_period_bound
    (RefinedExteriorBoundary prepared result) componentIndex
    (result.references.get componentIndex)
    endpoints.endpoints readings (fun outer => result.side_bound componentIndex outer cache later) endpointLater
  have totalPaid := result.total_errors_paid componentIndex cache later
  have endpointPaid := component_endpoint_total_paid
    (RefinedExteriorBoundary prepared result) componentIndex
    endpoints
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct (le_refl (result.localTarget / 4)) totalPaid) (by
            decide : (0 : Fraction.Rational) ≤ 2))
      endpointPaid) (by decide : (0 : Fraction.Rational) ≤ 2)
  have equal : 2 * (2 * (result.localTarget / 4 + result.localTarget) + endpointTarget) =
      5 * result.localTarget + 2 * endpointTarget := by
    calc
      _ = (result.localTarget / 4) * 4 + 4 * result.localTarget + 2 * endpointTarget := by ring1
      _ = _ := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide : (4 : Fraction.Rational) ≠ 0)]; ring1
  have requestedNonnegative : 0 ≤ requested :=
    (Norm.Basic.normSq_nonneg _).trans result.bounded.le
  have quarterNonnegative := Fraction.Order.Field.div_nonneg_direct requestedNonnegative
    (by decide : (0 : Fraction.Rational) ≤ 4)
  have localLe : result.localTarget ≤ requested / 4 :=
    (result.localTarget_eq.trans_le (Fraction.Order.Basic.min_le_right _ _)).trans
      (Budget.Aggregate.perTerm_le quarterNonnegative _)
  have sourcePaid : 5 * result.localTarget ≤ 2 * requested := by
    have small := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct localLe (by
        decide : (0 : Fraction.Rational) ≤ 5)
    have larger := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide : (5 : Fraction.Rational) ≤ 8) quarterNonnegative
    have cancel : 8 * (requested / 4) = 2 * requested := by
      calc
        _ = 2 * ((requested / 4) * 4) := by ring1
        _ = _ := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide : (4 : Fraction.Rational) ≠ 0)]
    exact small.trans (larger.trans_eq cancel)
  have requestPaid := (Fraction.Order.Arithmetic.add_le_add_direct sourcePaid (le_refl (2 * endpointTarget))).trans_eq
    (show 2 * requested + 2 * endpointTarget = 2 * (requested + endpointTarget) by ring1)
  have complete := paid.trans (equal.trans_le requestPaid)
  exact ⟨bounded.1.trans complete, bounded.2.trans complete⟩

section
open Purelib.Integration.Path.PairedIncrementArea (area)
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Topology.Polygon
/-- The total boundary joining area equals the sum of areas of the original components' canonical edge valuations. -/
theorem boundary_joining_valuation
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {index : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun i => ComponentBoundaryJoiningArea prepared i readings)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.exterior.prepared.components.map (fun component =>
        area (component.program.indexed.map
          (fun edge => (⟨Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh
            readings.left.values edge,
            Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh readings.right.values edge⟩ :
              Stokes.PrimitivePoint))))) := by
  have pointwise := congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum (OfFn.Basic.ofFn_congr
    (fun i => component_joining_valuation prepared i readings))
  have materialized := OfFn.Basic.map_ofFn
    (function := fun i : Fin prepared.exterior.prepared.components.length =>
      prepared.exterior.prepared.components[i.val]'i.isLt)
    (transform := fun component => area (component.program.indexed.map
      (fun edge => (⟨Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh readings.left.values
        edge,
        Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh readings.right.values edge⟩ :
          Stokes.PrimitivePoint))))
  exact pointwise.trans (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (materialized.symm.trans (congrArg _ (OfFn.Basic.ofFn_getElem prepared.exterior.prepared.components))))

/-- The retained physical component area splits into its signed centered-side sum and endpoint joining area. -/
private theorem component_readback (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index) :
    ComponentPhysicalArea prepared componentIndex cache =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
        ((prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences.map
        (fun occurrence =>
          Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.CenteredPerimeters.occurrenceArea
          (prepared.traces.samples cache first second) occurrence.sideOccurrence)) +
      ComponentJoiningArea prepared componentIndex cache := by
  apply congrArg₂ (· + ·)
  · have materialized := OfFn.Basic.map_ofFn
      (function := fun outer : Fin
        (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences.length =>

          (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences[
            outer.val]'outer.isLt)
      (transform := fun occurrence =>
        Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.CenteredPerimeters.occurrenceArea
        (prepared.traces.samples cache first second) occurrence.sideOccurrence)
    refine Eq.trans ?_ (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (materialized.symm.trans (congrArg _ (OfFn.Basic.ofFn_getElem
        (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences))))
    apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
    apply OfFn.Basic.ofFn_congr
    intro outer
    exact orientation _ _ _
  · apply congrArg area
    apply OfFn.Basic.ofFn_congr
    intro outer
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences outer
    exact congrArg (fun value => if occurrence.sourceForward then value
      else Stokes.PrimitivePoint.zero.sub value)
      (side_total_eq_endpoints _ _)

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
/-- The total retained physical component area splits into centered sides and component joining areas.

The equality uses the exact original component-to-occurrence flattening and source orientations without changing the
retained sample cache. -/
theorem physical_components_eq (prepared : BoundaryPreparation preparation first second target radius floor)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun i => ComponentPhysicalArea prepared i cache)) =
      prepared.exterior.prepared.centeredSideArea (prepared.traces.samples cache first second) +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun i => ComponentJoiningArea prepared i cache)) := by
  have pointwise := congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum (OfFn.Basic.ofFn_congr
    (fun i => component_readback prepared i cache))
  have split := Data.Gaussian.Norm.Sum.Basic.gaussianSum_map_add (List.ofFn (fun i : Fin
    prepared.exterior.prepared.components.length => i))
    (fun i => Data.Gaussian.Norm.Sum.Basic.gaussianSum
      ((prepared.exterior.prepared.components[i.val]'i.isLt).prepared.occurrences.map
      (fun occurrence =>
        Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.CenteredPerimeters.occurrenceArea
        (prepared.traces.samples cache first second) occurrence.sideOccurrence)))
    (fun i => ComponentJoiningArea prepared i cache)
  simp only [OfFn.Basic.map_ofFn, -eq_self, -iff_self] at split
  apply pointwise.trans (split.symm.trans (congrArg (fun value => value + _) ?_))
  have read := (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum (OfFn.Basic.map_ofFn.symm.trans
    (congrArg (List.map (fun component =>
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((component.prepared).occurrences.map (fun occurrence =>
      Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.CenteredPerimeters.occurrenceArea
        (prepared.traces.samples cache first second) occurrence.sideOccurrence)))) (OfFn.Basic.ofFn_getElem
        prepared.exterior.prepared.components))))
  refine read.trans ?_
  exact (Data.Gaussian.Norm.Sum.Basic.gaussianSum_map_flatMap prepared.exterior.prepared.components (fun component =>
    component.prepared.occurrences)
    (fun occurrence => Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.CenteredPerimeters.occurrenceArea
      (prepared.traces.samples cache first second) occurrence.sideOccurrence)).symm.trans
      (congrArg (fun values => Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map (fun occurrence =>
        Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.CenteredPerimeters.occurrenceArea
          (prepared.traces.samples cache first second) occurrence.sideOccurrence)))
        prepared.exterior.prepared.occurrences_eq.symm)

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation
/-- The exterior physical correction plus retained joining areas has a paid squared-norm bound.

At stages covering the original source and endpoint requests, the bound is twice the sum of their targets and retains
the exact refined exterior preparation. -/
theorem ExteriorSourceRequest.remainder_accurate
    {prepared : BoundaryPreparation preparation first second target radius floor}
    {requested : Fraction.Rational} {minimum : Nat}
    (result : ExteriorSourceRequest prepared requested minimum)
    {endpointTarget : Fraction.Rational}
    (endpoints :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.SideRemainderRequest
      (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth).exterior.prepared
        (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth).paid.cut.fixed first second
        endpointTarget)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings
      (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth).paid.cut cache)
    (later : result.index ≤ stage) (endpointLater : endpoints.endpoints.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Meshes.PuncturedGrid.PhysicalComponentCorrection.physicalComponentCorrection
      readings.normalized readings.neighbors readings.left readings.right .exterior +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun i => ComponentJoiningArea
        (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth) i cache))) <
      2 * (endpointTarget + requested) := by
  rw [← (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared
    result.depth).exterior.prepared.fineRemainder_eq_physical readings.neighbors]
  have endpoint := NewtonRequestedExteriorSides.exterior_sides_accurate
    (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth) _ endpoints readings endpointLater
  have physical := result.physical_accurate cache later
  rw [physical_components_eq
      (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth) cache] at physical
  have bound := (Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct endpoint physical))
  exact (congrArg Data.Gaussian.Norm.Basic.normSq (by ring1)).trans_lt bound

/-- The retained remaining area is close to the same refined component joining sum.

The cache stage covers the source, endpoint, selected-interface and omitted-hole banks; the bound retains their boundary
target and both remainder allowances. -/
theorem ExteriorSourceRequest.retained_area_bound
    {prepared : BoundaryPreparation preparation first second target radius floor}
    {requested : Fraction.Rational} {minimum : Nat}
    (result : ExteriorSourceRequest prepared requested minimum)
    {endpointTarget : Fraction.Rational}
    (endpoints :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.SideRemainderRequest
      (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth).exterior.prepared
        (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth).paid.cut.fixed first second
        endpointTarget)
    (interfaces : NewtonSelectedInterfaceBank.InterfaceBank (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth
      prepared result.depth).excision
      (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth).traces first second)
    (omitted : NewtonOmittedHoleBank.OmittedHoleBank (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared
      result.depth).excision
      (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth).traces first second)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth).Readings cache)
    (later : result.index ≤ stage) (endpointLater : endpoints.endpoints.index ≤ stage)
    (interfaceLater : interfaces.index ≤ stage) (omittedLater : omitted.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (readings.2.val.remaining.remainingArea -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun i => ComponentJoiningArea
        (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth) i cache))) <
      2 * (16 * target + 2 * (endpointTarget + requested)) := by
  have surfaceLater := (congrArg BoundaryPreparation.index result.refined_eq).symm.trans_le (result.refined_le.trans
    later)
  have retained := (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared
    result.depth).retained_exterior_bound interfaces omitted readings
    surfaceLater interfaceLater omittedLater
  have exterior := ExteriorSourceRequest.remainder_accurate result endpoints readings.1 later endpointLater
  have estimate := (Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct retained exterior))
  exact (congrArg Data.Gaussian.Norm.Basic.normSq (by ring1)).trans_lt estimate

end

open Purelib.Data.Gaussian in
/-- Subtracting the selected term from an exact selected-plus-remaining partition recovers the remaining term. -/
private theorem remove_selected {selected remaining paired : Basic.Canonical}
    (partition : selected + remaining = paired) : paired - selected = remaining := by
  rw [← partition]
  ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A strict fine-area bound transports through a weak fine-to-coarse joining bound. -/
private theorem transport_joining_bound {value fine coarse : Basic.Canonical} {bound error : Fraction.Rational}
    (original : Data.Gaussian.Norm.Basic.normSq (value - fine) < bound) (joining : Data.Gaussian.Norm.Basic.normSq
      (fine - coarse)
      ≤ error) :
    Data.Gaussian.Norm.Basic.normSq (value - coarse) < 2 * (bound + error) := by
  have combined := (Fraction.Order.Arithmetic.add_lt_add_right_direct original (Data.Gaussian.Norm.Basic.normSq (fine -
    coarse))).trans_le
    (Fraction.Order.Arithmetic.add_le_add_direct (le_refl bound) joining)
  have estimate := (Norm.Bounds.normSq_add_le_two (value - fine) (fine - coarse)).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2) combined)
  exact (congrArg Data.Gaussian.Norm.Basic.normSq (by ring1)).trans_lt estimate

open Purelib.Integration.Path.PairedIncrementArea (area) in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
open Purelib.Topology.Polygon in
open Purelib.Topology.Surface in
/-- The paid error between cut pairing, selected annular area and canonical exterior joining areas.

The formula retains paired and remaining word contractions, the closed correction, exact selected annuli and original
component edge valuations at the retained refined depth. -/
@[expose] def ExteriorCutPairingBound
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {requested : Fraction.Rational} {minimum : Nat}
    (result : ExteriorSourceRequest prepared requested minimum)
    (endpointTarget : Fraction.Rational)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth).Readings cache) : Prop
      :=
    Data.Gaussian.Norm.Basic.normSq ((2 * Word.Pairing.contract
        (fun row column => readings.1.integral.paired row column) readings.1.word.values +
      Word.Pairing.contract
        (fun row column => readings.1.integral.remaining row column) readings.1.word.values +
      readings.1.word.closedCorrection) - readings.2.val.annuli.selectedArea -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared
        result.depth).exterior.prepared.components.map (fun component =>
        area (component.program.indexed.map (fun edge =>
          (⟨Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
            (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth).lifted.mesh
            readings.1.left.values edge,
            Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
              (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth).lifted.mesh
              readings.1.right.values edge⟩ :
              Stokes.PrimitivePoint)))))) <
      2 * (2 * (16 * target + 2 * (endpointTarget + requested)) + endpointTarget)

open Purelib.Integration.Path.PairedIncrementArea (area) in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- The retained source and joining-endpoint requests certify the complete cut-pairing bound.

The stage covers the original source, endpoint, selected-interface and omitted-hole owners. Exact selected/remaining
partition and joining valuation identities transport the previously paid bounds. -/
theorem ExteriorSourceRequest.cut_pairing_bound
    {prepared : BoundaryPreparation preparation first second target radius floor}
    {requested : Fraction.Rational} {minimum : Nat}
    (result : ExteriorSourceRequest prepared requested minimum)
    {endpointTarget : Fraction.Rational}
    (endpoints : JoiningEndpointRequest (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared
      result.depth) endpointTarget)
    (interfaces : NewtonSelectedInterfaceBank.InterfaceBank (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth
      prepared result.depth).excision
      (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth).traces first second)
    (omitted : NewtonOmittedHoleBank.OmittedHoleBank (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared
      result.depth).excision
      (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth).traces first second)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth).Readings cache)
    (later : result.index ≤ stage) (endpointLater : endpoints.val.endpoints.index ≤ stage)
    (interfaceLater : interfaces.index ≤ stage) (omittedLater : omitted.index ≤ stage) :
    ExteriorCutPairingBound prepared result endpointTarget readings := by
  dsimp only [ExteriorCutPairingBound, -eq_self, -iff_self]
  have retained := ExteriorSourceRequest.retained_area_bound result endpoints.val interfaces omitted readings later
    endpointLater interfaceLater omittedLater
  have partition := (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared
    result.depth).selected_remaining_eq_paired readings.2.val
  have equal := remove_selected partition
  have original := (congrArg (fun value => Data.Gaussian.Norm.Basic.normSq (value -
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (List.ofFn (fun i => ComponentJoiningArea (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared
      result.depth) i cache)))) equal).trans_lt retained
  have estimate := transport_joining_bound original
    ((joining_boundary_bound (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth)
      endpoints.val.endpoints readings.1 endpointLater).trans endpoints.property)
  exact (congrArg (fun area => Data.Gaussian.Norm.Basic.normSq (readings.1.paired - readings.2.val.annuli.selectedArea -
    area))
    (boundary_joining_valuation (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth)
      readings.1)).symm.trans_lt estimate

end Purelib.Riemann.RootContinuation.NewtonRequestedExteriorRemainder
