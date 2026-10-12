module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Reverse
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JunctionOwnerBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedSideBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.PairedIncrementComparison
import Purelib.Integration.Polynomial.Rectangle.Perimeter.RetainedIncrements
import Purelib.Integration.Polynomial.Rectangle.SampleReadback
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
public import Purelib.Riemann.RootContinuation.NewtonRetainedExteriorSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceOccurrencePartition
public import Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourcePathComparison
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Riemann.Paths.RectangularSegmentRefinement
import Purelib.Riemann.Paths.RectangularTraceParameterReadings
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Data.Rat.Fraction.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Polynomial.Dense.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceAlignment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SharedPointReadings

public section

/-! Requested quantitative bounds for the retained exterior sides. -/
namespace Purelib.Riemann.RootContinuation.NewtonRequestedExteriorSides

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces.LiftedPuncturedGrid.ExteriorProgram

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece (junctionCount
  pieceIndex junction)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece (piece trace
  first_along last_along first_across last_across parameters_eq increasing)
open Purelib.Integration.Polynomial.Rectangle.Perimeter.RetainedIncrements (increments increments_eq)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordRuns (SourceChordRun)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation (occurrenceAt)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (maximum maximum_nonnegative
  le_maximum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData (SourceSample sourceParameters)
open
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison
  (orient_source_difference Piece)
open Purelib.Integration.Path.PairedIncrementArea (area total total_bound)
open Purelib.Integration.Path.PairedAreaBlocks (area_flatten total_flatten)
open Purelib.Integration.Path.PairedIncrementComparison (total_differences area_difference_bound)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest (OwnerRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea (parameterStep)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder (sideCenteredArea)
open Purelib.Geometry.Rectangle.SourceIntervals (axisIntervals)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Normalization
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {first second : Fin genus} {target radius : Fraction.Rational} {floor :
    Nat}
  {differential : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

section
open Purelib.Data.Gaussian
/-- Applying one orientation sign to each Gaussian entry applies that sign to its finite sum. -/
private theorem oriented_sum (forward : Bool) (values : List Basic.Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map (fun value => if forward then value else -value)) =
      if forward then Data.Gaussian.Norm.Sum.Basic.gaussianSum values else -Data.Gaussian.Norm.Sum.Basic.gaussianSum
        values := by
  induction values with
  | nil =>
    cases forward
    · change (0 : Basic.Canonical) = -0; ring1
    · rfl
  | cons value rest ih =>
    change (if forward then value else -value) + _ = _
    rw [ih]
    cases forward
    · change -value + -Data.Gaussian.Norm.Sum.Basic.gaussianSum rest = -(value +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum rest)
      ring1
    · rfl

/-- Reversing a Gaussian value's orientation preserves its squared norm. -/
private theorem oriented_norm (forward : Bool) (value : Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (if forward then value else -value) = Data.Gaussian.Norm.Basic.normSq value := by
  cases forward
  · exact Norm.Basic.normSq_neg _
  · rfl

end

/-- Orienting a list by keeping or reversing it preserves its length. -/
private theorem oriented_length {α : Type} (forward : Bool) (values : List α) :
    (if forward then values else values.reverse).length = values.length := by
  cases forward
  · change values.reverse.length = values.length
    exact Data.List.Reverse.length_reverse values
  · rfl

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.RootContinuation in
open Purelib.Topology.Polygon in
/-- The retained source component has paid residual and total-area bounds at the original mesh depth.

Its signed occurrence areas, paired totals and resampling errors retain the same source-parent runs, reference allowance
and squared original parent count. -/
@[expose] def RetainedExteriorComponentSourceBound
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum),
    let source := fun outer : Fin component.prepared.occurrences.length =>
      let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
        outer
      let side := occurrence.sideOccurrence.side
      let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
        occurrence.sideOccurrence.sheet).meshes.entries.get
        occurrence.sideOccurrence.position
      (List.ofFn (fun i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh
        side + 1) =>
        (NewtonRetainedExteriorSources.retainedExteriorChord prepared componentIndex comparison outer
          (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side
          i)).increments)).flatten
    let forward := fun outer : Fin component.prepared.occurrences.length =>
      (Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
        outer).sourceForward
    let remainders := fun outer : Fin component.prepared.occurrences.length =>
      let grouped := NewtonRetainedExteriorSources.retainedExteriorSourceGrouping prepared componentIndex comparison
        outer
      let blocks := grouped.runs.map Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.values
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map PairedIncrementArea.area) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum
          ((comparison.sourceOccurrenceBlocks outer (forward outer)).map PairedIncrementArea.area)
    let areas := fun outer => if forward outer then PairedIncrementArea.area (source outer)
      else -PairedIncrementArea.area (source outer)
    let totals := fun outer => if forward outer then PairedIncrementArea.total (source outer)
      else Stokes.PrimitivePoint.zero.sub (PairedIncrementArea.total (source outer))
    let errors := fun outer => if forward outer then remainders outer else -remainders outer
    let rate := 16 * comparison.sourceMagnitude^2 *
      ((1 / 2 : Fraction.Rational)^prepared.paid.cut.exterior.prepared.energy.depth)^2
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn areas) +
      PairedIncrementArea.area (List.ofFn totals) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn errors)) < requested ∧
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn areas) +
      PairedIncrementArea.area (List.ofFn totals)) ≤
        2 * (requested + (comparison.original.plans.length : Fraction.Rational)^2 * rate + requested / 128)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle in
open Purelib.Integration.Path in
open Purelib.Riemann.RootContinuation in
open Purelib.Topology.Polygon in
/-- Combine the exact retained source-run readbacks and resampling payments into the component bounds.

Orientation preserves each run's squared error, while original parent order and count retain the exact source reference
and its separate allowance. -/
theorem retained_exterior_component_source_bound
    (prepared : BoundaryPreparation preparation first second target radius floor) :
    RetainedExteriorComponentSourceBound prepared := by
  intro componentIndex component requested minimum comparison source forward remainders areas totals errors rate
  have sourceTotals (outer : Fin component.prepared.occurrences.length) :
      PairedIncrementArea.total (source outer) =
        PairedIncrementArea.total (comparison.sourceOccurrenceBlocks outer (forward outer)).flatten := by
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let side := occurrence.sideOccurrence.side
    let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
      occurrence.sideOccurrence.sheet).meshes.entries.get occurrence.sideOccurrence.position
    let intervals := SourceIntervals.axisIntervals mesh occurrence.sourceVertical
    let chords := fun i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh
      side + 1) =>
      (⟨intervals[(Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side
        i).val]'(Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i).isLt,
        NewtonRetainedExteriorSources.retainedExteriorChord prepared componentIndex comparison outer
          (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i)⟩ :
        Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord comparison occurrence.sourceVertical)
    change PairedIncrementArea.total
      (List.ofFn (fun i => Meshes.PuncturedGrid.Exterior.SourceChordRuns.StoredSourceChord.increments (chords
        i))).flatten = _
    exact comparison.source_total_ofFn outer (forward outer) (source := chords)
      (NewtonRetainedExteriorSources.retainedExteriorSourceGrouping prepared componentIndex comparison outer)
      (NewtonRetainedExteriorSources.retained_exterior_run_totals prepared componentIndex comparison outer)
  have orientedTotals := OfFn.Basic.ofFn_congr (fun outer : Fin component.prepared.occurrences.length =>
    (congrArg (fun value => if forward outer then value else Stokes.PrimitivePoint.zero.sub value)
      (sourceTotals outer)).trans (comparison.sourceOccurrenceBlocks_total_orientation outer (forward outer)))
  have differences (outer : Fin component.prepared.occurrences.length) :
      areas outer - PairedIncrementArea.area (comparison.sourceOccurrenceBlocks outer true).flatten = errors outer := by
    exact
      SurfacePreparation.ClosedBoundaryComparison.orient_source_difference
      (forward outer) (PairedIncrementArea.area (source outer))
      (PairedIncrementArea.area (comparison.sourceOccurrenceBlocks outer (forward outer)).flatten)
      (remainders outer) (PairedIncrementArea.area (comparison.sourceOccurrenceBlocks outer true).flatten)
      (NewtonRetainedExteriorSources.retained_exterior_source_area_difference prepared componentIndex comparison outer)
      (comparison.sourceOccurrenceBlocks_area_orientation outer (forward outer))
  have estimate := comparison.component_source_bound areas errors differences
  have reference := (congrArg (fun joined => Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (List.ofFn
    areas) +
    PairedIncrementArea.area joined - Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn errors)))
      orientedTotals).trans_lt estimate
  refine ⟨reference, ?_⟩
  let terms := fun outer : Fin component.prepared.occurrences.length =>
    let grouped := NewtonRetainedExteriorSources.retainedExteriorSourceGrouping prepared componentIndex comparison outer
    (grouped.runs.map (fun run => PairedIncrementArea.area run.values -
      comparison.sourceReferenceArea (forward outer) run.parent)).map (fun value => if forward outer then value else
        -value)
  have readback (outer : Fin component.prepared.occurrences.length) :
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms outer) = errors outer :=
    (oriented_sum (forward outer) _).trans (congrArg (fun value => if forward outer then value else -value)
      (comparison.source_runs_resampling_eq outer (forward outer)
        (NewtonRetainedExteriorSources.retainedExteriorSourceGrouping prepared componentIndex comparison outer).runs
        (NewtonRetainedExteriorSources.retained_exterior_run_order prepared componentIndex comparison outer)))
  have lengths (outer : Fin component.prepared.occurrences.length) :
      (terms outer).length = (comparison.parentIndices outer).length := by
    let runs := (NewtonRetainedExteriorSources.retainedExteriorSourceGrouping prepared componentIndex comparison
      outer).runs
    have ordered := NewtonRetainedExteriorSources.retained_exterior_run_order prepared componentIndex comparison outer
    change runs.map Meshes.PuncturedGrid.Exterior.SourceChordRuns.SourceChordRun.parent =
      (if forward outer then comparison.parentIndices outer else (comparison.parentIndices outer).reverse) at ordered
    exact (Data.List.Map.length_map _ _).trans ((Data.List.Map.length_map _ runs).trans
      ((Data.List.Map.length_map _ runs).symm.trans ((congrArg List.length ordered).trans
        (oriented_length (forward outer) (comparison.parentIndices outer)))))
  have nonnegative : 0 ≤ rate := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have parentRate (index : Fin comparison.original.plans.length) :
      max (16 * (comparison.sourceDensity index)^2 *
        ((1 / 2 : Fraction.Rational)^prepared.paid.cut.exterior.prepared.energy.depth)^2)
        (comparison.entries.get index).referenceError ≤ rate + comparison.referenceAllowance := by
    have density : comparison.sourceDensity index ≤ comparison.sourceMagnitude :=
      Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum _ (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩)
    have physical := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.pow_le_pow_direct (comparison.sourceDensity_nonnegative index) density 2) (by
            decide : (0 : Fraction.Rational) ≤ 16))
      (Fraction.Order.Arithmetic.sq_nonneg_direct ((1 / 2 :
        Fraction.Rational)^prepared.paid.cut.exterior.prepared.energy.depth))
    have allowance := comparison.reference_le index
    exact Fraction.Order.Basic.max_le (physical.trans (le_add_of_nonneg_right comparison.reference_positive.le))
      (allowance.trans (le_add_of_nonneg_left nonnegative))
  have bounds (outer : Fin component.prepared.occurrences.length) (value : Basic.Canonical)
      (member : value ∈ terms outer) : Data.Gaussian.Norm.Basic.normSq value ≤ rate + comparison.referenceAllowance :=
        by
    obtain ⟨raw, rawMember, rfl⟩ := Map.mem_map.mp member
    obtain ⟨run, runMember, rfl⟩ := Map.mem_map.mp rawMember
    have paid := NewtonRetainedExteriorSources.retained_exterior_run_resampling prepared componentIndex comparison outer
      run runMember
    have depth := prepared.paid.cut.exterior.prepared.energy.mesh_depth
      (Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
        outer).sideOccurrence.sheet
      (Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
        outer).sideOccurrence.position
    have rateEq := congrArg (fun depth => max (16 * (comparison.sourceDensity run.parent)^2 * ((1 / 2 :
      Fraction.Rational)^depth)^2)
      (comparison.entries.get run.parent).referenceError) depth
    have bound := (paid.trans_eq rateEq).trans (parentRate run.parent)
    exact (oriented_norm (forward outer) _).trans_le bound
  have residual := comparison.component_resampling_bound terms errors readback lengths bounds
  have paid := comparison.reference_paid.le
  have residualPaid : Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn errors)) ≤
      (comparison.original.plans.length : Fraction.Rational)^2 * rate + requested / 128 := by
    have allocation := Fraction.Order.Arithmetic.add_le_add_direct
      (le_refl ((comparison.original.plans.length : Fraction.Rational)^2 * rate)) paid
    exact residual.trans ((show (comparison.original.plans.length : Fraction.Rational)^2 * (rate +
      comparison.referenceAllowance) =
      (comparison.original.plans.length : Fraction.Rational)^2 * rate +
        (comparison.original.plans.length : Fraction.Rational) * ((comparison.original.plans.length : Fraction.Rational)
          * comparison.referenceAllowance) by ring1).trans_le allocation)
  let value := Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn areas) +
    PairedIncrementArea.area (List.ofFn totals)
  let error := Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn errors)
  have combined := Norm.Bounds.normSq_add_le_two (value - error) error
  rw [show value - error + error = value by ring1] at combined
  exact combined.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    ((Fraction.Order.Arithmetic.add_le_add_direct reference.le residualPaid).trans_eq (by ring1)) (by decide))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle in
open Purelib.Integration.Path in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- A retained physical fragment has separate area and total comparison bounds against its original source chord.

The original assigned parent, trace parameters, owner request and cache stage identify the same increments; the source
total also equals its exact chord endpoint value. -/
@[expose] def RetainedExteriorFragmentBound
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀
    (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    let componentMember : component ∈ prepared.exterior.prepared.components := List.getElem_mem componentIndex.isLt
    ∀
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
    (outer : Fin component.prepared.occurrences.length),
    let originalOccurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      component.prepared.occurrences outer
    let sheet := originalOccurrence.sideOccurrence.sheet
    let position := originalOccurrence.sideOccurrence.position
    let vertical := originalOccurrence.sourceVertical
    let forward := originalOccurrence.sourceForward
    let meshes := (prepared.paid.cut.exterior.prepared.energy.entries.get sheet).meshes
    let intervals := SourceIntervals.axisIntervals (meshes.entries.get position) vertical
    ∀
    (intervalIndex : Fin intervals.length),
    let physical := intervals[intervalIndex.val]'intervalIndex.isLt
    let present : physical ∈ intervals := List.getElem_mem intervalIndex.isLt
    let crossing := comparison.locateSideInterval outer meshes physical present
    let i := crossing.index
    let assigned := crossing.assigned
    let occurrence := assigned.occurrence
    let member := assigned.in_surface prepared.exterior.prepared componentMember
    let split := assigned.selected
    let rangeCertificate := NewtonRetainedExteriorSources.locateRetainedParentInterval prepared assigned member sheet
      position vertical forward physical present crossing.lower crossing.upper
    let range := rangeCertificate.val
    let mesh := meshes.entries.get position
    let side := originalOccurrence.sideOccurrence.side
    let perimeter := (prepared.traces.get position).get sheet
    let count := RectangularDyadicPairedTrace.dyadicCount mesh.depth
    let trace := Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.trace perimeter side
      intervalIndex
    let firstAlong := Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.first_along mesh side
      intervalIndex
    let lastAlong := Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.last_along mesh side
      intervalIndex
    let firstAcross := (Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.first_across mesh side
      intervalIndex).trans

        (SurfacePreparation.ClosedBoundaryComparison.sourceAcross_side
        originalOccurrence).symm
    let lastAcross := (Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.last_across mesh side
      intervalIndex).trans

        (SurfacePreparation.ClosedBoundaryComparison.sourceAcross_side
        originalOccurrence).symm
    let transport := assigned.traceParameters rangeCertificate (crossing.lower.trans_lt crossing.upper)
      trace firstAlong lastAlong firstAcross lastAcross
    let parameters := transport.parameters
    ∀ {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index),
    let samples := ((prepared.traces.samples cache first second).samples.get position).get sheet
    let ownedIncrements := Perimeter.RetainedIncrements.increments samples side intervalIndex
    ∀
    {allowance : Fraction.Rational} (budget : NoisyPathArea.LengthErrorBudget count allowance)
    (owners : Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence
      (standardDifferential second) budget.tolerance) (_later : owners.index ≤ index),
    let located := NewtonRetainedExteriorSources.locateRetainedExteriorInterval prepared sheet position member
      split.split split.member
      vertical physical present range rangeCertificate.property.1 rangeCertificate.property.2
    let length := Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward
      (parameters 0) (parameters (Fin.last count))
    let sourceChord := (NewtonRetainedExteriorSources.retainedExteriorChord prepared componentIndex comparison outer
      intervalIndex).value
    let sourceIncrements := (NewtonRetainedExteriorSources.retainedExteriorChord prepared componentIndex comparison
      outer intervalIndex).increments
    comparison.OwnedAreaBound occurrence i located.piece index length allowance budget.tolerance
      (PairedIncrementArea.area ownedIncrements) (PairedIncrementArea.area sourceIncrements) ∧
      comparison.OwnedTotalsBound occurrence i located.piece index length budget.tolerance
        (PairedIncrementArea.total ownedIncrements) (PairedIncrementArea.total sourceIncrements) ∧
      PairedIncrementArea.total sourceIncrements = sourceChord

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece
  Purelib.Integration.Polynomial.Rectangle.Perimeter.RetainedIncrements in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Integration.Path in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Periods in
open Purelib.Riemann.RootContinuation in
open Purelib.Topology.Polygon in
/-- Transport the original paired-owner estimates onto the exact retained physical and source increments.

Readback equalities reuse the original whole-side samples and source chord, retaining area, total and endpoint
identities separately. -/
theorem retained_exterior_fragment_bound
    (prepared : BoundaryPreparation preparation first second target radius floor) :
    RetainedExteriorFragmentBound prepared := by
  intro componentIndex component componentMember requested minimum comparison outer originalOccurrence sheet position
    vertical forward meshes intervals intervalIndex physical present crossing i assigned occurrence member split
      rangeCertificate range
    mesh side perimeter count trace firstAlong lastAlong firstAcross lastAcross transport parameters index cache samples
      ownedIncrements
    allowance budget owners later located length sourceChord sourceIncrements
  have inside := Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.trace_inside transport
  have ordered := Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.trace_ordered transport
    (Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.increasing perimeter side intervalIndex)
  -- These witnesses live only in the erased proof. The conclusion consumes
  -- the original whole-side centered vector, not a newly evaluated sample.
  let leftBank := cache.normalize.get first
  let rightBank := cache.normalize.get second
  let leftData := (leftBank.get position).atSheet sheet
  let rightData := (rightBank.get position).atSheet sheet
  let left := trace.leftReadings leftData.anchors leftData.offsets
  let right := trace.leftReadings rightData.anchors rightData.offsets
  let owned := CenteredBilinearPath.Sample.build
    (fun vertex => (⟨left.values vertex, right.values vertex⟩ : Stokes.PrimitivePoint))
  let retainedSource : Meshes.PuncturedGrid.Exterior.SourceChordData.SourceSample
      comparison i forward range mesh.depth :=
    (NewtonRetainedExteriorSources.retainedExteriorChord prepared componentIndex comparison outer intervalIndex).sample
  have sourceParametersEq (vertex : Fin (count + 1)) :
      Meshes.PuncturedGrid.Exterior.SourceChordData.sourceParameters forward range mesh.depth vertex =
        parameters vertex :=
    ((transport.parameters_eq vertex).trans
      (congrArg (fun parameter =>
        Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.firstParameter forward range + parameter *
          (Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.lastParameter forward range -
            Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.firstParameter forward range))
        (Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.parameters_eq perimeter side
          intervalIndex vertex))).symm
  let source := SampleReadback.Sample.readback retainedSource (last := fun vertex => comparison.sourceValues i
    (parameters vertex))
    (fun vertex => congrArg (comparison.sourceValues i) (sourceParametersEq vertex))
  have sourceEq : CenteredPathIncrements.Sample.increments source = sourceIncrements :=
    SampleReadback.Sample.readback_increments retainedSource (fun vertex => congrArg (comparison.sourceValues i)
      (sourceParametersEq vertex))
  have valuesEq (vertex : Fin (count + 1)) :
      (⟨left.values vertex, right.values vertex⟩ : Stokes.PrimitivePoint) =
        Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize first second position sheet
          (Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.piece mesh side
            intervalIndex).leftColumn
          (Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.piece mesh side
            intervalIndex).leftRow (trace.points vertex) :=
    congrArg₂ Stokes.PrimitivePoint.mk
      (trace.leftReadings_value leftData.anchors leftData.offsets vertex)
      (trace.leftReadings_value rightData.anchors rightData.offsets vertex)
  have incrementsEq : CenteredPathIncrements.Sample.increments owned = ownedIncrements := by
    refine ((CenteredPathIncrements.Sample.increments_raw owned).trans (OfFn.Basic.ofFn_congr ?_)).trans
      (Perimeter.RetainedIncrements.increments_eq samples side intervalIndex).symm
    intro edge
    exact congrArg₂ Stokes.PrimitivePoint.sub (valuesEq edge.succ) (valuesEq edge.castSucc)
  have areaEq : PairedIncrementArea.area ownedIncrements = owned.centeredArea :=
    (congrArg PairedIncrementArea.area incrementsEq.symm).trans (CenteredPathIncrements.Sample.increments_area owned)
  let firstReadings := occurrence.compared.sharedReadings leftBank occurrence.aligned left
  let secondReadings := (occurrence.recastComparison (standardDifferential second)).sharedReadings
    rightBank (occurrence.recastComparison_aligned (standardDifferential second)) right
  let reused := SampleReadback.Sample.readback owned (fun vertex => congrArg₂ Stokes.PrimitivePoint.mk
    (congrArg (fun values => values vertex) firstReadings.property.symm)
    (congrArg (fun values => values vertex) secondReadings.property.symm))
  have original := comparison.owned_fragment_area_bound occurrence i assigned.parent_mem located.piece leftBank
    rightBank
    parameters (fun vertex => located.contains (inside vertex)) forward ordered budget owners later
      (transport.readings firstReadings.val) (transport.readings secondReadings.val) reused source
  have totals := comparison.owned_fragment_totals_bound occurrence i assigned.parent_mem located.piece leftBank
    rightBank
    parameters (fun vertex => located.contains (inside vertex)) forward owners later
      (transport.readings firstReadings.val) (transport.readings secondReadings.val) reused source
  have totalReadback := congrArg PairedIncrementArea.total incrementsEq
  have firstParameterEq : parameters 0 = Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.firstParameter
      assigned.occurrence.sourceForward rangeCertificate.val := by
    rw [transport.parameters_eq, trace.first_eq]
    ring1
  have sourceReadback : PairedIncrementArea.total (CenteredPathIncrements.Sample.increments source) = sourceChord :=
    (CenteredPathIncrements.Sample.increments_total source).trans (congrArg₂ Stokes.PrimitivePoint.sub
      (congrArg (comparison.sourceValues i) transport.last_parameter)
      (congrArg (comparison.sourceValues i) firstParameterEq))
  have retainedTotals := Eq.mp (congrArg
    (fun owned => comparison.OwnedTotalsBound occurrence i located.piece index length budget.tolerance owned
      (PairedIncrementArea.total (CenteredPathIncrements.Sample.increments source))) totalReadback) totals
  have fineArea := (congrArg₂ (fun owned source => Data.Gaussian.Norm.Basic.normSq (owned - source)) areaEq
    (CenteredPathIncrements.Sample.increments_area source)).trans_le original
  have retainedArea := (congrArg (fun increments =>
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ownedIncrements - PairedIncrementArea.area increments))
      sourceEq).symm.trans_le fineArea
  have finalTotals := Eq.mp (congrArg (fun increments => comparison.OwnedTotalsBound occurrence i located.piece
    index length budget.tolerance (PairedIncrementArea.total ownedIncrements)
      (PairedIncrementArea.total increments)) sourceEq) retainedTotals
  exact ⟨retainedArea, finalTotals, (congrArg PairedIncrementArea.total sourceEq).symm.trans sourceReadback⟩

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Each retained physical junction meets one quarter of its original paired-owner tolerance. -/
@[expose] def RetainedExteriorJunctionBound
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (outer : Fin prepared.exterior.prepared.occurrences.length),
    let occurrence := prepared.exterior.prepared.occurrences[outer.val]'outer.isLt
    let position := occurrence.sideOccurrence.position
    let sheet := occurrence.sideOccurrence.sheet
    let side := occurrence.sideOccurrence.side
    let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get sheet).meshes.entries.get position
    ∀ (junctionIndex : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh
      side))
      {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index)
        {tolerance : Fraction.Rational}
      (owners : Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence
        (standardDifferential second) tolerance) (_later : owners.index ≤ index),
    let samples := ((prepared.traces.samples cache first second).samples.get position).get sheet
    Bounded (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junction samples side junctionIndex)
      (tolerance / 4)

open Purelib.Curves.Hyperelliptic in
/-- The retained paired-owner request bounds each exact original physical junction at any later stage. -/
theorem retained_exterior_junction_bound
    (prepared : BoundaryPreparation preparation first second target radius floor) :
    RetainedExteriorJunctionBound prepared := by
  intro outer occurrence position sheet side mesh junctionIndex index cache tolerance owners later samples
  exact Meshes.PuncturedGrid.Exterior.JunctionOwnerBounds.SurfaceOccurrence.retained_junction_bound occurrence
    ((prepared.traces.get position).get sheet)
    (cache.normalize.get first) (cache.normalize.get second) samples side junctionIndex owners later

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle in
open Purelib.Topology.Polygon in
/-- Separate area and total rates with the exact source increments for every retained physical interval.

The original component, occurrence and interval indices determine the assigned source piece; stage, allowance and
tolerance remain explicit arguments. -/
@[expose] def RetainedExteriorPieceRates
    (prepared : BoundaryPreparation preparation first second target radius floor) : Type _ :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (_comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let meshes := (prepared.paid.cut.exterior.prepared.energy.entries.get occurrence.sideOccurrence.sheet).meshes
    Fin (SourceIntervals.axisIntervals (meshes.entries.get occurrence.sideOccurrence.position)
      occurrence.sourceVertical).length →
      Nat → Fraction.Rational → Fraction.Rational → (Fraction.Rational × Fraction.Rational) × List Stokes.PrimitivePoint

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece in
open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Rectangle in
open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- Compute the retained interval's original area and total error rates and source increment list.

The exact side crossing and trace parameter transport locate the original piece and oriented length without replacing
its source-chord owner. -/
@[expose] def retainedExteriorPieceRates
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorPieceRates prepared
      := by
  intro componentIndex component requested minimum comparison outer occurrence meshes intervalIndex index allowance
    tolerance
  let sheet := occurrence.sideOccurrence.sheet
  let position := occurrence.sideOccurrence.position
  let vertical := occurrence.sourceVertical
  let forward := occurrence.sourceForward
  let intervals := SourceIntervals.axisIntervals (meshes.entries.get position) vertical
  let physical := intervals[intervalIndex.val]'intervalIndex.isLt
  have present : physical ∈ intervals := List.getElem_mem intervalIndex.isLt
  let crossing := comparison.locateSideInterval outer meshes physical present
  let assigned := crossing.assigned
  have member := assigned.in_surface prepared.exterior.prepared (List.getElem_mem componentIndex.isLt)
  let rangeCertificate := NewtonRetainedExteriorSources.locateRetainedParentInterval prepared assigned member sheet
    position vertical forward physical present crossing.lower crossing.upper
  let range := rangeCertificate.val
  let split := assigned.selected
  let located := NewtonRetainedExteriorSources.locateRetainedExteriorInterval prepared sheet position member split.split
    split.member
    vertical physical present range rangeCertificate.property.1 rangeCertificate.property.2
  let mesh := meshes.entries.get position
  let side := occurrence.sideOccurrence.side
  let perimeter := (prepared.traces.get position).get sheet
  let trace := Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.trace perimeter side
    intervalIndex
  let firstAcross := (Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.first_across mesh side
    intervalIndex).trans

      (SurfacePreparation.ClosedBoundaryComparison.sourceAcross_side
      occurrence).symm
  let lastAcross := (Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.last_across mesh side
    intervalIndex).trans

      (SurfacePreparation.ClosedBoundaryComparison.sourceAcross_side
      occurrence).symm
  let transport := assigned.traceParameters rangeCertificate (crossing.lower.trans_lt crossing.upper)
    trace (Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.first_along mesh side intervalIndex)
      (Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.last_along mesh side intervalIndex)
        firstAcross lastAcross
  let count := RectangularDyadicPairedTrace.dyadicCount mesh.depth
  let length := Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward
    (transport.parameters 0) (transport.parameters (Fin.last count))
  exact ⟨⟨comparison.ownedAreaError assigned.occurrence crossing.index located.piece index length allowance tolerance,
    comparison.ownedTotalError assigned.occurrence crossing.index located.piece index length tolerance⟩,
    (NewtonRetainedExteriorSources.retainedExteriorChord prepared componentIndex comparison outer
      intervalIndex).increments⟩

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle in
/-- Every retained physical interval's area and total rates meet their respective target bounds. -/
@[expose] def RetainedExteriorPieceEstimate
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (standardDifferential second) requested minimum)
    (index : Nat) (allowance tolerance areaTarget totalTarget : Fraction.Rational) : Prop :=
  ∀ outer : Fin
    (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences.length,
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences outer
    let meshes := (prepared.paid.cut.exterior.prepared.energy.entries.get occurrence.sideOccurrence.sheet).meshes
    ∀ intervalIndex : Fin (SourceIntervals.axisIntervals (meshes.entries.get occurrence.sideOccurrence.position)
      occurrence.sourceVertical).length,
      let rates := retainedExteriorPieceRates prepared componentIndex comparison outer intervalIndex index allowance
        tolerance
      rates.1.1 ≤ areaTarget ∧ rates.1.2 ≤ totalTarget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Uniform original piece estimates on unit-length fragments pay all retained physical-interval rates. -/
@[expose] def RetainedExteriorPiecePayment
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ componentIndex : Fin prepared.exterior.prepared.components.length,
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (index : Nat) (allowance tolerance areaTarget totalTarget : Fraction.Rational),
    (∀ outer : Fin component.prepared.occurrences.length,
      let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
        outer
      ∀ (i : Fin comparison.original.plans.length)
        (piece :
          SurfacePreparation.ClosedBoundaryComparison.Piece
          comparison occurrence i)
        (length : Fraction.Rational), (0 ≤ length ∧ length ≤ 1) →
        comparison.ownedAreaError occurrence i piece index length allowance tolerance ≤ areaTarget ∧
        comparison.ownedTotalError occurrence i piece index length tolerance ≤ totalTarget) →
      RetainedExteriorPieceEstimate prepared componentIndex comparison index allowance tolerance areaTarget totalTarget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece in
open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Rectangle in
open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- The original trace-length certificate specializes uniform piece payment to every retained physical interval. -/
theorem retained_exterior_piece_bound
    (prepared : BoundaryPreparation preparation first second target radius floor) :
      RetainedExteriorPiecePayment prepared := by
  intro componentIndex component requested minimum comparison index allowance tolerance areaTarget totalTarget paid
    outer occurrence meshes intervalIndex rates
  let sheet := occurrence.sideOccurrence.sheet
  let position := occurrence.sideOccurrence.position
  let vertical := occurrence.sourceVertical
  let forward := occurrence.sourceForward
  let intervals := SourceIntervals.axisIntervals (meshes.entries.get position) vertical
  let physical := intervals[intervalIndex.val]'intervalIndex.isLt
  have present : physical ∈ intervals := List.getElem_mem intervalIndex.isLt
  let crossing := comparison.locateSideInterval outer meshes physical present
  let assigned := crossing.assigned
  have member := assigned.in_surface prepared.exterior.prepared (List.getElem_mem componentIndex.isLt)
  let rangeCertificate := NewtonRetainedExteriorSources.locateRetainedParentInterval prepared assigned member sheet
    position vertical forward physical present crossing.lower crossing.upper
  let range := rangeCertificate.val
  let split := assigned.selected
  let located := NewtonRetainedExteriorSources.locateRetainedExteriorInterval prepared sheet position member split.split
    split.member
    vertical physical present range rangeCertificate.property.1 rangeCertificate.property.2
  let mesh := meshes.entries.get position
  let side := occurrence.sideOccurrence.side
  let perimeter := (prepared.traces.get position).get sheet
  let trace := Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.trace perimeter side
    intervalIndex
  let firstAcross := (Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.first_across mesh side
    intervalIndex).trans

      (SurfacePreparation.ClosedBoundaryComparison.sourceAcross_side
      occurrence).symm
  let lastAcross := (Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.last_across mesh side
    intervalIndex).trans

      (SurfacePreparation.ClosedBoundaryComparison.sourceAcross_side
      occurrence).symm
  let transport := assigned.traceParameters rangeCertificate (crossing.lower.trans_lt crossing.upper)
    trace (Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.first_along mesh side intervalIndex)
      (Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece.last_along mesh side intervalIndex)
        firstAcross lastAcross
  let count := RectangularDyadicPairedTrace.dyadicCount mesh.depth
  let length := Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward
    (transport.parameters 0) (transport.parameters (Fin.last count))
  have lengthBound := Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters.trace_length_bound transport
    rangeCertificate.property.1
  exact paid outer crossing.index located.piece length lengthBound

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Separate retained-side area and total errors with exact junction-count factors and maximum piece rates.

The same original cache supplies physical increments, while the retained source list and its magnitude enter the
paired-area comparison formula. -/
@[expose] def RetainedExteriorSideEstimate
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (standardDifferential second) requested minimum)
    (outer : Fin
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences.length)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index)
      (allowance tolerance : Fraction.Rational) : Prop :=
  let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
  let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences outer
  let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
    occurrence.sideOccurrence.sheet).meshes.entries.get
    occurrence.sideOccurrence.position
  let side := occurrence.sideOccurrence.side
  let samples := ((prepared.traces.samples cache first second).samples.get occurrence.sideOccurrence.position).get
    occurrence.sideOccurrence.sheet
  let rates := fun i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh
    side + 1) =>
    retainedExteriorPieceRates prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i) index allowance
        tolerance
  let pieces := List.ofFn (fun i => (rates i).1)
  let source := fun i => (rates i).2
  let areaError := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum Prod.fst pieces
  let totalError := max tolerance (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum Prod.snd pieces)
  Data.Gaussian.Norm.Basic.normSq (Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea samples side -
    PairedIncrementArea.area (List.ofFn source).flatten) ≤
    2 * (((2 * Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side + 1 : Nat)
      : Fraction.Rational)^2 * areaError +
      16 * ((2 * Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side + 1 :
        Nat) : Fraction.Rational)^4 * totalError * (2 * (comparison.sourceMagnitude + totalError))) ∧
  Bounded ((PairedIncrementArea.total (Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece.blocks
    samples side).flatten).sub
    (PairedIncrementArea.total (List.ofFn source).flatten))
    (((2 * Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side + 1 : Nat) :
      Fraction.Rational)^2 * totalError)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Paths in
/-- Later paired-owner readings satisfy the retained side's area and total comparison estimates.

A length-error budget and the original physical mesh identify every fragment and junction, preserving their distinct
errors and exact count factors. -/
@[expose] def RetainedExteriorSideBound
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length),
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length),
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let position := occurrence.sideOccurrence.position
    let sheet := occurrence.sideOccurrence.sheet
    let side := occurrence.sideOccurrence.side
    let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get sheet).meshes.entries.get position
    ∀ {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index),
    let samples := ((prepared.traces.samples cache first second).samples.get position).get sheet
    ∀ {allowance : Fraction.Rational}
      (budget : NoisyPathArea.LengthErrorBudget
        (RectangularDyadicPairedTrace.dyadicCount mesh.depth) allowance)
      (owners : Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence
        (standardDifferential second) budget.tolerance) (_later : owners.index ≤ index),
    let rates := fun i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh
      side + 1) =>
      retainedExteriorPieceRates prepared componentIndex comparison outer
        (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i) index allowance
          budget.tolerance
    let pieces := List.ofFn (fun i => (rates i).1)
    let source := fun i => (rates i).2
    let areaError := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum Prod.fst pieces
    let totalError := max budget.tolerance
      (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum Prod.snd pieces)
    Data.Gaussian.Norm.Basic.normSq (Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea samples side -
      PairedIncrementArea.area (List.ofFn source).flatten) ≤
      2 * (((2 * Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side + 1 :
        Nat) : Fraction.Rational)^2 * areaError +
        16 * ((2 * Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side + 1 :
          Nat) : Fraction.Rational)^4 * totalError * (2 * (comparison.sourceMagnitude + totalError))) ∧
    Bounded ((PairedIncrementArea.total (Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece.blocks
      samples side).flatten).sub
      (PairedIncrementArea.total (List.ofFn source).flatten))
      (((2 * Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side + 1 : Nat) :
        Fraction.Rational)^2 * totalError)

open Purelib.Data.Rat in
/-- One quarter of a nonnegative rational value is bounded by that value. -/
private theorem quarter_le {value : Fraction.Rational} (nonnegative : 0 ≤ value) : value / 4 ≤ value := by
  apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : Fraction.Rational) < 4)).mpr
  exact (le_add_of_nonneg_right (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative
    (by decide : (0 : Fraction.Rational) ≤ 3))).trans_eq (by ring1)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.RootContinuation in
/-- Assemble retained fragment and junction estimates into the original whole-side comparison.

The exact flattened block-area readback retains the original physical sample owner and source increments, with separate
squared-count total and fourth-power area terms. -/
theorem retained_exterior_side_bound
    (prepared : BoundaryPreparation preparation first second target radius floor) : RetainedExteriorSideBound prepared
      := by
  intro componentIndex component requested minimum comparison outer occurrence position sheet side mesh index cache
    samples allowance
    budget owners later rates pieces source areaError totalError
  have areaNonnegative : 0 ≤ areaError := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _
  have toleranceLe : budget.tolerance ≤ totalError := Fraction.Order.Basic.le_max_left _ _
  have totalNonnegative : 0 ≤ totalError := budget.tolerance_positive.le.trans toleranceLe
  have pieceBounds (i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh
    side + 1)) :
      Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area
        (Perimeter.RetainedIncrements.increments samples side
          (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i)) -
          PairedIncrementArea.area (source i)) ≤ (rates i).1.1 ∧
      Bounded ((PairedIncrementArea.total
        (Perimeter.RetainedIncrements.increments samples side
          (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i))).sub
          (PairedIncrementArea.total (source i))) (rates i).1.2 := by
    have bound := retained_exterior_fragment_bound prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i) cache budget
        owners later
    exact ⟨bound.1, bound.2.1.1⟩
  have areas (i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side +
    1)) :=
    (pieceBounds i).1.trans (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum
      Prod.fst (show (rates i).1 ∈ pieces from Data.List.OfFn.Basic.mem_ofFn.mpr ⟨i, rfl⟩))
  have totals (i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side +
    1)) :
      Bounded ((PairedIncrementArea.total
        (Perimeter.RetainedIncrements.increments samples side
          (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i))).sub
          (PairedIncrementArea.total (source i))) totalError := by
    have upper : (rates i).1.2 ≤ totalError :=
      (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum
        Prod.snd (show (rates i).1 ∈ pieces from Data.List.OfFn.Basic.mem_ofFn.mpr ⟨i, rfl⟩)).trans
          (Fraction.Order.Basic.le_max_right _ _)
    exact ⟨(pieceBounds i).2.1.trans upper, (pieceBounds i).2.2.trans upper⟩
  have sources : ∀ i, Bounded (PairedIncrementArea.total (source i)) comparison.sourceMagnitude := by
    intro i
    have bound := retained_exterior_fragment_bound prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i) cache budget
        owners later
    exact Eq.mpr (congrArg (fun value => Bounded value comparison.sourceMagnitude) bound.2.2)
      (NewtonRetainedExteriorSources.retainedExteriorChord prepared componentIndex comparison outer
        (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i)).bounded
  have estimate := Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece.blocks_comparison samples
    side source
    areaNonnegative totalNonnegative comparison.sourceMagnitude_nonnegative areas totals sources (by
      intro i
      have paid := Meshes.PuncturedGrid.Exterior.JunctionOwnerBounds.SurfaceOccurrence.retained_junction_bound
        occurrence ((prepared.traces.get position).get sheet)
        (cache.normalize.get first) (cache.normalize.get second) samples side i owners later
      have upper := (quarter_le budget.tolerance_positive.le).trans toleranceLe
      exact ⟨paid.1.trans upper, paid.2.trans upper⟩)
  have exactArea := (PairedAreaBlocks.area_flatten
    (Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece.blocks samples side)).trans
    (Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.LiftedPuncturedGrid.CenteredPerimeters.retained_blocks_area
      (prepared.traces.samples cache first second) position sheet side).symm
  exact ⟨(congrArg (fun value => Data.Gaussian.Norm.Basic.normSq (value - PairedIncrementArea.area (List.ofFn
    source).flatten)) exactArea).symm.trans_le estimate.1,
    estimate.2⟩

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.RootContinuation in
open Purelib.Topology.Polygon in
/-- The original component's oriented source-side areas plus the area of their ordered total increments. -/
@[expose] def ComponentSourceArea
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (standardDifferential second) requested minimum) : Basic.Canonical :=
  let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
  let source := fun outer : Fin component.prepared.occurrences.length =>
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let side := occurrence.sideOccurrence.side
    let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
      occurrence.sideOccurrence.sheet).meshes.entries.get
      occurrence.sideOccurrence.position
    (List.ofFn (fun i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh
      side + 1) =>
      (NewtonRetainedExteriorSources.retainedExteriorChord prepared componentIndex comparison outer
        (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side
        i)).increments)).flatten
  let forward := fun outer : Fin component.prepared.occurrences.length =>
    (Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences outer).sourceForward
  let areas := fun outer => if forward outer then PairedIncrementArea.area (source outer)
    else -PairedIncrementArea.area (source outer)
  let totals := fun outer => if forward outer then PairedIncrementArea.total (source outer)
    else Stokes.PrimitivePoint.zero.sub (PairedIncrementArea.total (source outer))
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn areas) + PairedIncrementArea.area (List.ofFn totals)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The retained component's oriented physical-side areas plus the area of their ordered total increments. -/
@[expose] def ComponentPhysicalArea
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index) :
      Basic.Canonical :=
  let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
  let occurrence := fun outer : Fin component.prepared.occurrences.length =>
    Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences outer
  let samples := fun outer => ((prepared.traces.samples cache first second).samples.get
    (occurrence outer).sideOccurrence.position).get (occurrence outer).sideOccurrence.sheet
  let areas := fun outer => if (occurrence outer).sourceForward then
    Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea (samples outer) (occurrence outer).sideOccurrence.side
      else
    -Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea (samples outer) (occurrence outer).sideOccurrence.side
  let totals := fun outer =>
    let value := PairedIncrementArea.total
      (Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece.blocks (samples outer) (occurrence
        outer).sideOccurrence.side).flatten
    if (occurrence outer).sourceForward then value else Stokes.PrimitivePoint.zero.sub value
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn areas) + PairedIncrementArea.area (List.ofFn totals)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Topology.Polygon in
set_option genInjectivity false in
/-- Oriented physical and source readbacks with separate area, total and magnitude estimates.

The record keeps both area values and both paired total values alongside the three distinct rational rates used in
component comparison. -/
structure ExteriorComponentSide where
  /-- The retained oriented physical-side area. -/ physicalArea : Basic.Canonical
  /-- The original oriented source-side area. -/ sourceArea : Basic.Canonical
  /-- The retained oriented physical-side paired total. -/ physicalTotal : Stokes.PrimitivePoint
  /-- The original oriented source-side paired total. -/ sourceTotal : Stokes.PrimitivePoint
  /-- The separate count-weighted squared area-difference rate. -/ areaError : Fraction.Rational
  /-- The separate count-weighted paired-total difference rate. -/ totalError : Fraction.Rational
  /-- The count-weighted source-total magnitude bound. -/ magnitude : Fraction.Rational

constructive_injectivity ExteriorComponentSide

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Read one retained side's exact physical and source data and its count-weighted error rates.

The original occurrence orientation signs both readbacks; retained fragment maxima and junction count determine area
error, total error and source magnitude separately. -/
@[expose] def exteriorComponentSide
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (standardDifferential second) requested minimum)
    (outer : Fin
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences.length)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index)
      (allowance tolerance : Fraction.Rational) : ExteriorComponentSide :=
  let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
  let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences outer
  let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
    occurrence.sideOccurrence.sheet).meshes.entries.get
    occurrence.sideOccurrence.position
  let side := occurrence.sideOccurrence.side
  let samples := ((prepared.traces.samples cache first second).samples.get occurrence.sideOccurrence.position).get
    occurrence.sideOccurrence.sheet
  let rates := fun i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh
    side + 1) =>
    retainedExteriorPieceRates prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i) index allowance
        tolerance
  let pieces := List.ofFn (fun i => (rates i).1)
  let source := (List.ofFn (fun i => (rates i).2)).flatten
  let areaError := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum Prod.fst pieces
  let totalError := max tolerance (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum Prod.snd pieces)
  let count := ((2 * Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side + 1
    : Nat) : Fraction.Rational)
  let physicalTotal := PairedIncrementArea.total
    (Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece.blocks samples side).flatten
  let sourceTotal := PairedIncrementArea.total source
  ⟨if occurrence.sourceForward then Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea samples side else
    -Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea samples side,
    if occurrence.sourceForward then PairedIncrementArea.area source else -PairedIncrementArea.area source,
    if occurrence.sourceForward then physicalTotal else Stokes.PrimitivePoint.zero.sub physicalTotal,
    if occurrence.sourceForward then sourceTotal else Stokes.PrimitivePoint.zero.sub sourceTotal,
    2 * (count^2 * areaError + 16 * count^4 * totalError * (2 * (comparison.sourceMagnitude + totalError))),
    count^2 * totalError,
    ((Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side + 1 : Nat) :
      Fraction.Rational)^2 * comparison.sourceMagnitude⟩

open Purelib.Data.Gaussian in
/-- A common orientation sign preserves the squared area difference. -/
private theorem signed_area_error (forward : Bool) (left right : Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq ((if forward then left else -left) - (if forward then right else -right)) =
      Data.Gaussian.Norm.Basic.normSq (left - right) := by
  cases forward
  · change Data.Gaussian.Norm.Basic.normSq (-left - -right) = _
    rw [show -left - -right = -(left - right) by ring1]
    exact Norm.Basic.normSq_neg _
  · rfl

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Topology.Polygon
/-- A common orientation sign preserves both coordinate bounds of a paired-total difference. -/
private theorem signed_total_error (forward : Bool) {left right : Stokes.PrimitivePoint}
    {bound : Fraction.Rational} (bounded : Bounded (left.sub right) bound) :
    Bounded ((if forward then left else Stokes.PrimitivePoint.zero.sub left).sub
      (if forward then right else Stokes.PrimitivePoint.zero.sub right)) bound := by
  cases forward
  · change Basic.Canonical.normSq ((0 - left.left) - (0 - right.left)) ≤ bound ∧
      Basic.Canonical.normSq ((0 - left.right) - (0 - right.right)) ≤ bound
    rw [show (0 - left.left) - (0 - right.left) = -(left.left - right.left) by ring1,
      show (0 - left.right) - (0 - right.right) = -(left.right - right.right) by ring1,
      Basic.Canonical.normSq_neg, Basic.Canonical.normSq_neg]
    exact bounded
  · exact bounded

/-- A common orientation sign preserves both coordinate bounds of a paired total. -/
private theorem signed_total_bound (forward : Bool) {value : Stokes.PrimitivePoint}
    {bound : Fraction.Rational} (bounded : Bounded value bound) :
    Bounded (if forward then value else Stokes.PrimitivePoint.zero.sub value) bound := by
  cases forward
  · change Basic.Canonical.normSq (0 - value.left) ≤ bound ∧ Basic.Canonical.normSq (0 - value.right) ≤ bound
    simpa only [zero_sub, Basic.Canonical.normSq_neg, -eq_self, -iff_self] using
      (show Basic.Canonical.normSq value.left ≤ bound ∧ Basic.Canonical.normSq value.right ≤ bound from bounded)
  · exact bounded

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained side estimate bounds both signed readback differences and the source total's magnitude. -/
private def ExteriorComponentSideBound
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ componentIndex : Fin prepared.exterior.prepared.components.length,
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      (outer : Fin component.prepared.occurrences.length) {index : Nat} (cache :
        Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index)
      {allowance tolerance : Fraction.Rational},
    RetainedExteriorSideEstimate prepared componentIndex comparison outer cache allowance tolerance →
    let data := exteriorComponentSide prepared componentIndex comparison outer cache allowance tolerance
    Data.Gaussian.Norm.Basic.normSq (data.physicalArea - data.sourceArea) ≤ data.areaError ∧
      Bounded (data.physicalTotal.sub data.sourceTotal) data.totalError ∧ Bounded data.sourceTotal data.magnitude

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.List in
open Purelib.Integration.Path in
open Purelib.Riemann.RootContinuation in
/-- Transport the original retained side estimate to its signed component record. -/
private theorem exteriorComponentSide_bounded
    (prepared : BoundaryPreparation preparation first second target radius floor) : ExteriorComponentSideBound prepared
      := by
  intro componentIndex component requested minimum comparison outer index cache allowance tolerance estimate data
  let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences outer
  let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
    occurrence.sideOccurrence.sheet).meshes.entries.get
    occurrence.sideOccurrence.position
  let side := occurrence.sideOccurrence.side
  let source := fun i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh
    side + 1) =>
    (NewtonRetainedExteriorSources.retainedExteriorChord prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i)).increments
  have sources : ∀ i, Bounded (PairedIncrementArea.total (source i)) comparison.sourceMagnitude := by
    intro i
    let chord := NewtonRetainedExteriorSources.retainedExteriorChord prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i)
    exact Eq.mpr (congrArg (fun value => Bounded value comparison.sourceMagnitude) chord.increments_total) chord.bounded
  have sourceBound := PairedIncrementArea.total_bound comparison.sourceMagnitude_nonnegative
    (values := List.ofFn (fun i => PairedIncrementArea.total (source i)))
    (by intro value member; obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member; exact sources i)
    (count := Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh side + 1) (by
        rw [Data.List.OfFn.Basic.length_ofFn])
  have sourceEq := PairedAreaBlocks.total_flatten (List.ofFn source)
  rw [OfFn.Basic.map_ofFn] at sourceEq
  change PairedIncrementArea.total (List.ofFn source).flatten =
    PairedIncrementArea.total (List.ofFn (fun i => PairedIncrementArea.total (source i))) at sourceEq
  rw [← sourceEq] at sourceBound
  refine ⟨?_, ?_, ?_⟩
  · exact (signed_area_error occurrence.sourceForward _ _).trans_le estimate.1
  · exact signed_total_error occurrence.sourceForward estimate.2
  · exact signed_total_bound occurrence.sourceForward sourceBound

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- The ordered side records read back the exact original component source area. -/
private def ComponentSourceReadback
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (standardDifferential second) requested minimum)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index)
      (allowance tolerance : Fraction.Rational) : Prop :=
    let sides := List.ofFn (fun outer => exteriorComponentSide prepared componentIndex comparison outer cache allowance
      tolerance)
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (sides.map ExteriorComponentSide.sourceArea) +
      PairedIncrementArea.area (sides.map ExteriorComponentSide.sourceTotal) =
      ComponentSourceArea prepared componentIndex comparison

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- The retained side records' source fields equal the original component source-area formula. -/
private theorem component_source_eq
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (standardDifferential second) requested minimum)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index)
      (allowance tolerance : Fraction.Rational) :
    ComponentSourceReadback prepared componentIndex comparison cache allowance tolerance := by
  unfold ComponentSourceReadback ComponentSourceArea
  apply congrArg₂ (fun a b : Basic.Canonical => a + b)
  · apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
    refine OfFn.Basic.map_ofFn.trans ?_
    apply OfFn.Basic.ofFn_congr
    intro outer
    rfl
  · apply congrArg PairedIncrementArea.area
    refine OfFn.Basic.map_ofFn.trans ?_
    apply OfFn.Basic.ofFn_congr
    intro outer
    rfl

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- The ordered side records read back the exact retained component physical area. -/
private def ComponentPhysicalReadback
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (standardDifferential second) requested minimum)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index)
      (allowance tolerance : Fraction.Rational) : Prop :=
    let sides := List.ofFn (fun outer => exteriorComponentSide prepared componentIndex comparison outer cache allowance
      tolerance)
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (sides.map ExteriorComponentSide.physicalArea) +
      PairedIncrementArea.area (sides.map ExteriorComponentSide.physicalTotal) =
      ComponentPhysicalArea prepared componentIndex cache

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- The retained side records' physical fields equal the original component physical-area formula. -/
private theorem component_physical_eq
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (standardDifferential second) requested minimum)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index)
      (allowance tolerance : Fraction.Rational) :
    ComponentPhysicalReadback prepared componentIndex comparison cache allowance tolerance := by
  unfold ComponentPhysicalReadback ComponentPhysicalArea
  apply congrArg₂ (fun a b : Basic.Canonical => a + b)
  · apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
    refine OfFn.Basic.map_ofFn.trans ?_
    apply OfFn.Basic.ofFn_congr
    intro outer
    rfl
  · apply congrArg PairedIncrementArea.area
    refine OfFn.Basic.map_ofFn.trans ?_
    apply OfFn.Basic.ofFn_congr
    intro outer
    rfl

open Purelib.Data.List in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The total of indexed list totals equals the total of their exact ordered flattening. -/
private theorem total_ofFn_flatten {count : Nat}
    (paths : Fin count → List Stokes.PrimitivePoint) :
    PairedIncrementArea.total (List.ofFn (fun i => PairedIncrementArea.total (paths i))) =
      PairedIncrementArea.total (List.ofFn paths).flatten := by
  rw [PairedAreaBlocks.total_flatten, OfFn.Basic.map_ofFn]
  rfl

open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The total of the original component's oriented retained physical-side increments. -/
@[expose] def ComponentPhysicalTotal
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index) :
      Stokes.PrimitivePoint :=
  let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
  PairedIncrementArea.total (List.ofFn (fun outer : Fin component.prepared.occurrences.length =>
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    let samples := ((prepared.traces.samples cache first second).samples.get
      occurrence.sideOccurrence.position).get occurrence.sideOccurrence.sheet
    let value := PairedIncrementArea.total
      (Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece.blocks samples
      occurrence.sideOccurrence.side).flatten
    if occurrence.sourceForward then value else Stokes.PrimitivePoint.zero.sub value))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- The squared retained side count times the maximum original side-total error. -/
@[expose] def ComponentTotalError
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (standardDifferential second) requested minimum)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index)
      (allowance tolerance : Fraction.Rational) : Fraction.Rational :=
  let sides := List.ofFn (fun outer => exteriorComponentSide prepared componentIndex comparison outer cache allowance
    tolerance)
  (sides.length : Fraction.Rational)^2 *
    Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorComponentSide.totalError sides

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.RootContinuation in
open Purelib.Topology.Polygon in
open Purelib.Topology.Surface in
/-- The retained physical component total is bounded by its source target and aggregate total error.

The exact oriented source totals recover the original closed comparison path, preserving its source-total certificate
and the ordered physical readback. -/
theorem retained_exterior_component_total_bound
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (standardDifferential second) requested minimum)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index)
      {allowance tolerance : Fraction.Rational}
    (estimates : ∀ outer, RetainedExteriorSideEstimate prepared componentIndex comparison outer cache allowance
      tolerance) :
    Bounded (ComponentPhysicalTotal prepared componentIndex cache)
      (2 * (requested + ComponentTotalError prepared componentIndex comparison cache allowance tolerance)) := by
  let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
  let sides := List.ofFn (fun outer => exteriorComponentSide prepared componentIndex comparison outer cache allowance
    tolerance)
  let error := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorComponentSide.totalError sides
  let pairs := sides.map (fun side => (side.physicalTotal, side.sourceTotal))
  have bounded : ∀ value ∈ pairs.map (fun pair => pair.1.sub pair.2), Bounded value error := by
    intro value member
    obtain ⟨pair, inPairs, rfl⟩ := Map.mem_map.mp member
    obtain ⟨side, inSides, rfl⟩ := Map.mem_map.mp inPairs
    obtain ⟨outer, equal⟩ := Data.List.OfFn.Basic.mem_ofFn.mp inSides
    have bound := (exteriorComponentSide_bounded prepared componentIndex comparison outer cache (estimates outer)).2.1
    rw [equal] at bound
    have upper := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum ExteriorComponentSide.totalError inSides
    exact ⟨bound.1.trans upper, bound.2.trans upper⟩
  have difference := PairedIncrementArea.total_bound
    (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _) bounded
    (count := sides.length) (by rw [Data.List.Map.length_map, Data.List.Map.length_map])
  rw [PairedIncrementComparison.total_differences] at difference
  have left : pairs.map Prod.fst = sides.map ExteriorComponentSide.physicalTotal := by rw [Data.List.Map.map_map]; rfl
  have right : pairs.map Prod.snd = sides.map ExteriorComponentSide.sourceTotal := by rw [Data.List.Map.map_map]; rfl
  rw [left, right] at difference
  have physical : PairedIncrementArea.total (sides.map ExteriorComponentSide.physicalTotal) =
      ComponentPhysicalTotal prepared componentIndex cache := by
    rw [OfFn.Basic.map_ofFn]
    rfl
  have sourceEntries : sides.map ExteriorComponentSide.sourceTotal =
      List.ofFn (fun outer => PairedIncrementArea.total (comparison.sourceOccurrenceBlocks outer true).flatten) := by
    rw [OfFn.Basic.map_ofFn]
    apply OfFn.Basic.ofFn_congr
    intro outer
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    have equal := comparison.source_total_ofFn outer occurrence.sourceForward
      (NewtonRetainedExteriorSources.retainedExteriorSourceGrouping prepared componentIndex comparison outer)
      (NewtonRetainedExteriorSources.retained_exterior_run_totals prepared componentIndex comparison outer)
    exact (congrArg (fun value => if occurrence.sourceForward then value else Stokes.PrimitivePoint.zero.sub value)
      equal).trans (comparison.sourceOccurrenceBlocks_total_orientation outer occurrence.sourceForward)
  have source : PairedIncrementArea.total (sides.map ExteriorComponentSide.sourceTotal) = comparison.path.totalValue :=
    by
    exact (congrArg PairedIncrementArea.total sourceEntries).trans
      ((total_ofFn_flatten (fun outer => (comparison.sourceOccurrenceBlocks outer true).flatten)).trans
        ((congrArg PairedIncrementArea.total comparison.sourceOccurrencePaths_partition).trans
          comparison.path.total_eq.symm))
  rw [physical, source] at difference
  exact Boundary.HandleAreaBounds.PrimitivePoint.perturbation_bounded comparison.source_total_bounded difference

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- The component area-comparison rate from separate retained side-area, total and magnitude maxima.

The formula preserves the squared and fourth-power side-count factors and the original paired-total perturbation term.
-/
@[expose] def ComponentComparisonError
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (standardDifferential second) requested minimum)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index)
      (allowance tolerance : Fraction.Rational) : Fraction.Rational :=
  let sides := List.ofFn (fun outer => exteriorComponentSide prepared componentIndex comparison outer cache allowance
    tolerance)
  let areaError := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorComponentSide.areaError sides
  let totalError := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorComponentSide.totalError sides
  let magnitude := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorComponentSide.magnitude sides
  2 * ((sides.length : Fraction.Rational)^2 * areaError +
    16 * (sides.length : Fraction.Rational)^4 * totalError * (2 * (magnitude + totalError)))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained physical-versus-source component area meets its exact aggregate comparison rate. -/
@[expose] def RetainedExteriorComponentEstimate
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (standardDifferential second) requested minimum)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index)
      (allowance tolerance : Fraction.Rational) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (ComponentPhysicalArea prepared componentIndex cache - ComponentSourceArea prepared
    componentIndex comparison) ≤
    ComponentComparisonError prepared componentIndex comparison cache allowance tolerance

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Topology.Surface in
/-- Combine the original retained side estimates into the component area-comparison bound.

Separate finite-sum area errors and paired-total area perturbations preserve the original side ordering and their
distinct count factors. -/
theorem retained_exterior_component_bound
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (standardDifferential second) requested minimum)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index)
      {allowance tolerance : Fraction.Rational}
    (estimates : ∀ outer, RetainedExteriorSideEstimate prepared componentIndex comparison outer cache allowance
      tolerance) :
    RetainedExteriorComponentEstimate prepared componentIndex comparison cache allowance tolerance := by
  unfold RetainedExteriorComponentEstimate
  rw [← component_physical_eq prepared componentIndex comparison cache allowance tolerance,
    ← component_source_eq prepared componentIndex comparison cache allowance tolerance]
  let sides := List.ofFn (fun outer => exteriorComponentSide prepared componentIndex comparison outer cache allowance
    tolerance)
  let areaError := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorComponentSide.areaError sides
  let totalError := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorComponentSide.totalError sides
  let magnitude := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorComponentSide.magnitude sides
  have each (data : ExteriorComponentSide) (member : data ∈ sides) :
      Data.Gaussian.Norm.Basic.normSq (data.physicalArea - data.sourceArea) ≤ areaError ∧
      Bounded (data.physicalTotal.sub data.sourceTotal) totalError ∧ Bounded data.sourceTotal magnitude := by
    obtain ⟨outer, equal⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    have localBound := exteriorComponentSide_bounded prepared componentIndex comparison outer cache (estimates outer)
    rw [equal] at localBound
    have areaLe := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum ExteriorComponentSide.areaError member
    have totalLe := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum ExteriorComponentSide.totalError
      member
    have magnitudeLe := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum ExteriorComponentSide.magnitude
      member
    exact ⟨localBound.1.trans areaLe, ⟨localBound.2.1.1.trans totalLe, localBound.2.1.2.trans totalLe⟩,
      ⟨localBound.2.2.1.trans magnitudeLe, localBound.2.2.2.trans magnitudeLe⟩⟩
  have totalNonnegative : 0 ≤ totalError := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _
  have magnitudeNonnegative : 0 ≤ magnitude := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _
    _
  let bound := 2 * (magnitude + totalError)
  have boundNonnegative : 0 ≤ bound := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg magnitudeNonnegative totalNonnegative)
  have magnitudeLe : magnitude ≤ bound :=
    (le_add_of_nonneg_right totalNonnegative).trans
      ((le_add_of_nonneg_right (add_nonneg magnitudeNonnegative totalNonnegative)).trans_eq (by
        dsimp only [bound, -eq_self, -iff_self]; ring1))
  have areas := Norm.Sum.Bounds.normSq_sum_le
    (sides.map (fun data => data.physicalArea - data.sourceArea)) areaError (by
      intro value member; obtain ⟨data, present, rfl⟩ := Map.mem_map.mp member; exact (each data present).1)
  have totals := PairedIncrementComparison.area_difference_bound
    (sides.map (fun data => (data.physicalTotal, data.sourceTotal))) totalNonnegative boundNonnegative
    (by intro pair member; obtain ⟨data, present, rfl⟩ := Map.mem_map.mp member; exact (each data present).2.1)
    (by intro pair member; obtain ⟨data, present, rfl⟩ := Map.mem_map.mp member
        exact Boundary.HandleAreaBounds.PrimitivePoint.perturbation_bounded (each data present).2.2 (each data
          present).2.1)
    (by intro pair member; obtain ⟨data, present, rfl⟩ := Map.mem_map.mp member
        exact ⟨(each data present).2.2.1.trans magnitudeLe, (each data present).2.2.2.trans magnitudeLe⟩)
  simp only [Data.List.Map.map_map, Data.List.Map.length_map, -eq_self, -iff_self] at totals
  dsimp only [Function.comp_def] at totals
  rw [Data.List.Map.length_map] at areas
  have difference : Data.Gaussian.Norm.Sum.Basic.gaussianSum (sides.map (fun data => data.physicalArea -
    data.sourceArea)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (sides.map ExteriorComponentSide.physicalArea) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (sides.map ExteriorComponentSide.sourceArea) := by
    clear each estimates
    induction sides with
    | nil => change (0 : Basic.Canonical) = 0 - 0; ring1
    | cons data tail ih => change (_ - _) + _ = (_ + _) - (_ + _); rw [ih]; ring1
  rw [difference] at areas
  have areaBound := areas.trans_eq (show (sides.length : Fraction.Rational) * ((sides.length : Fraction.Rational) *
    areaError) =
    (sides.length : Fraction.Rational)^2 * areaError by ring1)
  have rearrange (a b c d : Basic.Canonical) : (a + b) - (c + d) = (a - c) + (b - d) := by ring1
  change Data.Gaussian.Norm.Basic.normSq ((_ + _) - (_ + _)) ≤ _
  rw [rearrange]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct areaBound totals) (by decide))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Bound the retained physical component area by its comparison error and supplied original source bound. -/
theorem retained_exterior_component_physical_bound
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (standardDifferential second) requested minimum)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index)
      {allowance tolerance sourceBound : Fraction.Rational}
    (estimate : RetainedExteriorComponentEstimate prepared componentIndex comparison cache allowance tolerance)
    (source : Data.Gaussian.Norm.Basic.normSq (ComponentSourceArea prepared componentIndex comparison) ≤ sourceBound) :
    Data.Gaussian.Norm.Basic.normSq (ComponentPhysicalArea prepared componentIndex cache) ≤
      2 * (ComponentComparisonError prepared componentIndex comparison cache allowance tolerance + sourceBound) := by
  have bounded := (Norm.Bounds.normSq_add_le_two
    (ComponentPhysicalArea prepared componentIndex cache - ComponentSourceArea prepared componentIndex comparison)
    (ComponentSourceArea prepared componentIndex comparison)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct estimate source) (by decide))
  rw [sub_add_cancel] at bounded
  exact bounded

open Purelib.Data.Rat in
/-- The paired-area rate increases with its area, total and source bounds under the stated nonnegativity conditions. -/
private theorem rate_mono (count : Nat) {a A t T s S : Fraction.Rational}
    (areaLe : a ≤ A) (totalLe : t ≤ T) (sourceLe : s ≤ S)
    (totalNonnegative : 0 ≤ t) (upperNonnegative : 0 ≤ T) (sourceNonnegative : 0 ≤ s) :
    2 * ((count : Fraction.Rational)^2 * a + 16 * (count : Fraction.Rational)^4 * t * (2 * (s + t))) ≤
      2 * ((count : Fraction.Rational)^2 * A + 16 * (count : Fraction.Rational)^4 * T * (2 * (S + T))) := by
  have factor := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 16)
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4)
  have totals := Fraction.Order.Arithmetic.mul_le_mul_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totalLe factor)
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct sourceLe totalLe) (by decide : (0 : Fraction.Rational) ≤ 2))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 2) (add_nonneg sourceNonnegative
      totalNonnegative))
    (Fraction.Order.Arithmetic.mul_nonneg_direct factor upperNonnegative)
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct areaLe (Fraction.Order.Arithmetic.sq_nonneg_direct _))
        totals)
    (by decide)

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Rat
/-- A nonnegative common bound controls the finite retained maximum, including the empty list. -/
private theorem maximum_bound {Item : Type} (value : Item → Fraction.Rational) (items : List Item)
    {bound : Fraction.Rational} (nonnegative : 0 ≤ bound) (bounded : ∀ item ∈ items, value item ≤ bound) :
    Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum value items ≤ bound := by
  induction items with
  | nil => exact nonnegative
  | cons first rest ih =>
      exact Fraction.Order.Basic.max_le (bounded first List.mem_cons_self)
        (ih (fun item member => bounded item (List.mem_cons_of_mem _ member)))

/-- The original component's retained source magnitude is bounded by its parent preparation slope. -/
theorem component_source_magnitude_le_slope
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (standardDifferential second) requested minimum) :
    comparison.sourceMagnitude ≤ comparison.original.slope := by
  apply maximum_bound _ _ comparison.original.slope_nonnegative
  intro value member
  obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
  have bound := comparison.original.plan_bounds
    (Charts.Reciprocal.Disk.PairedParentCharts.ChartParent comparison.original i) (List.getElem_mem i.isLt)
  exact Fraction.Order.Basic.max_le bound.1 bound.2

end

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Separate count-based area, total and source-magnitude caps for one original exterior side. -/
structure ExteriorCountSide where
  /-- The separate count-weighted squared area-difference rate. -/ areaError : Fraction.Rational
  /-- The separate count-weighted paired-total difference rate. -/ totalError : Fraction.Rational
  /-- The count-weighted source-total magnitude bound. -/ magnitude : Fraction.Rational

constructive_injectivity ExteriorCountSide

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Rat
/-- Compute side caps from the original junction count and supplied area, total and magnitude targets. -/
@[expose] def exteriorCountSide
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    (sourceMagnitude : Fraction.Rational)
    (outer : Fin
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences.length)
    (areaTarget totalTarget : Fraction.Rational) : ExteriorCountSide :=
  let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
    (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences outer
  let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
    occurrence.sideOccurrence.sheet).meshes.entries.get
    occurrence.sideOccurrence.position
  let joins := Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh
    occurrence.sideOccurrence.side
  let count := ((2 * joins + 1 : Nat) : Fraction.Rational)
  ⟨2 * (count^2 * areaTarget + 16 * count^4 * totalTarget * (2 * (sourceMagnitude + totalTarget))),
    count^2 * totalTarget, ((joins + 1 : Nat) : Fraction.Rational)^2 * sourceMagnitude⟩

/-- The original component's aggregate comparison cap computed from retained side counts. -/
@[expose] def ComponentCountError
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    (sourceMagnitude : Fraction.Rational) (areaTarget totalTarget : Fraction.Rational) : Fraction.Rational :=
  let sides := List.ofFn (fun outer => exteriorCountSide prepared componentIndex sourceMagnitude outer areaTarget
    totalTarget)
  let areaError := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorCountSide.areaError sides
  let totalError := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorCountSide.totalError sides
  let magnitude := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorCountSide.magnitude sides
  2 * ((sides.length : Fraction.Rational)^2 * areaError +
    16 * (sides.length : Fraction.Rational)^4 * totalError * (2 * (magnitude + totalError)))

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Refining the original preparation depth preserves each retained side's count-based caps. -/
private theorem exteriorCountSide_atDepth
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    (sourceMagnitude : Fraction.Rational)
    (depth : Nat)
    (outer : Fin
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences.length)
    (areaTarget totalTarget : Fraction.Rational) :
    exteriorCountSide (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared depth) componentIndex
      sourceMagnitude outer areaTarget totalTarget =
      exteriorCountSide prepared componentIndex sourceMagnitude outer areaTarget totalTarget := by
  let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
    (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences outer
  let rate := fun joins : Nat =>
    let count := ((2 * joins + 1 : Nat) : Fraction.Rational)
    (⟨2 * (count^2 * areaTarget + 16 * count^4 * totalTarget * (2 * (sourceMagnitude + totalTarget))),
      count^2 * totalTarget, ((joins + 1 : Nat) : Fraction.Rational)^2 * sourceMagnitude⟩ : ExteriorCountSide)
  exact congrArg rate (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth_junction_count prepared depth
    occurrence.sideOccurrence.sheet
    occurrence.sideOccurrence.position occurrence.sideOccurrence.side)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Refining the original preparation depth preserves the complete component count-error cap. -/
theorem component_count_error_atDepth
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    (sourceMagnitude : Fraction.Rational)
    (depth : Nat) (areaTarget totalTarget : Fraction.Rational) :
    ComponentCountError (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared depth) componentIndex
      sourceMagnitude areaTarget totalTarget =
      ComponentCountError prepared componentIndex sourceMagnitude areaTarget totalTarget := by
  have sides : List.ofFn (fun outer => exteriorCountSide (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth
    prepared depth) componentIndex sourceMagnitude outer areaTarget totalTarget) =
      List.ofFn (fun outer => exteriorCountSide prepared componentIndex sourceMagnitude outer areaTarget totalTarget) :=
    OfFn.Basic.ofFn_congr (fun outer => exteriorCountSide_atDepth prepared componentIndex sourceMagnitude depth outer
      areaTarget totalTarget)
  exact congrArg (fun sides : List ExteriorCountSide =>
    let areaError := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorCountSide.areaError sides
    let totalError := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorCountSide.totalError sides
    let magnitude := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorCountSide.magnitude sides
    2 * ((sides.length : Fraction.Rational)^2 * areaError +
      16 * (sides.length : Fraction.Rational)^4 * totalError * (2 * (magnitude + totalError)))) sides

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Rat
/-- Paid original piece rates and source magnitude bound every retained side by its count-based caps. -/
private def ExteriorSideRatePayment
    (prepared : BoundaryPreparation preparation first second target radius floor) : Prop :=
  ∀ componentIndex : Fin prepared.exterior.prepared.components.length,
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ {requested : Fraction.Rational} {minimum : Nat}
      (comparison : component.prepared.ClosedBoundaryComparison (standardDifferential second) requested minimum)
      {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index)
        {allowance tolerance areaTarget totalTarget sourceMagnitude : Fraction.Rational},
      0 ≤ areaTarget → 0 ≤ totalTarget → tolerance ≤ totalTarget → comparison.sourceMagnitude ≤ sourceMagnitude →
      RetainedExteriorPieceEstimate prepared componentIndex comparison index allowance tolerance areaTarget totalTarget
        →
      ∀ outer : Fin component.prepared.occurrences.length,
        let side := exteriorComponentSide prepared componentIndex comparison outer cache allowance tolerance
        let cap := exteriorCountSide prepared componentIndex sourceMagnitude outer areaTarget totalTarget
        side.areaError ≤ cap.areaError ∧ side.totalError ≤ cap.totalError ∧ side.magnitude ≤ cap.magnitude

/-- Transport the original piece payment through retained side maxima and exact count factors. -/
private theorem exteriorSideRatePayment
    (prepared : BoundaryPreparation preparation first second target radius floor) : ExteriorSideRatePayment prepared :=
      by
  intro componentIndex component requested minimum comparison index cache allowance tolerance areaTarget totalTarget
    sourceMagnitude
    areaNonnegative totalNonnegative toleranceLe sourceLe paid outer data cap
  let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences outer
  let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
    occurrence.sideOccurrence.sheet).meshes.entries.get
    occurrence.sideOccurrence.position
  let side := occurrence.sideOccurrence.side
  let rates := fun i : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh
    side + 1) =>
    retainedExteriorPieceRates prepared componentIndex comparison outer
      (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side i)
      index allowance tolerance
  let pieces := List.ofFn (fun i => (rates i).1)
  have areaLe : Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum Prod.fst pieces ≤ areaTarget :=
    maximum_bound _ _ areaNonnegative (by
      intro value member; obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      exact (paid outer (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side
        i)).1)
  have totalLe : max tolerance (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum Prod.snd pieces) ≤
    totalTarget :=
    Fraction.Order.Basic.max_le toleranceLe (maximum_bound _ _ totalNonnegative (by
      intro value member; obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      exact (paid outer (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.pieceIndex mesh side
        i)).2))
  have currentNonnegative : 0 ≤ max tolerance (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum Prod.snd
    pieces) :=
    (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _).trans
      (Fraction.Order.Basic.le_max_right _ _)
  exact ⟨rate_mono _ areaLe totalLe sourceLe currentNonnegative totalNonnegative comparison.sourceMagnitude_nonnegative,
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totalLe (Fraction.Order.Arithmetic.sq_nonneg_direct _),
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sourceLe (Fraction.Order.Arithmetic.sq_nonneg_direct _)⟩

/-- Paid original piece rates control the retained component comparison error by its count-based cap. -/
theorem component_comparison_error_paid
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (standardDifferential second) requested minimum)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index)
      {allowance tolerance areaTarget totalTarget sourceMagnitude : Fraction.Rational}
    (areaNonnegative : 0 ≤ areaTarget) (totalNonnegative : 0 ≤ totalTarget) (toleranceLe : tolerance ≤ totalTarget)
    (sourceLe : comparison.sourceMagnitude ≤ sourceMagnitude)
    (paid : RetainedExteriorPieceEstimate prepared componentIndex comparison index allowance tolerance areaTarget
      totalTarget) :
    ComponentComparisonError prepared componentIndex comparison cache allowance tolerance ≤
      ComponentCountError prepared componentIndex sourceMagnitude areaTarget totalTarget := by
  let sides := List.ofFn (fun outer => exteriorComponentSide prepared componentIndex comparison outer cache allowance
    tolerance)
  let caps := List.ofFn (fun outer => exteriorCountSide prepared componentIndex sourceMagnitude outer areaTarget
    totalTarget)
  have each := exteriorSideRatePayment prepared componentIndex comparison cache areaNonnegative totalNonnegative
    toleranceLe sourceLe paid
  have areas := maximum_bound ExteriorComponentSide.areaError sides
    (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative ExteriorCountSide.areaError caps) (by
      intro data member; obtain ⟨outer, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      exact (each outer).1.trans (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum
        ExteriorCountSide.areaError (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨outer, rfl⟩)))
  have totals := maximum_bound ExteriorComponentSide.totalError sides
    (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative ExteriorCountSide.totalError caps) (by
      intro data member; obtain ⟨outer, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      exact (each outer).2.1.trans (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum
        ExteriorCountSide.totalError (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨outer, rfl⟩)))
  have magnitudes := maximum_bound ExteriorComponentSide.magnitude sides
    (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative ExteriorCountSide.magnitude caps) (by
      intro data member; obtain ⟨outer, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      exact (each outer).2.2.trans (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum
        ExteriorCountSide.magnitude (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨outer, rfl⟩)))
  have estimate := rate_mono
    (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences.length
    areas totals magnitudes (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _)
    (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _)
    (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _)
  simpa only [ComponentComparisonError, ComponentCountError, Data.List.OfFn.Basic.length_ofFn, -eq_self, -iff_self]
    using estimate

end

open Purelib.Integration.Path.PairedIncrementArea (area) in
open Purelib.Data.Rat in
/-- The count-weighted total term is at most twice the paired-area rate under the four-area target relation. -/
private theorem total_le_twice_area (count : Nat) {area total source : Fraction.Rational}
    (totalNonnegative : 0 ≤ total) (sourceNonnegative : 0 ≤ source) (small : total ≤ 4 * area) :
    (count : Fraction.Rational)^2 * total ≤
      2 * (2 * ((count : Fraction.Rational)^2 * area +
        16 * (count : Fraction.Rational)^4 * total * (2 * (source + total)))) := by
  have extra : 0 ≤ 16 * (count : Fraction.Rational)^4 * total * (2 * (source + total)) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4))
        totalNonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg sourceNonnegative totalNonnegative))
  have first := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small
    (Fraction.Order.Arithmetic.sq_nonneg_direct (count : Fraction.Rational))
  have second := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (le_add_of_nonneg_right (a := (count : Fraction.Rational)^2 * area) extra) (by decide : (0 : Fraction.Rational) ≤ 4)
  exact first.trans ((le_of_eq (by ring1)).trans (second.trans_eq (by ring1)))

open Purelib.Integration.Path.PairedIncrementArea (area) in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- The retained component total error fits the count-based comparison cap when its target is at most four area targets.

Nonnegative area, total and source bounds and the original piece payment keep the component's separate total and area
estimates aligned. -/
theorem component_total_error_paid
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (standardDifferential second) requested minimum)
    {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index)
      {allowance tolerance areaTarget totalTarget sourceMagnitude : Fraction.Rational}
    (areaNonnegative : 0 ≤ areaTarget) (totalNonnegative : 0 ≤ totalTarget) (sourceNonnegative : 0 ≤ sourceMagnitude)
    (toleranceLe : tolerance ≤ totalTarget) (small : totalTarget ≤ 4 * areaTarget)
    (sourceLe : comparison.sourceMagnitude ≤ sourceMagnitude)
    (paid : RetainedExteriorPieceEstimate prepared componentIndex comparison index allowance tolerance areaTarget
      totalTarget) :
    ComponentTotalError prepared componentIndex comparison cache allowance tolerance ≤
      ComponentCountError prepared componentIndex sourceMagnitude areaTarget totalTarget := by
  let sides := List.ofFn (fun outer => exteriorComponentSide prepared componentIndex comparison outer cache allowance
    tolerance)
  let caps := List.ofFn (fun outer => exteriorCountSide prepared componentIndex sourceMagnitude outer areaTarget
    totalTarget)
  let area := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorCountSide.areaError caps
  let total := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorCountSide.totalError caps
  let magnitude := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorCountSide.magnitude caps
  have each := exteriorSideRatePayment prepared componentIndex comparison cache areaNonnegative totalNonnegative
    toleranceLe sourceLe paid
  have areasNonnegative : 0 ≤ area := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _
  have totals := maximum_bound ExteriorComponentSide.totalError sides
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 2) areasNonnegative) (by
      intro data member
      obtain ⟨outer, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      have sideBound : (exteriorCountSide prepared componentIndex sourceMagnitude outer areaTarget
        totalTarget).totalError ≤
          2 * (exteriorCountSide prepared componentIndex sourceMagnitude outer areaTarget totalTarget).areaError :=
        total_le_twice_area _ totalNonnegative sourceNonnegative small
      exact (each outer).2.1.trans (sideBound.trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum ExteriorCountSide.areaError
            (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨outer, rfl⟩)) (by decide))))
  have totalNonnegative : 0 ≤ total := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _
  have magnitudeNonnegative : 0 ≤ magnitude := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _
    _
  let count : Rational :=
    (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences.length
  have extra : 0 ≤ 16 * count^4 * total * (2 * (magnitude + total)) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))
            totalNonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg magnitudeNonnegative totalNonnegative))
  have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totals
    (Fraction.Order.Arithmetic.sq_nonneg_direct count)
  have larger := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (le_add_of_nonneg_right (a := count^2 * area) extra) (by decide : (0 : Fraction.Rational) ≤ 2)
  have result := bound.trans ((le_of_eq (by ring1)).trans larger)
  simpa only [ComponentTotalError, ComponentCountError, Data.List.OfFn.Basic.length_ofFn, -eq_self, -iff_self] using
    result

open Purelib.Integration.Path.PairedIncrementArea (area) in
open Purelib.Data.Rat in
/-- Scaling area and total targets by a factor in the unit interval scales the paired-area rate by at most that factor.
-/
private theorem rate_scale (count : Nat) (scale area total source : Fraction.Rational)
    (nonnegative : 0 ≤ scale) (small : scale ≤ 1) (totalNonnegative : 0 ≤ total) :
    2 * ((count : Fraction.Rational)^2 * (scale * area) +
      16 * (count : Fraction.Rational)^4 * (scale * total) * (2 * (source + scale * total))) ≤
    scale * (2 * ((count : Fraction.Rational)^2 * area +
      16 * (count : Fraction.Rational)^4 * total * (2 * (source + total)))) := by
  have totalLe := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct small totalNonnegative).trans_eq (one_mul
    total)
  have weighted := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (le_refl source) totalLe) (by decide : (0 : Fraction.Rational) ≤ 2))
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 16)
        (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4))
          totalNonnegative)
  have result := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (le_refl ((count : Fraction.Rational)^2 * area)) weighted)
      (by decide : (0 : Fraction.Rational) ≤ 2)) nonnegative
  exact (show 2 * ((count : Fraction.Rational)^2 * (scale * area) +
      16 * (count : Fraction.Rational)^4 * (scale * total) * (2 * (source + scale * total))) =
    scale * (2 * ((count : Fraction.Rational)^2 * area +
      16 * (count : Fraction.Rational)^4 * total * (2 * (source + scale * total)))) by ring1).trans_le result

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Rat
/-- Each retained side cap is controlled by its unit-target cap and the original area scale. -/
private theorem exteriorCountSide_scale
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    (sourceMagnitude : Fraction.Rational)
    (outer : Fin
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences.length)
    (areaTarget totalTarget : Fraction.Rational) (sourceNonnegative : 0 ≤ sourceMagnitude)
    (areaNonnegative : 0 ≤ areaTarget) (small : areaTarget ≤ 1)
    (totalNonnegative : 0 ≤ totalTarget) (totalLe : totalTarget ≤ 4 * areaTarget) :
    let side := exteriorCountSide prepared componentIndex sourceMagnitude outer areaTarget totalTarget
    let unit := exteriorCountSide prepared componentIndex sourceMagnitude outer 1 4
    side.areaError ≤ areaTarget * unit.areaError ∧ side.totalError ≤ areaTarget * unit.totalError ∧ side.magnitude ≤
      unit.magnitude := by
  let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt
    (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences outer
  let mesh := (prepared.paid.cut.exterior.prepared.energy.entries.get
    occurrence.sideOccurrence.sheet).meshes.entries.get
    occurrence.sideOccurrence.position
  let count := 2 * Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh
    occurrence.sideOccurrence.side + 1
  have normalized := rate_mono count (show areaTarget ≤ areaTarget * 1 by rw [mul_one])
    (totalLe.trans_eq (mul_comm _ _)) (le_refl sourceMagnitude) totalNonnegative
    (Fraction.Order.Arithmetic.mul_nonneg_direct areaNonnegative (by decide : (0 : Fraction.Rational) ≤ 4))
      sourceNonnegative
  have areaBound := normalized.trans (rate_scale count areaTarget 1 4 sourceMagnitude areaNonnegative small (by decide))
  have totalBound : (count : Fraction.Rational)^2 * totalTarget ≤ areaTarget * ((count : Fraction.Rational)^2 * 4) :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totalLe (Fraction.Order.Arithmetic.sq_nonneg_direct
      _)).trans_eq (by ring1)
  exact ⟨areaBound, totalBound, le_rfl⟩

/-- The retained component cap is bounded by its unit-target cap times the original area target.

The area scale lies in the unit interval, and the total target is nonnegative and at most four times that scale. -/
theorem component_count_error_scale
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    (sourceMagnitude areaTarget totalTarget : Fraction.Rational) (sourceNonnegative : 0 ≤ sourceMagnitude)
    (areaNonnegative : 0 ≤ areaTarget) (small : areaTarget ≤ 1)
    (totalNonnegative : 0 ≤ totalTarget) (totalLe : totalTarget ≤ 4 * areaTarget) :
    ComponentCountError prepared componentIndex sourceMagnitude areaTarget totalTarget ≤
      areaTarget * ComponentCountError prepared componentIndex sourceMagnitude 1 4 := by
  let sides := List.ofFn (fun outer => exteriorCountSide prepared componentIndex sourceMagnitude outer areaTarget
    totalTarget)
  let units := List.ofFn (fun outer => exteriorCountSide prepared componentIndex sourceMagnitude outer 1 4)
  let unitArea := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorCountSide.areaError units
  let unitTotal := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorCountSide.totalError units
  let unitMagnitude := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum ExteriorCountSide.magnitude units
  have unitAreaNonnegative : 0 ≤ unitArea := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _
  have unitTotalNonnegative : 0 ≤ unitTotal := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _
    _
  have unitMagnitudeNonnegative : 0 ≤ unitMagnitude :=
    Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _
  have each := exteriorCountSide_scale prepared componentIndex sourceMagnitude
    (areaTarget := areaTarget) (totalTarget := totalTarget)
  have areas := maximum_bound ExteriorCountSide.areaError sides
    (Fraction.Order.Arithmetic.mul_nonneg_direct areaNonnegative unitAreaNonnegative) (by
      intro data member; obtain ⟨outer, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      exact (each outer sourceNonnegative areaNonnegative small totalNonnegative totalLe).1.trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum ExteriorCountSide.areaError
            (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨outer, rfl⟩)) areaNonnegative))
  have totals := maximum_bound ExteriorCountSide.totalError sides
    (Fraction.Order.Arithmetic.mul_nonneg_direct areaNonnegative unitTotalNonnegative) (by
      intro data member; obtain ⟨outer, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      exact (each outer sourceNonnegative areaNonnegative small totalNonnegative totalLe).2.1.trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum ExteriorCountSide.totalError
            (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨outer, rfl⟩)) areaNonnegative))
  have magnitudes := maximum_bound ExteriorCountSide.magnitude sides unitMagnitudeNonnegative (by
    intro data member; obtain ⟨outer, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    exact (each outer sourceNonnegative areaNonnegative small totalNonnegative totalLe).2.2.trans
      (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum ExteriorCountSide.magnitude
        (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨outer, rfl⟩)))
  let count :=
    (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.occurrences.length
  have normalized := rate_mono count areas totals magnitudes
    (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct areaNonnegative unitTotalNonnegative)
    (Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _)
  have result := normalized.trans (rate_scale count areaTarget unitArea unitTotal unitMagnitude areaNonnegative small
    unitTotalNonnegative)
  simpa only [ComponentCountError, Data.List.OfFn.Basic.length_ofFn, -eq_self, -iff_self] using result

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The original allocated endpoint request bounds exterior fine remainder minus retained centered side area.

The exact cache stage is later than the request's original endpoint stage, so both readbacks share the same paired
readings. -/
theorem exterior_sides_accurate (prepared : BoundaryPreparation preparation first second target radius floor)
    (exterior :
      Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation regular
      prepared.domains differential)
    {tolerance : Fraction.Rational}
    (allocated :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.SideRemainderRequest
      exterior prepared.paid.cut.fixed first second tolerance)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) (later :
      allocated.endpoints.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (exterior.fineRemainder readings.normalized readings.left readings.right -
      exterior.centeredSideArea (prepared.traces.samples cache first second)) < tolerance :=
  allocated.accurate later (prepared.traces.samples cache first second) readings.normalized readings.left readings.right

open Purelib.Integration.Path.PairedIncrementArea (area) in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- The exact requested source chords and retained physical side blocks satisfy the original exterior tolerance.

The request-chord identity transports the paid side estimate while retaining the actual occurrence word, source edges,
orientations and cached block readbacks. -/
theorem exterior_request_chords_accurate (prepared : BoundaryPreparation preparation first second target radius floor)
    (exterior :
      Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation regular
      prepared.domains differential)
    {other : Differentials.Basic.Differential genus} {next :
      Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation regular
      prepared.domains other}
    {capTarget capArea : Fraction.Rational} {capFloor : Nat}
    (requested : Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request next capTarget capArea
      capFloor)
    {tolerance : Fraction.Rational}
    (allocated :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.SideRemainderRequest
      exterior prepared.paid.cut.fixed first second tolerance)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) (later :
      allocated.endpoints.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (exterior.occurrences.map
        (fun occurrence => Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.occurrenceFineArea
          readings.normalized occurrence.sideOccurrence)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (requested.entries.map
        (fun entry => Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord readings.left
          readings.right entry.occurrence.placement.location.sourceEdge)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (exterior.occurrences.map (fun occurrence =>
        let blocks := Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece.blocks
          (((prepared.traces.samples cache first second).samples.get occurrence.sideOccurrence.position).get
            occurrence.sideOccurrence.sheet)
          occurrence.sideOccurrence.side
        Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
          occurrence.sideOccurrence
          (Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map PairedIncrementArea.area) +
            PairedIncrementArea.area (blocks.map PairedIncrementArea.total))))) < tolerance := by
  have aligned := exterior.fineRemainder_request_chords requested readings.normalized readings.left readings.right
  have cancel (left right : Basic.Canonical) : left = (left + right) - right := by ring1
  have remainder := (cancel _ _).trans (congrArg (fun value => value -
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (requested.entries.map
      (fun entry => Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord
        readings.left readings.right entry.occurrence.placement.location.sourceEdge))) aligned)
  have bounded := (congrArg (fun value => Data.Gaussian.Norm.Basic.normSq (value - exterior.centeredSideArea
    (prepared.traces.samples cache first second))) remainder).symm.trans_lt
      (exterior_sides_accurate prepared exterior allocated readings later)
  exact (congrArg (fun area => Data.Gaussian.Norm.Basic.normSq
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum (exterior.occurrences.map
      (fun occurrence => Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.occurrenceFineArea
        readings.normalized occurrence.sideOccurrence)) -
     Data.Gaussian.Norm.Sum.Basic.gaussianSum (requested.entries.map
      (fun entry => Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord readings.left
        readings.right entry.occurrence.placement.location.sourceEdge)) - area))

      (RetainedSideBlocks.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.centeredSideArea_retained_blocks
      exterior (prepared.traces.samples cache first second))).symm.trans_lt bounded

end Purelib.Riemann.RootContinuation.NewtonRequestedExteriorSides
