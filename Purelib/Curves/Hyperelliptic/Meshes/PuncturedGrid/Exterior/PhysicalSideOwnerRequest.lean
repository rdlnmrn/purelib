module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideOwnerErrors
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Budget.RequestedLengthBudget
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FamilyBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.RectangularMatchedObservationSides

@[expose] public section

/-! Apply automatically selected owner budgets to the retained physical side samples. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideOwnerRequest
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (JoinedFragmentFamily AxisSourceBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily (buildHorizontal
  buildVertical build_property)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest (PhysicalOwnerBudget)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Coordinate} {minimum
    stage fine index : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : PairedSourcePlan occurrence
    other target minimum}

variable {data : FirstData occurrence
  index} {otherData : SecondData
  occurrence other index}

namespace JoinedFragmentFamily
section MatchedSides
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
variable {lc lr rc rr depth : Nat} {lg : Geometry lc lr} {rg :
  Geometry rc rr}
  {leftCuts : GridCuts lg} {rightCuts :
    GridCuts rg} {leftBox rightBox :
    Purelib.Geometry.Rational.Box}
  {left : ObservationMesh leftCuts leftBox} {right :
    ObservationMesh rightCuts rightBox}

open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)

/-- The original constructed horizontal fragment family's error is strictly below the retained owner request target. -/
def horizontalRequestedError
    {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
    {height : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedHorizontalSide left right leftRow
      rightRow height}
    {requested : InverseRootPolynomial.Coordinate}
    (ownerBudget : PhysicalOwnerRequest.PhysicalOwnerBudget plan left.boundaryColumns requested)
    (selected : ownerBudget.Owners (RectangularDyadicPairedTrace.dyadicCount depth)) (later : selected.index ≤ index)
    (prepared : ownerBudget.Prepared)
    {evaluated : PairedSourcePlan.ParentEvaluation prepared.plan sample otherSample fine}
    (trace : side.Trace depth)
    {forward : Bool}
    (sources : FragmentFamilies.AxisSourceBank evaluated left false forward)
    (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height)
    (first : RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (second : RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (leftValues rightValues : side.Vertex depth → InverseRootPolynomial.Gaussian)
    (leftEq : ∀ vertex, first.values vertex = leftValues (trace.vertices.indexed vertex))
    (rightEq : ∀ vertex, second.values vertex = rightValues (trace.vertices.indexed vertex))
    : Prop :=
  (JoinedFragmentFamily.buildHorizontal (evaluated := evaluated) (data := data) (otherData := otherData) trace sources
    sourceFirst sourceLast selected.piece.budget selected.junction.budget selected.owners (selected.owners_le.trans
    later) selected.junctionOwners (selected.junctionOwners_le.trans later) first second leftValues rightValues leftEq
    rightEq).error < requested

/-- The paid original horizontal owner request certifies the actual retained fragment family's requested error.

The source and face stages, original numerical readings and separately budgeted piece and junction tolerances are
preserved. -/
theorem buildHorizontal_error_requested
    {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
    {height : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedHorizontalSide left right leftRow
      rightRow height}
    {requested : InverseRootPolynomial.Coordinate} (positive : 0 < requested)
    (ownerBudget : PhysicalOwnerRequest.PhysicalOwnerBudget plan left.boundaryColumns requested)
    (selected : ownerBudget.Owners (RectangularDyadicPairedTrace.dyadicCount depth)) (later : selected.index ≤ index)
    (prepared : ownerBudget.Prepared)
    {evaluated : PairedSourcePlan.ParentEvaluation prepared.plan sample otherSample fine}
    (trace : side.Trace depth)
    {forward : Bool}
    (sources : FragmentFamilies.AxisSourceBank evaluated left false forward)
    (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height)
    (first : RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (second : RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (leftValues rightValues : side.Vertex depth → InverseRootPolynomial.Gaussian)
    (leftEq : ∀ vertex, first.values vertex = leftValues (trace.vertices.indexed vertex))
    (rightEq : ∀ vertex, second.values vertex = rightValues (trace.vertices.indexed vertex))
    :
      horizontalRequestedError
      ownerBudget selected later prepared trace sources sourceFirst sourceLast first second leftValues rightValues
      leftEq rightEq := by
  apply prepared.error_lt _ positive (selected.face_le.trans later)
  · apply JoinedFragmentFamily.build_property
    · intro i
      exact le_rfl
    · intro i
      exact le_rfl
  · apply JoinedFragmentFamily.build_property
    · intro i
      exact selected.piece.tolerance_le
    · intro i
      exact selected.junction.tolerance_le

/-- The original constructed vertical fragment family's error is strictly below the retained owner request target. -/
def verticalRequestedError
    {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
    {horizontal : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedVerticalSide left right leftColumn
      rightColumn horizontal}
    {requested : InverseRootPolynomial.Coordinate}
    (ownerBudget : PhysicalOwnerRequest.PhysicalOwnerBudget plan left.boundaryRows requested)
    (selected : ownerBudget.Owners (RectangularDyadicPairedTrace.dyadicCount depth)) (later : selected.index ≤ index)
    (prepared : ownerBudget.Prepared)
    {evaluated : PairedSourcePlan.ParentEvaluation prepared.plan sample otherSample fine}
    (trace : side.Trace depth)
    {forward : Bool}
    (sources : FragmentFamilies.AxisSourceBank evaluated left true forward)
    (sourceFirst : occurrence.start.re = horizontal) (sourceLast : occurrence.finish.re = horizontal)
    (first : RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (second : RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (leftValues rightValues : side.Vertex depth → InverseRootPolynomial.Gaussian)
    (leftEq : ∀ vertex, first.values vertex = leftValues (trace.vertices.indexed vertex))
    (rightEq : ∀ vertex, second.values vertex = rightValues (trace.vertices.indexed vertex))
    : Prop :=
  (JoinedFragmentFamily.buildVertical (evaluated := evaluated) (data := data) (otherData := otherData) trace sources
    sourceFirst sourceLast selected.piece.budget selected.junction.budget selected.owners (selected.owners_le.trans
    later) selected.junctionOwners (selected.junctionOwners_le.trans later) first second leftValues rightValues leftEq
    rightEq).error < requested

/-- The paid original vertical owner request certifies the actual retained fragment family's requested error.

The source and face stages, original numerical readings and separately budgeted piece and junction tolerances are
preserved. -/
theorem buildVertical_error_requested
    {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
    {horizontal : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedVerticalSide left right leftColumn
      rightColumn horizontal}
    {requested : InverseRootPolynomial.Coordinate} (positive : 0 < requested)
    (ownerBudget : PhysicalOwnerRequest.PhysicalOwnerBudget plan left.boundaryRows requested)
    (selected : ownerBudget.Owners (RectangularDyadicPairedTrace.dyadicCount depth)) (later : selected.index ≤ index)
    (prepared : ownerBudget.Prepared)
    {evaluated : PairedSourcePlan.ParentEvaluation prepared.plan sample otherSample fine}
    (trace : side.Trace depth)
    {forward : Bool}
    (sources : FragmentFamilies.AxisSourceBank evaluated left true forward)
    (sourceFirst : occurrence.start.re = horizontal) (sourceLast : occurrence.finish.re = horizontal)
    (first : RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (second : RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (leftValues rightValues : side.Vertex depth → InverseRootPolynomial.Gaussian)
    (leftEq : ∀ vertex, first.values vertex = leftValues (trace.vertices.indexed vertex))
    (rightEq : ∀ vertex, second.values vertex = rightValues (trace.vertices.indexed vertex))
    :
      verticalRequestedError
      ownerBudget selected later prepared trace sources sourceFirst sourceLast first second leftValues rightValues
      leftEq rightEq := by
  apply prepared.error_lt _ positive (selected.face_le.trans later)
  · apply JoinedFragmentFamily.build_property
    · intro i
      exact le_rfl
    · intro i
      exact le_rfl
  · apply JoinedFragmentFamily.build_property
    · intro i
      exact selected.piece.tolerance_le
    · intro i
      exact selected.junction.tolerance_le

end MatchedSides
end JoinedFragmentFamily
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideOwnerRequest
