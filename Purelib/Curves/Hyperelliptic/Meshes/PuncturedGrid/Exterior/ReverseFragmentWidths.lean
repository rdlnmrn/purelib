module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Readings.RectangularPointReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalFragmentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSourceWidths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedReverseFamily
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
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
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Polynomial.Rectangle.JoinedSampleBlocks
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
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalFragmentIndices

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSourceWidths.PairedSourcePlan

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Integration.Path

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.RectangularMatchedObservationSides

@[expose] public section

/-! Reversed mesh-width certificates for both cached physical-side factories. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentWidths
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest (OwnerRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (JoinedFragmentFamily AxisSourceBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily (build
  buildHorizontal buildVertical)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily.JoinedFragmentFamily
  (indexedItems)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalFragmentIndices.JoinedFragmentFamily
  (buildHorizontal_parent_owners buildVertical_parent_owners)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains.IndexedOwnedFragment
  (ReverseFineEnough)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior (SourceBlockParameters)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
  (firstParameter lastParameter)
open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSourceWidths.PairedSourcePlan.SourceBlockParameters
  (horizontalParameters_reverse_bounds verticalParameters_reverse_bounds)
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

variable {evaluated :
  ParentEvaluation
  plan sample otherSample fine}
  {data : FirstData occurrence index}
    {otherData : SecondData occurrence
    other index}

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

/-- The original reversed horizontal family retains its source endpoints and descending dyadic step bounds, with
constant parameters on owner junctions. -/
theorem buildHorizontal_reverse_parameter_bounds
    {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
    {height : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedHorizontalSide left right leftRow
      rightRow height}
    (trace : side.Trace depth)
    (sources : FragmentFamilies.AxisSourceBank evaluated left false false)
    (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height)
    {allowance junctionAllowance : InverseRootPolynomial.Coordinate}
    (budget : NoisyPathArea.LengthErrorBudget (RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (junctionBudget : NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
    (owners : PairedOwnerRequest.OwnerRequest occurrence other budget.tolerance) (later : owners.index ≤ index)
    (junctionOwners : PairedOwnerRequest.OwnerRequest occurrence other junctionBudget.tolerance) (junctionLater :
      junctionOwners.index ≤ index)
    (first : RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (second : RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (leftValues rightValues : side.Vertex depth → InverseRootPolynomial.Gaussian)
    (leftEq : ∀ vertex, first.values vertex = leftValues (trace.vertices.indexed vertex))
    (rightEq : ∀ vertex, second.values vertex = rightValues (trace.vertices.indexed vertex)) :
    let family := JoinedFragmentFamily.buildHorizontal trace sources sourceFirst sourceLast budget junctionBudget owners
      later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
    (∀ i : Fin (left.boundaryColumns + 1),
      let source := sources.get (Fin.cast left.boundaryColumns_eq i)
      let fragment := (family.pieces.get i).fragment
      fragment.forward = false ∧ fragment.parameters 0 = SourceBlockParameters.firstParameter source.block ∧
        fragment.parameters (Fin.last fragment.count) = SourceBlockParameters.lastParameter source.block ∧
        ∀ edge : Fin fragment.count,
          fragment.parameters edge.castSucc - fragment.parameters edge.succ ≤ (1 / 2 :
            InverseRootPolynomial.Coordinate) ^ depth) ∧
    (∀ i : Fin left.boundaryColumns,
      let source := sources.get (Fin.cast left.boundaryColumns_eq i.castSucc)
      let fragment := (family.junctions.get i).fragment
      fragment.forward = true ∧ ∀ vertex, fragment.parameters vertex = SourceBlockParameters.lastParameter source.block)
        := by
  constructor
  · intro i
    dsimp only [JoinedFragmentFamily.buildHorizontal, FragmentFamilies.JoinedFragmentFamily.build]
    rw [DependentVector.ofFn_get]
    have bounds := SourceBlockParameters.horizontalParameters_reverse_bounds trace (Fin.cast left.boundaryColumns_eq i)
      (sources.get (Fin.cast left.boundaryColumns_eq i)).block sourceFirst sourceLast
    exact ⟨rfl, bounds.1, bounds.2.1, bounds.2.2⟩
  · intro i
    dsimp only [JoinedFragmentFamily.buildHorizontal, FragmentFamilies.JoinedFragmentFamily.build]
    rw [DependentVector.ofFn_get]
    exact ⟨rfl, fun _ => rfl⟩

/-- The original reversed vertical family retains its source endpoints and descending dyadic step bounds, with constant
parameters on owner junctions. -/
theorem buildVertical_reverse_parameter_bounds
    {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
    {horizontal : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedVerticalSide left right leftColumn
      rightColumn horizontal}
    (trace : side.Trace depth)
    (sources : FragmentFamilies.AxisSourceBank evaluated left true false)
    (sourceFirst : occurrence.start.re = horizontal) (sourceLast : occurrence.finish.re = horizontal)
    {allowance junctionAllowance : InverseRootPolynomial.Coordinate}
    (budget : NoisyPathArea.LengthErrorBudget (RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (junctionBudget : NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
    (owners : PairedOwnerRequest.OwnerRequest occurrence other budget.tolerance) (later : owners.index ≤ index)
    (junctionOwners : PairedOwnerRequest.OwnerRequest occurrence other junctionBudget.tolerance) (junctionLater :
      junctionOwners.index ≤ index)
    (first : RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (second : RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (leftValues rightValues : side.Vertex depth → InverseRootPolynomial.Gaussian)
    (leftEq : ∀ vertex, first.values vertex = leftValues (trace.vertices.indexed vertex))
    (rightEq : ∀ vertex, second.values vertex = rightValues (trace.vertices.indexed vertex)) :
    let family := JoinedFragmentFamily.buildVertical trace sources sourceFirst sourceLast budget junctionBudget owners
      later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
    (∀ i : Fin (left.boundaryRows + 1),
      let source := sources.get (Fin.cast left.boundaryRows_eq i)
      let fragment := (family.pieces.get i).fragment
      fragment.forward = false ∧ fragment.parameters 0 = SourceBlockParameters.firstParameter source.block ∧
        fragment.parameters (Fin.last fragment.count) = SourceBlockParameters.lastParameter source.block ∧
        ∀ edge : Fin fragment.count,
          fragment.parameters edge.castSucc - fragment.parameters edge.succ ≤ (1 / 2 :
            InverseRootPolynomial.Coordinate) ^ depth) ∧
    (∀ i : Fin left.boundaryRows,
      let source := sources.get (Fin.cast left.boundaryRows_eq i.castSucc)
      let fragment := (family.junctions.get i).fragment
      fragment.forward = true ∧ ∀ vertex, fragment.parameters vertex = SourceBlockParameters.lastParameter source.block)
        := by
  constructor
  · intro i
    dsimp only [JoinedFragmentFamily.buildVertical, FragmentFamilies.JoinedFragmentFamily.build]
    rw [DependentVector.ofFn_get]
    have bounds := SourceBlockParameters.verticalParameters_reverse_bounds trace (Fin.cast left.boundaryRows_eq i)
      (sources.get (Fin.cast left.boundaryRows_eq i)).block sourceFirst sourceLast
    exact ⟨rfl, bounds.1, bounds.2.1, bounds.2.2⟩
  · intro i
    dsimp only [JoinedFragmentFamily.buildVertical, FragmentFamilies.JoinedFragmentFamily.build]
    rw [DependentVector.ofFn_get]
    exact ⟨rfl, fun _ => rfl⟩

/-- The actual horizontal trace depth pays every indexed reversed piece and stationary owner junction's source-width
bound. -/
theorem buildHorizontal_reverse_indexed_fine_enough
    {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
    {height : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedHorizontalSide left right leftRow
      rightRow height}
    (trace : side.Trace depth)
    (sources : FragmentFamilies.AxisSourceBank evaluated left false false)
    (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height)
    {allowance junctionAllowance : InverseRootPolynomial.Coordinate}
    (budget : NoisyPathArea.LengthErrorBudget (RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (junctionBudget : NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
    (owners : PairedOwnerRequest.OwnerRequest occurrence other budget.tolerance) (later : owners.index ≤ index)
    (junctionOwners : PairedOwnerRequest.OwnerRequest occurrence other junctionBudget.tolerance) (junctionLater :
      junctionOwners.index ≤ index)
    (first : RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (second : RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (leftValues rightValues : side.Vertex depth → InverseRootPolynomial.Gaussian)
    (leftEq : ∀ vertex, first.values vertex = leftValues (trace.vertices.indexed vertex))
    (rightEq : ∀ vertex, second.values vertex = rightValues (trace.vertices.indexed vertex))
    (width : InverseRootPolynomial.Coordinate) (refined : (1 / 2 : InverseRootPolynomial.Coordinate) ^ depth ≤ width) :
    let family := JoinedFragmentFamily.buildHorizontal trace sources sourceFirst sourceLast budget junctionBudget owners
      later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
    let parents := fun i : Fin (left.boundaryColumns + 1) => (sources.get (Fin.cast left.boundaryColumns_eq
      i)).block.index
    let retained := JoinedFragmentFamily.buildHorizontal_parent_owners trace sources sourceFirst sourceLast budget
      junctionBudget owners later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
    ∀ item ∈ JoinedFragmentFamily.indexedItems family parents retained.1 retained.2,
      IndexedOwnedFragment.ReverseFineEnough item width := by
  intro family parents retained
  have parameters :=
    buildHorizontal_reverse_parameter_bounds
    trace sources sourceFirst sourceLast budget junctionBudget owners later junctionOwners junctionLater first second
    leftValues rightValues leftEq rightEq
  apply family.indexedItems_reverse_fine_enough parents retained.1 retained.2 width
  · intro i
    have bounds := parameters.1 i
    refine ⟨?_, fun edge => (bounds.2.2.2 edge).trans refined⟩
    intro edge
    have ordered := (family.pieces.get i).fragment.ordered edge
    rw [bounds.1] at ordered
    exact ordered
  · intro i
    have bounds := parameters.2 i
    refine ⟨?_, ?_⟩
    · intro edge
      rw [bounds.2 edge.succ, bounds.2 edge.castSucc]
    · intro edge
      rw [bounds.2 edge.succ, bounds.2 edge.castSucc, sub_self]
      exact (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1 / 2)
        depth).trans refined

/-- The actual vertical trace depth pays every indexed reversed piece and stationary owner junction's source-width
bound. -/
theorem buildVertical_reverse_indexed_fine_enough
    {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
    {horizontal : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedVerticalSide left right leftColumn
      rightColumn horizontal}
    (trace : side.Trace depth)
    (sources : FragmentFamilies.AxisSourceBank evaluated left true false)
    (sourceFirst : occurrence.start.re = horizontal) (sourceLast : occurrence.finish.re = horizontal)
    {allowance junctionAllowance : InverseRootPolynomial.Coordinate}
    (budget : NoisyPathArea.LengthErrorBudget (RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (junctionBudget : NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
    (owners : PairedOwnerRequest.OwnerRequest occurrence other budget.tolerance) (later : owners.index ≤ index)
    (junctionOwners : PairedOwnerRequest.OwnerRequest occurrence other junctionBudget.tolerance) (junctionLater :
      junctionOwners.index ≤ index)
    (first : RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (second : RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex => trace.point
      (trace.vertices.indexed vertex)))
    (leftValues rightValues : side.Vertex depth → InverseRootPolynomial.Gaussian)
    (leftEq : ∀ vertex, first.values vertex = leftValues (trace.vertices.indexed vertex))
    (rightEq : ∀ vertex, second.values vertex = rightValues (trace.vertices.indexed vertex))
    (width : InverseRootPolynomial.Coordinate) (refined : (1 / 2 : InverseRootPolynomial.Coordinate) ^ depth ≤ width) :
    let family := JoinedFragmentFamily.buildVertical trace sources sourceFirst sourceLast budget junctionBudget owners
      later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
    let parents := fun i : Fin (left.boundaryRows + 1) => (sources.get (Fin.cast left.boundaryRows_eq i)).block.index
    let retained := JoinedFragmentFamily.buildVertical_parent_owners trace sources sourceFirst sourceLast budget
      junctionBudget owners later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
    ∀ item ∈ JoinedFragmentFamily.indexedItems family parents retained.1 retained.2,
      IndexedOwnedFragment.ReverseFineEnough item width := by
  intro family parents retained
  have parameters :=
    buildVertical_reverse_parameter_bounds
    trace sources sourceFirst sourceLast budget junctionBudget owners later junctionOwners junctionLater first second
    leftValues rightValues leftEq rightEq
  apply family.indexedItems_reverse_fine_enough parents retained.1 retained.2 width
  · intro i
    have bounds := parameters.1 i
    refine ⟨?_, fun edge => (bounds.2.2.2 edge).trans refined⟩
    intro edge
    have ordered := (family.pieces.get i).fragment.ordered edge
    rw [bounds.1] at ordered
    exact ordered
  · intro i
    have bounds := parameters.2 i
    refine ⟨?_, ?_⟩
    · intro edge
      rw [bounds.2 edge.succ, bounds.2 edge.castSucc]
    · intro edge
      rw [bounds.2 edge.succ, bounds.2 edge.castSucc, sub_self]
      exact (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1 / 2)
        depth).trans refined

end MatchedSides
end JoinedFragmentFamily
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentWidths
