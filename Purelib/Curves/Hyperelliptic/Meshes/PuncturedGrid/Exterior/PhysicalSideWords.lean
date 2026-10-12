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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedFragmentChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalFragmentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalFragmentWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalFragmentParameters
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
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
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
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
import Purelib.Riemann.Integration.RectangularClippedCornerGeometry

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedFragmentChains

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedParentOrder

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalFragmentIndices

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalFragmentParameters

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalFragmentWords

open Purelib.Integration.Path

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.RectangularMatchedObservationSides

@[expose] public section

/-! Complete source words for the cached horizontal and vertical side factories. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (AxisSourceBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily (buildHorizontal
  buildVertical)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalFragmentIndices.JoinedFragmentFamily
  (buildHorizontal_parent_owners buildVertical_parent_owners)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalFragmentParameters.JoinedFragmentFamily
  (buildHorizontal_parameter_bounds buildVertical_parameter_bounds)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
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

/-- The actual horizontal side family forms complete forward parameter and parent words.

Original mesh endpoints, consecutive intervals and cached source-parameter readbacks certify exhaustive traversal of the
retained parent bank. -/
theorem buildHorizontal_indexed_words
    {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
    {height : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedHorizontalSide left right leftRow
      rightRow height}
    (trace : side.Trace depth)
    (sources : FragmentFamilies.AxisSourceBank evaluated left false true)
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
    (axis : false = occurrence.sourceVertical) (forward : occurrence.sourceForward = true)
    (start : leftBox.xLower = occurrence.start.re)
    (finish : leftBox.xUpper = occurrence.finish.re) :
    let family := JoinedFragmentFamily.buildHorizontal trace sources sourceFirst sourceLast budget junctionBudget owners
      later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
    let parents := fun i => (sources.get (Fin.cast left.boundaryColumns_eq i)).block.index
    let retained := JoinedFragmentFamily.buildHorizontal_parent_owners trace sources sourceFirst sourceLast budget
      junctionBudget owners later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
    let items := JoinedFragmentFamily.indexedItems family parents retained.1 retained.2
    IndexedOwnedFragment.Word items ∧ IndexedOwnedFragment.ParentWord items := by
  let family := JoinedFragmentFamily.buildHorizontal trace sources sourceFirst sourceLast budget junctionBudget owners
    later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
  have retained := JoinedFragmentFamily.buildHorizontal_parent_owners trace sources sourceFirst sourceLast budget
    junctionBudget owners later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
  have parameters := JoinedFragmentFamily.buildHorizontal_parameter_bounds trace sources sourceFirst sourceLast budget
    junctionBudget owners later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
  exact JoinedFragmentFamily.indexedItems_physical_words family
    (fun i => left.partition.x.intervals[(Fin.cast left.boundaryColumns_eq i).val]'(Fin.cast left.boundaryColumns_eq
      i).isLt)
    (fun i => (sources.get (Fin.cast left.boundaryColumns_eq i)).block) axis forward retained.1 retained.2
    (fun i => (parameters.1 i).2.1) (fun i => (parameters.1 i).2.2.1)
    (fun i vertex => (parameters.2 i).2 vertex)
    (fun i => (left.x_next i).symm) (left.x_first.trans start) (left.x_last.trans finish)

/-- The actual vertical side family forms complete forward parameter and parent words.

Original mesh endpoints, consecutive intervals and cached source-parameter readbacks certify exhaustive traversal of the
retained parent bank. -/
theorem buildVertical_indexed_words
    {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
    {horizontal : InverseRootPolynomial.Coordinate} {side : ObservationMesh.MatchedVerticalSide left right leftColumn
      rightColumn horizontal}
    (trace : side.Trace depth)
    (sources : FragmentFamilies.AxisSourceBank evaluated left true true)
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
    (axis : true = occurrence.sourceVertical) (forward : occurrence.sourceForward = true)
    (start : leftBox.yLower = occurrence.start.im)
    (finish : leftBox.yUpper = occurrence.finish.im) :
    let family := JoinedFragmentFamily.buildVertical trace sources sourceFirst sourceLast budget junctionBudget owners
      later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
    let parents := fun i => (sources.get (Fin.cast left.boundaryRows_eq i)).block.index
    let retained := JoinedFragmentFamily.buildVertical_parent_owners trace sources sourceFirst sourceLast budget
      junctionBudget owners later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
    let items := JoinedFragmentFamily.indexedItems family parents retained.1 retained.2
    IndexedOwnedFragment.Word items ∧ IndexedOwnedFragment.ParentWord items := by
  let family := JoinedFragmentFamily.buildVertical trace sources sourceFirst sourceLast budget junctionBudget owners
    later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
  have retained := JoinedFragmentFamily.buildVertical_parent_owners trace sources sourceFirst sourceLast budget
    junctionBudget owners later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
  have parameters := JoinedFragmentFamily.buildVertical_parameter_bounds trace sources sourceFirst sourceLast budget
    junctionBudget owners later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
  exact JoinedFragmentFamily.indexedItems_physical_words family
    (fun i => left.partition.y.intervals[(Fin.cast left.boundaryRows_eq i).val]'(Fin.cast left.boundaryRows_eq i).isLt)
    (fun i => (sources.get (Fin.cast left.boundaryRows_eq i)).block) axis forward retained.1 retained.2
    (fun i => (parameters.1 i).2.1) (fun i => (parameters.1 i).2.2.1)
    (fun i vertex => (parameters.2 i).2 vertex)
    (fun i => (left.y_next i).symm) (left.y_first.trans start) (left.y_last.trans finish)

end MatchedSides
end JoinedFragmentFamily
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
