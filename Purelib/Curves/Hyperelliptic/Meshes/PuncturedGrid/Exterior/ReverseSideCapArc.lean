module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalFragmentIndices
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSideWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentWidths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedReverseCapArc
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
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
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

public section

/-! Compare the actual cached physical side samples to their literal cap arcs. -/
section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedReverseCapArc
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalFragmentIndices
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentWidths
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSideWords
open Purelib.Integration.Path
open Purelib.Riemann.Paths
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.RectangularMatchedObservationSides
open Purelib.Topology.Polygon

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement (sourceRunDensity)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior (SourceRunRefinement)
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
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSideWords.JoinedFragmentFamily
  (buildHorizontal_reverse_indexed_words buildVertical_reverse_indexed_words)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentWidths.JoinedFragmentFamily
  (buildHorizontal_reverse_indexed_fine_enough buildVertical_reverse_indexed_fine_enough)
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

open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSideCapArc.JoinedFragmentFamily

/-- The cached reversed horizontal physical side satisfies the requested conjugated cap-arc area bound.

The comparison retains its reversed sign, literal endpoint chord and exact original parent order, with physical
refinement and source, owner and cap budgets paid separately. -/
theorem buildHorizontal_reverse_conjugate_cap_arc
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
    (axis : false = occurrence.sourceVertical) (backward : occurrence.sourceForward = false)
    (start : leftBox.xLower = occurrence.finish.re)
    (finish : leftBox.xUpper = occurrence.start.re)
    (original : CenteredBilinearPath.Sample (fun vertex => ConjugateIncrementComparison.conjugateFirst
      ⟨leftValues (trace.vertices.indexed vertex), rightValues (trace.vertices.indexed vertex)⟩))
    (capLater : plan.parents.index ≤ stage) {requested : InverseRootPolynomial.Coordinate} {floor : Nat}
    (request : SourceRunRefinement plan.parents.plans.length (SourceRunRefinement.sourceRunDensity
      plan) (requested / 8) floor)
    (physicalRefined : (1 / 2 : InverseRootPolynomial.Coordinate) ^ depth ≤ request.width)
    (sourceRefined : request.depth ≤ plan.parents.depth + fine)
    (ownerPaid : (JoinedFragmentFamily.buildHorizontal trace sources sourceFirst sourceLast budget junctionBudget owners
      later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq).error ≤ requested / 8)
    (capPaid : target ≤ requested / 4) :
    Data.Gaussian.Norm.Basic.normSq (original.centeredArea +
      (Bilinear.arcArea
        (fun point => ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval point,
          otherSample.primitive.value.eval point⟩)
        (occurrence.piece.mesh.depth + (plan.parents.depth + fine)) occurrence.start occurrence.finish -
      Stokes.edgeArea
        (ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.start⁻¹,
          otherSample.primitive.value.eval occurrence.start⁻¹⟩)
        (ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.finish⁻¹,
          otherSample.primitive.value.eval occurrence.finish⁻¹⟩))) < requested := by
  let family := JoinedFragmentFamily.buildHorizontal trace sources sourceFirst sourceLast budget junctionBudget owners
    later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
  let parents := fun i => (sources.get (Fin.cast left.boundaryColumns_eq i)).block.index
  have retained := JoinedFragmentFamily.buildHorizontal_parent_owners trace sources sourceFirst sourceLast budget
    junctionBudget owners later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
  have words := JoinedFragmentFamily.buildHorizontal_reverse_indexed_words trace sources sourceFirst sourceLast budget
    junctionBudget owners later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq axis
    backward start finish
  have widths := JoinedFragmentFamily.buildHorizontal_reverse_indexed_fine_enough trace sources sourceFirst sourceLast
    budget junctionBudget owners later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
    request.width physicalRefined
  exact JoinedFragmentFamily.reverse_conjugate_cap_arc_of_indexed family
    (JoinedFragmentFamily.indexedItems family parents retained.1 retained.2)
    (JoinedFragmentFamily.indexedItems_readback family parents retained.1 retained.2)
    original trace.vertices_eq capLater request words.1 words.2 widths sourceRefined ownerPaid capPaid

/-- The cached reversed vertical physical side satisfies the requested conjugated cap-arc area bound.

The comparison retains its reversed sign, literal endpoint chord and exact original parent order, with physical
refinement and source, owner and cap budgets paid separately. -/
theorem buildVertical_reverse_conjugate_cap_arc
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
    (axis : true = occurrence.sourceVertical) (backward : occurrence.sourceForward = false)
    (start : leftBox.yLower = occurrence.finish.im)
    (finish : leftBox.yUpper = occurrence.start.im)
    (original : CenteredBilinearPath.Sample (fun vertex => ConjugateIncrementComparison.conjugateFirst
      ⟨leftValues (trace.vertices.indexed vertex), rightValues (trace.vertices.indexed vertex)⟩))
    (capLater : plan.parents.index ≤ stage) {requested : InverseRootPolynomial.Coordinate} {floor : Nat}
    (request : SourceRunRefinement plan.parents.plans.length (SourceRunRefinement.sourceRunDensity
      plan) (requested / 8) floor)
    (physicalRefined : (1 / 2 : InverseRootPolynomial.Coordinate) ^ depth ≤ request.width)
    (sourceRefined : request.depth ≤ plan.parents.depth + fine)
    (ownerPaid : (JoinedFragmentFamily.buildVertical trace sources sourceFirst sourceLast budget junctionBudget owners
      later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq).error ≤ requested / 8)
    (capPaid : target ≤ requested / 4) :
    Data.Gaussian.Norm.Basic.normSq (original.centeredArea +
      (Bilinear.arcArea
        (fun point => ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval point,
          otherSample.primitive.value.eval point⟩)
        (occurrence.piece.mesh.depth + (plan.parents.depth + fine)) occurrence.start occurrence.finish -
      Stokes.edgeArea
        (ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.start⁻¹,
          otherSample.primitive.value.eval occurrence.start⁻¹⟩)
        (ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.finish⁻¹,
          otherSample.primitive.value.eval occurrence.finish⁻¹⟩))) < requested := by
  let family := JoinedFragmentFamily.buildVertical trace sources sourceFirst sourceLast budget junctionBudget owners
    later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
  let parents := fun i => (sources.get (Fin.cast left.boundaryRows_eq i)).block.index
  have retained := JoinedFragmentFamily.buildVertical_parent_owners trace sources sourceFirst sourceLast budget
    junctionBudget owners later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
  have words := JoinedFragmentFamily.buildVertical_reverse_indexed_words trace sources sourceFirst sourceLast budget
    junctionBudget owners later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq axis
    backward start finish
  have widths := JoinedFragmentFamily.buildVertical_reverse_indexed_fine_enough trace sources sourceFirst sourceLast
    budget junctionBudget owners later junctionOwners junctionLater first second leftValues rightValues leftEq rightEq
    request.width physicalRefined
  exact JoinedFragmentFamily.reverse_conjugate_cap_arc_of_indexed family
    (JoinedFragmentFamily.indexedItems family parents retained.1 retained.2)
    (JoinedFragmentFamily.indexedItems_readback family parents retained.1 retained.2)
    original trace.vertices_eq capLater request words.1 words.2 widths sourceRefined ownerPaid capPaid

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSideCapArc.JoinedFragmentFamily

end MatchedSides

end
