module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedParentOrder
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JunctionParameterReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalParameterReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalPathReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedCapacity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.NextPieceJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.MeshEndpoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideCertificates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedWidths
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
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
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

public section

/-! Complete forward vertical source chains on the retained canonical side banks. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalChains

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted
    differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable (retained : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  prepared) {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length)
  {lc lr rc rr depth faceIndex : Nat} {lg : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry lc lr} {rg :
    Purelib.Riemann.Normalization.RectangularInverseModels.Geometry rc rr}
  {leftCuts : Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts lg} {rightCuts :
    Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts rg} {leftBox rightBox :
    Purelib.Geometry.Rational.Box}
  {left : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh leftCuts leftBox} {right :
    Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh rightCuts rightBox}
  {data : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) faceIndex}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

section Vertical
variable {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {width : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {side : Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide left right
    leftColumn rightColumn width}
  (trace : side.Trace depth)
  (blocks : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlockBank
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) left true true)
  (sourceFirst : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).start.re = width)
  (sourceLast : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).finish.re = width)

variable {allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} (budget :
  Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget
  (Purelib.Riemann.Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
    (owners : OwnerRequest
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer) budget.tolerance)
    (later : owners.index ≤ faceIndex)
    (original : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data (fun
      vertex => trace.point (trace.vertices.indexed vertex)))
    (values : Fin genus → side.Vertex depth → Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian)
    (readback : ∀ basisRow vertex, (original basisRow).values vertex = values basisRow (trace.vertices.indexed vertex))

variable {junctionAllowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} (junctionBudget :
  Purelib.Integration.Path.NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer) junctionBudget.tolerance)
  (junctionLater : junctionOwners.index ≤ faceIndex)

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Geometry in
open Purelib.Integration in
open Purelib in
open Purelib.Riemann in
/-- Keep the physical pieces and owner junctions on their selected originals. -/
@[expose] def verticalItems :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback.indexedSideFragments
  (fun position => Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ofBlockSample
    (blocks.get (Fin.cast left.boundaryRows_eq position))
    ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.verticalPieces retained (coefficients :=
      coefficients) inputs outer trace blocks sourceFirst sourceLast
      budget owners later original values readback).get position))
  (fun position => Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.ofBlockSample
    (blocks.get (Fin.cast left.boundaryRows_eq position.castSucc))
    ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.verticalJunctions retained (coefficients :=
      coefficients) inputs outer trace blocks sourceFirst sourceLast
      junctionBudget junctionOwners junctionLater original values readback).get position))

local notation "items" => Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalChains.verticalItems
  retained (coefficients := coefficients) inputs outer trace blocks
  sourceFirst sourceLast budget owners later original values readback junctionBudget junctionOwners junctionLater

variable (axis : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
  prepared.occurrences outer).sourceVertical = true)
  (orientation : (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).sourceForward = true)
  (boxEq : leftBox =
    (base.faces.regulars[(Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
    prepared.occurrences outer).sideOccurrence.position.val]'(ParentIndices.occurrenceAt
      prepared.occurrences outer).sideOccurrence.position.isLt).cell.box)

include axis orientation boxEq

section
open Purelib.Algebra
open Purelib.Curves
open Purelib.Geometry
open Purelib.Integration
open Purelib
open Purelib.Riemann
/-- The canonical vertical pieces and their junctions form both a complete source word and the original ordered parent
word. -/
theorem vertical_words : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.Word items ∧
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedParentOrder.IndexedFragment.ParentWord items := by
  have endpoints := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.MeshEndpoints.ParentBlockBank.vertical_endpoints
    blocks axis orientation boxEq
  constructor
  · apply Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideCertificates.indexedSideFragments_word
    · exact (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalParameterReadback.verticalPieces_first retained
        inputs outer trace blocks sourceFirst sourceLast
        budget owners later original values readback 0).trans endpoints.2.1
    · intro position
      exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideJoins.verticalPieces_join_junction retained inputs
        outer trace blocks sourceFirst sourceLast
        budget owners later original values readback position junctionBudget junctionOwners junctionLater
    · intro position
      exact (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.NextPieceJoins.verticalJunctions_handoff retained inputs
        outer trace blocks sourceFirst sourceLast
        budget owners later original values readback position junctionBudget junctionOwners junctionLater axis
          orientation).2
    · exact (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalParameterReadback.verticalPieces_last retained
        inputs outer trace blocks sourceFirst sourceLast
        budget owners later original values readback (Fin.last left.boundaryRows)).trans endpoints.2.2.2
  · apply Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideCertificates.indexedSideFragments_parentWord
    · intro position; rfl
    · exact endpoints.1
    · intro position
      exact (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.NextPieceJoins.verticalJunctions_handoff retained inputs
        outer trace blocks sourceFirst sourceLast
        budget owners later original values readback position junctionBudget junctionOwners junctionLater axis
          orientation).1
    · exact endpoints.2.2.1

/-- Every maximal parent group has its complete increasing source chain;
endpoint and junction certificates are derived from the physical bank. -/
theorem vertical_source_chains :
    ∀ run ∈ (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build items).runs,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain run.fragments 0 1 := by
  apply Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedGrouping.source_chains
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build items)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalChains.vertical_words retained inputs outer trace blocks
      sourceFirst sourceLast budget owners later original values readback
      junctionBudget junctionOwners junctionLater axis orientation boxEq).1
  apply Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideCertificates.indexedSideFragments_increasing
  · intro position
    exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideJoins.verticalPieces_increasing retained inputs outer
      trace blocks sourceFirst sourceLast
      budget owners later original values readback position rfl
  · intro position
    exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SideJoins.verticalJunctions_increasing retained inputs outer
      trace blocks sourceFirst sourceLast
      original values readback position junctionBudget junctionOwners junctionLater

end

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Geometry in
open Purelib.Integration in
open Purelib in
open Purelib.Riemann in
/-- The groups exhaust the exact original parent list, in order and with
its original multiplicity; no equality test on numerical payloads is used. -/
theorem vertical_parent_entries :
    ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build items).runs.map (fun run
      =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.cacheParent
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer)
        run.parent)) =
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).compared.entered.cache.parents :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedParentOrder.IndexedGrouping.parent_entries
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build items)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalChains.vertical_words retained inputs outer trace blocks
      sourceFirst sourceLast budget owners later original values readback
      junctionBudget junctionOwners junctionLater axis orientation boxEq).2

omit axis orientation boxEq in
open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Geometry in
open Purelib.Integration in
open Purelib in
open Purelib.Riemann in
/-- The same certified groups retain the entire physical side area,
including owner junctions and the cross-parent joining polygon. -/
theorem vertical_grouped_area
    (sample : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (⟨sumFin (fun row => coefficients row * values row (trace.vertices.indexed vertex)),
        FiniteSum.Fin.sumFin (fun row => coefficients row * values row (trace.vertices.indexed vertex))⟩ :
          Topology.Polygon.Stokes.PrimitivePoint))) :
    Path.PairedIncrementArea.area
      ((((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build items).runs.map (fun
        run => run.fragments.map
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair)).flatten).map
        Prod.fst).flatten =
      sample.centeredArea := by
  rw [(Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build items).pairs_eq]
  unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalChains.verticalItems
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedSideReadback.indexedSideFragments_pairs]
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalPathReadback.pairedSideBlocks_area
    (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst (⟨sumFin (fun row => coefficients row * values row
      vertex),
      FiniteSum.Fin.sumFin (fun row => coefficients row * values row vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint))
    (fun position => left.partition.y.intervals[(Fin.cast left.boundaryRows_eq position).val]'
      (Fin.cast left.boundaryRows_eq position).isLt)
    (fun position => blocks.get (Fin.cast left.boundaryRows_eq position))
    (side.pieceVertices depth)
    (fun position => (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.verticalPieces retained inputs
      outer trace blocks sourceFirst sourceLast
      budget owners later original values readback).get position)
    (fun position => (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalBanks.verticalJunctions retained inputs
      outer trace blocks sourceFirst sourceLast
      junctionBudget junctionOwners junctionLater original values readback).get position)
    sample trace.vertices_eq

omit axis orientation boxEq in
open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Geometry in
open Purelib.Integration in
open Purelib in
open Purelib.Riemann in
/-- The retained physical dyadic depth bounds every grouped forward run,
including its stationary owner junctions, without reacquiring samples. -/
theorem vertical_widths :
    ∀ run ∈ (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build items).runs,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.sourceWidth run.fragments ≤ (1 /
        2 : Normalization.InverseRootPolynomial.Coordinate)^depth := open Purelib.Data.Rat in by
  apply Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedWidths.IndexedGrouping.width_bound
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build items)
    (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) depth)
  apply Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedWidths.indexedSideFragments_width
  · intro position
    exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalParameterReadback.verticalPieces_sourceWidth
      retained inputs outer trace blocks sourceFirst sourceLast
      budget owners later original values readback position
  · intro position
    exact (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JunctionParameterReadback.verticalJunctions_sourceWidth
      retained inputs outer trace blocks sourceFirst sourceLast
      junctionBudget junctionOwners junctionLater original values readback position).trans
      (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) depth)

omit axis orientation boxEq in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks.ParentBlock in
open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Geometry in
open Purelib.Integration in
open Purelib in
open Purelib.Riemann in
/-- A geometric capacity may be fixed before any physical readings are acquired. -/
theorem vertical_capacity :
    ∀ run ∈ (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build items).runs,
      run.fragments.length ≤ 2 * left.boundaryRows + 1 := by
  intro run member
  exact (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedCapacity.IndexedGrouping.run_length_bound
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping.build items) run
    member).trans_eq
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedCapacity.indexedSideFragments_length _ _)

end Vertical
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalChains
