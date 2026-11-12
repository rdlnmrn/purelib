module
import Purelib.Data.List.Reverse
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedParentOrder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HorizontalChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseHorizontalChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedPaths
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
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
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

public section

/-! Instantiate both horizontal run orientations in the shared Newton numerical bank. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalRuns

open Purelib.Curves
open Purelib.Geometry
open Purelib.Integration
open Purelib
open Purelib.Riemann

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank (Data values)

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.RectangularInverseModels

section SharedHorizontalRuns
variable (retained : Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {stage depth : Nat}

variable {cuts : Paths.RectangularSegmentSplitting.GridCuts ((domains.get
  (ParentIndices.occurrenceAt prepared.occurrences
  outer).sideOccurrence.position).domain (ParentIndices.occurrenceAt
  prepared.occurrences outer).sideOccurrence.sheet).geometry}
  {meshBox : Rational.Box} {mesh : Meshes.RectangularObservationMesh.ObservationMesh cuts meshBox}
  {firstRow secondRow : Fin mesh.partition.y.intervals.length} {height : InverseRootPolynomial.Coordinate}
  {side : Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide mesh mesh firstRow secondRow
    height}
  (trace : side.Trace depth) (cache : RegularDomainMeshes.RegularMeshes.Numerics
    domains stage)
  (bank : SharedSideBanks.SharedHorizontalBank.Data (occurrence :=
    ParentIndices.occurrenceAt prepared.occurrences outer) trace
    cache)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  (sourceFirst : (ParentIndices.occurrenceAt prepared.occurrences
    outer).start.im = height)
  (sourceLast : (ParentIndices.occurrenceAt prepared.occurrences
    outer).finish.im = height)
  {allowance : InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget
    (Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
  (owners : OwnerRequest
    (ParentIndices.occurrenceAt prepared.occurrences outer)
    budget.tolerance) (later : owners.index ≤ stage)
  {junctionAllowance : InverseRootPolynomial.Coordinate} (junctionBudget :
    Path.NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest
    (ParentIndices.occurrenceAt prepared.occurrences outer)
    junctionBudget.tolerance) (junctionLater : junctionOwners.index ≤ stage)

section Forward
variable (blocks : ParentBank.ParentBlockBank
  (ParentIndices.occurrenceAt prepared.occurrences outer) mesh false
  true)

/-- Reuse the cached Newton readings on every piece and owner junction. -/
@[expose] def forward : List (IndexedFragments.IndexedFragment
  retained inputs outer bank.data coefficients) := by
  let readings : OwnerRequest.OwnedReadings bank.data (fun vertex :
    Fin (trace.vertices.rest.length + 1) =>
    trace.point (trace.vertices.indexed vertex)) := bank.readings
  have same : ∀ (row : Fin genus) (vertex : Fin (trace.vertices.rest.length + 1)), (readings row).values vertex =
      SharedSideBanks.SharedHorizontalBank.values (occurrence :=
        ParentIndices.occurrenceAt prepared.occurrences outer) trace
        cache row (trace.vertices.indexed vertex) := by
    intro row vertex
    exact bank.readback row vertex
  exact HorizontalChains.horizontalItems retained (coefficients :=
    coefficients) inputs outer trace blocks
    sourceFirst sourceLast budget owners later readings
    (SharedSideBanks.SharedHorizontalBank.values (occurrence :=
      ParentIndices.occurrenceAt prepared.occurrences outer) trace
      cache) same
    junctionBudget junctionOwners junctionLater

variable (axis : (ParentIndices.occurrenceAt prepared.occurrences
  outer).sourceVertical = false)
  (orientation : (ParentIndices.occurrenceAt prepared.occurrences
    outer).sourceForward = true)
  (boxEq : meshBox = (base.faces.regulars[(ParentIndices.occurrenceAt prepared.occurrences
    outer).sideOccurrence.position.val]'(ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position.isLt).cell.box)

include axis orientation boxEq

/-- The shared horizontal readings retain the complete forward source word and original parent order. -/
theorem forward_words :
    IndexedFragments.IndexedFragment.Word
      (forward retained
      inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks) ∧
      GroupedParentOrder.IndexedFragment.ParentWord
        (forward retained
        inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks) := by
  exact HorizontalChains.horizontal_words retained (data := bank.data)
    (coefficients := coefficients) inputs outer trace blocks sourceFirst sourceLast
    budget owners later bank.readings
      (SharedSideBanks.SharedHorizontalBank.values trace cache)
      bank.readback
    junctionBudget junctionOwners junctionLater axis orientation boxEq

/-- Source positions remain distinct even when their payloads repeat. -/
@[expose] def forwardOrdered : SourceOrderedRuns.ParentOrderedRuns
  retained inputs outer bank.data coefficients :=
  SourceOrderedRuns.IndexedGrouping.inSourceOrder
    (FragmentGrouping.IndexedGrouping.build
    (forward retained inputs
    outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks))
    (forward_words retained
      inputs outer trace cache bank coefficients sourceFirst sourceLast
      budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).2

/-- Every source-ordered shared horizontal run retains its complete increasing source chain. -/
theorem forward_chains : ∀ run ∈
  (SharedHorizontalRuns.forwardOrdered retained
  inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).runs,
    SourceChains.SourceChain run.fragments 0 1 := by
  intro run member
  exact HorizontalChains.horizontal_source_chains retained (data :=
    bank.data) (coefficients := coefficients) inputs outer trace blocks sourceFirst sourceLast
    budget owners later bank.readings
      (SharedSideBanks.SharedHorizontalBank.values trace cache)
      bank.readback
    junctionBudget junctionOwners junctionLater axis orientation boxEq run
    member

/-- The complete unsampled side bounds each source-ordered run. -/
theorem forward_capacity : ∀ run ∈
  (SharedHorizontalRuns.forwardOrdered retained
  inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).runs,
    run.fragments.length ≤ 2 * mesh.boundaryColumns + 1 := by
  intro run member
  exact HorizontalChains.horizontal_capacity retained (data :=
    bank.data) (coefficients := coefficients) inputs outer trace blocks sourceFirst sourceLast
    budget owners later bank.readings
      (SharedSideBanks.SharedHorizontalBank.values trace cache)
      bank.readback
    junctionBudget junctionOwners junctionLater run member

/-- Each shared forward horizontal run retains the dyadic source-width bound of its original physical depth. -/
theorem forward_widths : ∀ run ∈
  (SharedHorizontalRuns.forwardOrdered retained
  inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).runs,
    PairedFragmentBlocks.maximum
      OwnedFragments.OwnedFragment.sourceWidth run.fragments ≤
      (1 / 2 : InverseRootPolynomial.Coordinate)^depth := by
  intro run member
  exact HorizontalChains.horizontal_widths retained (data :=
    bank.data) (coefficients := coefficients) inputs outer trace blocks sourceFirst sourceLast
    budget owners later bank.readings
      (SharedSideBanks.SharedHorizontalBank.values trace cache)
      bank.readback
    junctionBudget junctionOwners junctionLater run member

/-- The cached weighted side sample supplies the area of the complete path,
including owner junctions and all joins between parent groups. -/
theorem forward_area : Path.PairedIncrementArea.area (List.ofFn
  (forwardOrdered retained
  inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).physical).flatten =
    (SharedSideSamples.SharedHorizontalBank.Data.sample bank
      coefficients).centeredArea := by
  have path := (FragmentGrouping.IndexedGrouping.build
    (forward retained inputs
    outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks))
    |> fun grouped =>
      SourceOrderedPaths.IndexedGrouping.source_order_physical grouped
    (forward_words retained
      inputs outer trace cache bank coefficients sourceFirst sourceLast
      budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).2
  apply (congrArg Path.PairedIncrementArea.area path).trans
  have readback := HorizontalChains.horizontal_grouped_area retained
    (data := bank.data) (coefficients := coefficients) inputs outer trace blocks sourceFirst sourceLast
    budget owners later bank.readings
      (SharedSideBanks.SharedHorizontalBank.values trace cache)
      bank.readback
    junctionBudget junctionOwners junctionLater
      (SharedSideSamples.SharedHorizontalBank.Data.sample bank
      coefficients)
  have grouped := congrArg (fun pairs : List (List Topology.Polygon.Stokes.PrimitivePoint × List
    Topology.Polygon.Stokes.PrimitivePoint) =>
    Path.PairedIncrementArea.area (pairs.map Prod.fst).flatten)
      (FragmentGrouping.IndexedGrouping.build
      (forward retained
      inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks)).pairs_eq
  exact grouped.symm.trans readback

end Forward

section Reverse
variable (blocks : ParentBank.ParentBlockBank
  (ParentIndices.occurrenceAt prepared.occurrences outer) mesh false
  false)

/-- Reuse the cached Newton readings on every piece and owner junction. -/
@[expose] def reverse : List (IndexedFragments.IndexedFragment
  retained inputs outer bank.data coefficients) := by
  let readings : OwnerRequest.OwnedReadings bank.data (fun vertex :
    Fin (trace.vertices.rest.length + 1) =>
    trace.point (trace.vertices.indexed vertex)) := bank.readings
  have same : ∀ (row : Fin genus) (vertex : Fin (trace.vertices.rest.length + 1)), (readings row).values vertex =
      SharedSideBanks.SharedHorizontalBank.values (occurrence :=
        ParentIndices.occurrenceAt prepared.occurrences outer) trace
        cache row (trace.vertices.indexed vertex) := by
    intro row vertex
    exact bank.readback row vertex
  exact ReverseHorizontalChains.horizontalReverseItems retained
    (coefficients := coefficients) inputs outer trace blocks
    sourceFirst sourceLast budget owners later readings
    (SharedSideBanks.SharedHorizontalBank.values (occurrence :=
      ParentIndices.occurrenceAt prepared.occurrences outer) trace
      cache) same
    junctionBudget junctionOwners junctionLater

variable (axis : (ParentIndices.occurrenceAt prepared.occurrences
  outer).sourceVertical = false)
  (orientation : (ParentIndices.occurrenceAt prepared.occurrences
    outer).sourceForward = false)
  (boxEq : meshBox = (base.faces.regulars[(ParentIndices.occurrenceAt prepared.occurrences
    outer).sideOccurrence.position.val]'(ParentIndices.occurrenceAt prepared.occurrences
      outer).sideOccurrence.position.isLt).cell.box)

include axis orientation boxEq

/-- The shared horizontal readings retain the complete descending source word and reverse parent order. -/
theorem reverse_words :
    IndexedFragments.IndexedFragment.ReverseWord
      (reverse retained
      inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks) ∧
      GroupedReverseOrder.IndexedFragment.ReverseParentWord
        (reverse retained
        inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks) := by
  exact ReverseHorizontalChains.horizontal_reverse_words retained
    (data := bank.data) (coefficients := coefficients) inputs outer trace blocks sourceFirst sourceLast
    budget owners later bank.readings
      (SharedSideBanks.SharedHorizontalBank.values trace cache)
      bank.readback
    junctionBudget junctionOwners junctionLater axis orientation boxEq

/-- Source positions remain distinct even when their payloads repeat. -/
@[expose] def reverseOrdered : SourceOrderedRuns.ParentOrderedRuns
  retained inputs outer bank.data coefficients :=
  SourceOrderedRuns.IndexedGrouping.reverseInSourceOrder
    (FragmentGrouping.IndexedGrouping.build
    (reverse retained inputs
    outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks))
    (reverse_words retained
      inputs outer trace cache bank coefficients sourceFirst sourceLast
      budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).2

/-- Every source-ordered shared horizontal run retains its complete descending source chain. -/
theorem reverse_chains : ∀ run ∈
  (SharedHorizontalRuns.reverseOrdered retained
  inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).runs,
    ReverseSourceChains.ReverseSourceChain run.fragments 1 0 := by
  intro run member
  exact ReverseHorizontalChains.horizontal_reverse_source_chains
    retained (data := bank.data) (coefficients := coefficients) inputs outer trace blocks sourceFirst sourceLast
    budget owners later bank.readings
      (SharedSideBanks.SharedHorizontalBank.values trace cache)
      bank.readback
    junctionBudget junctionOwners junctionLater axis orientation boxEq run
    ((Data.List.Reverse.mem_reverse _).mp member)

/-- The complete unsampled side bounds each source-ordered run. -/
theorem reverse_capacity : ∀ run ∈
  (SharedHorizontalRuns.reverseOrdered retained
  inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).runs,
    run.fragments.length ≤ 2 * mesh.boundaryColumns + 1 := by
  intro run member
  exact ReverseHorizontalChains.horizontal_reverse_capacity retained
    (data := bank.data) (coefficients := coefficients) inputs outer trace blocks sourceFirst sourceLast
    budget owners later bank.readings
      (SharedSideBanks.SharedHorizontalBank.values trace cache)
      bank.readback
    junctionBudget junctionOwners junctionLater run ((Data.List.Reverse.mem_reverse _).mp member)

/-- Each shared reversed horizontal run retains the dyadic reverse-width bound of its original physical depth. -/
theorem reverse_widths : ∀ run ∈
  (SharedHorizontalRuns.reverseOrdered retained
  inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).runs,
    PairedFragmentBlocks.maximum
      OwnedFragments.OwnedFragment.reverseSourceWidth run.fragments ≤
      (1 / 2 : InverseRootPolynomial.Coordinate)^depth := by
  intro run member
  exact ReverseHorizontalChains.horizontal_reverse_widths retained
    (data := bank.data) (coefficients := coefficients) inputs outer trace blocks sourceFirst sourceLast
    budget owners later bank.readings
      (SharedSideBanks.SharedHorizontalBank.values trace cache)
      bank.readback
    junctionBudget junctionOwners junctionLater run ((Data.List.Reverse.mem_reverse _).mp member)

/-- The cached weighted side sample supplies the area of the complete path,
including owner junctions and all joins between parent groups. -/
theorem reverse_area : Path.PairedIncrementArea.area (List.ofFn (fun position =>
  Path.PairedAreaReversal.reverseIncrements
  ((reverseOrdered retained
  inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).physical
      position))).flatten =
    -(SharedSideSamples.SharedHorizontalBank.Data.sample bank
      coefficients).centeredArea := by
  have path := (FragmentGrouping.IndexedGrouping.build
    (reverse retained inputs
    outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks))
    |> fun grouped =>
      SourceOrderedPaths.IndexedGrouping.reverse_source_order_physical
      grouped
    (reverse_words retained
      inputs outer trace cache bank coefficients sourceFirst sourceLast
      budget owners later junctionBudget junctionOwners junctionLater blocks axis orientation boxEq).2
  apply (congrArg Path.PairedIncrementArea.area path).trans
  rw [Path.PairedAreaReversal.area_reverseIncrements]
  have readback :=
    ReverseHorizontalChains.horizontal_reverse_grouped_area retained
    (data := bank.data) (coefficients := coefficients) inputs outer trace blocks sourceFirst sourceLast
    budget owners later bank.readings
      (SharedSideBanks.SharedHorizontalBank.values trace cache)
      bank.readback
    junctionBudget junctionOwners junctionLater
      (SharedSideSamples.SharedHorizontalBank.Data.sample bank
      coefficients)
  have grouped := congrArg (fun pairs : List (List Topology.Polygon.Stokes.PrimitivePoint × List
    Topology.Polygon.Stokes.PrimitivePoint) =>
    Path.PairedIncrementArea.area (pairs.map Prod.fst).flatten)
      (FragmentGrouping.IndexedGrouping.build
      (reverse retained
      inputs outer trace cache bank coefficients sourceFirst sourceLast
    budget owners later junctionBudget junctionOwners junctionLater blocks)).pairs_eq
  exact congrArg Neg.neg (grouped.symm.trans readback)

end Reverse

end SharedHorizontalRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedHorizontalRuns
