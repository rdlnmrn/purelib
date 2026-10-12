module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic

import Purelib.Approximation.Budget.SynchronizedSamples
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.NormalFormErrorBounds
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.ChordErrors
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Cut.WordAreaBounds
import Purelib.Topology.Surface.Sewing.CenteredSewnSamples
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.NormalFormCycles
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.NormalFormBudgets
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Budget.WeightedRowBudgets
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.Alternating.Reduction.CycleRows
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Boundary.NormalFormArea
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

public section

/-!
# Actual normal-form handle periods on a single requested surface

The complete path length is proved from the cached chord routes. Every
component is sampled once at a common stage, then cached row coefficients
transport its paid error. Both handle orientations are compared to the
transformed word, with the physical-boundary corrections still explicit.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Polygon.Stokes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest

/-- The combined component comparison charges simplify to ten times the original component allowance. -/
private theorem component_cost (component : Normalization.InverseRootPolynomial.Coordinate) :
    2 * (2 * (component + component) + component) = 10 * component := by ring1

/-- The combined weighted row charges simplify to twenty-two times mass times the original component allowance. -/
private theorem row_cost (mass component : Normalization.InverseRootPolynomial.Coordinate) :
    2 * (mass * (10 * component) + mass * component) = 22 * mass * component := by ring1

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Hyperelliptic.Differentials.Basic.Differential genus}
  {pairing : Topology.Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {wordData : Topology.Surface.Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {routes : Topology.Surface.Sewing.ChordCycleBank wordData}
  {programBank : Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgramBank lifted source routes.cycles}
  {boundary : Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms.LiftedPuncturedGrid.BoundaryProgram lifted source}
    {boundarySegments : Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank boundary.program.period}
  {differential : Fin genus} {comparison :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank.ofSegments boundary.program boundarySegments)
    differential}
  {segments : Data.Vector.DependentVector (fun index =>
    Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (programBank.programs index).period)}
  {contacts : Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch
    pairing
    (Periods.PeriodMatrix.standardDifferential differential) comparison.domains}
  {reference : Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences.BoundaryReference boundary comparison
    contacts.prepared}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord wordData}
  {raw : List (Handle.Basic.PivotIndices wordData.alphabet.count)} {normal : LinearAlgebra.Alternating.NormalForm
    integral.paired
    raw}
  {components : Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples programBank differential}
  {family : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily programBank.programs
    comparison.domains differential}
  {periods : NormalFormPeriods components
    normal} {profile : Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.Profile periods}
  {rowTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate}
  {floors : Data.Vector Nat wordData.alphabet.count} {surfaceFloor : Nat}

/-- A uniform error bound on the actual component readings gives the retained coefficient-mass bound on each original
normal-form row. -/
private theorem sampled_rows_bounded {stage : Nat} {bound : Normalization.InverseRootPolynomial.Coordinate}
    {primitive : Fin lifted.cutPolygon.patch.cut.count → Topology.Polygon.Stokes.PrimitivePoint}
    {values : Data.Vector Topology.Polygon.Stokes.PrimitivePoint wordData.alphabet.count}
    {readings : routes.Sample integral primitive values}
    (rows : Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.Sample periods stage) (cycles :
      Topology.Surface.Sewing.NormalFormCycles normal readings)
    (bounded : ∀ index, Data.Gaussian.Norm.Basic.normSq (((routes.cycles index).increment primitive).right -
      rows.componentValues index) ≤ bound)
    (row : Fin wordData.alphabet.count) :
    Data.Gaussian.Norm.Basic.normSq ((cycles.jumps row).right - rows.rows row) ≤ (profile.rows.coefficients.get
      row).mass * bound := by
  have sameChain : (periods.rows row).period.chain = cycles.chains row := by
    rw [periods.row_chain, cycles.chains_eq, cycles.weights_eq]
  have estimate := Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.Sample.row_comparison rows primitive bounded row
  rw [sameChain, cycles.increment_eq, ← profile.masses_eq] at estimate
  exact estimate

namespace NormalFormRequest

/-- Retain the exact program geometry and ownership propositions behind
compact types, including the dependent constructor in bank agreement. -/
@[expose] def ProgramSegments (programBank : Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgramBank
  lifted source routes.cycles) :=
  Data.Vector.DependentVector (fun index => Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank
    (programBank.programs index).period)

variable {segments :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.ProgramSegments programBank}

/-- The retained original sewn-face sources for each exact cut-cycle program path. -/
@[expose] def ProgramSources (programBank : Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgramBank
  lifted source routes.cycles) :=
  Data.Vector.DependentVector (fun index => Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources
    lifted.cutPolygon.patch.cut
    (programBank.programs index).cycle.path.cutEdges)

/-- Every retained original path-source family has the required positive orientation. -/
@[expose] def SourcesPositive (sources :
  Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.ProgramSources programBank) : Prop :=
  ∀ index, (sources.get index).Positive

/-- Every original cut-cycle program route spine has the required positive orientation. -/
@[expose] def RoutesPositive (programBank : Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgramBank
  lifted source routes.cycles) : Prop :=
  ∀ index, Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.RouteSpine.Positive
    (programBank.programs index).routed.spine

/-- Every primitive family bank is exactly the bank constructed from its retained original program segments. -/
@[expose] def BanksAligned (family : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily
  programBank.programs comparison.domains differential)
    (segments : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.ProgramSegments programBank)
      : Prop :=
  ∀ index, family.banks.get index = Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank.ofSegments
    (programBank.programs index) (segments.get index)

variable {targets : Data.Vector Normalization.InverseRootPolynomial.Coordinate wordData.alphabet.count}
  (allocation : Topology.Surface.Word.NormalFormBudgets.RowAllocation profile.rows
    (Topology.Surface.Cut.WordAreaBounds.CutWordArea.areaWeight reference.bound boundary.count) rowTarget areaTarget)
  (area : Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests.WordAreaBudget family contacts reference
    boundary.count allocation.component allocation.area targets surfaceFloor)
  (movement : Budget.SynchronizedSamples.StageRequest components.streams allocation.component floors)
  (targets_eq : ∀ index, targets index = allocation.component)
  (banks_eq : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.BanksAligned
    family segments)
  {requested : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.PeriodRequest area
    movement.stages}
  {surface : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.SurfaceSample requested} {centered
    : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CenteredSample surface}
  {word : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.WordSample wordData centered}
  {readings : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.ChordSample routes integral word}
  {sampleFloor : Nat}

section
variable {allocation area movement}
/-- The actual original component period samples sharing the same requested surface and one sufficient stage. -/
@[expose] def CommonReadings (components : Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples
  programBank differential)
    (requested : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.PeriodRequest area
      movement.stages) (sampleFloor : Nat) :=
  Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodSamples.CommonSamples components requested sampleFloor
end

variable (common :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.CommonReadings components
  requested sampleFloor)
  (sources : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.ProgramSources
    programBank)
  (positive : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.SourcesPositive
    sources)
  (routedPositive :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.RoutesPositive
    programBank)

section
variable {allocation area movement common}

/-- The original normal-form row sample at the retained common component stage. -/
@[expose] def RowSample (periods :
  NormalFormPeriods components normal)
    (common : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.CommonReadings components
      requested sampleFloor) :=
  Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.Sample periods common.common.stage

/-- The actual cut-cycle increment and original component period reading differ within ten times the retained component
allowance. -/
@[expose] def ComponentAccurate (centered :
  Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CenteredSample surface)
    (common : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.CommonReadings components
      requested sampleFloor)
    (index : Fin wordData.alphabet.count) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (((routes.cycles index).increment centered.energyValues).right -
    common.common.values index) <
    10 * allocation.component

/-- The actual normal-form row jump differs from its original sampled row within the cached coefficient-mass bound. -/
@[expose] def RowsBounded (cycles : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CycleSample
  normal readings)
    (rows : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.RowSample periods common) (row :
      Fin wordData.alphabet.count) : Prop :=
  Data.Gaussian.Norm.Basic.normSq ((cycles.jumps row).right - rows.rows row) ≤
    (profile.rows.coefficients.get row).mass * (10 * allocation.component)

/-- The first original handle period meets its requested comparison to the transformed word coordinate with the original
physical correction subtracted. -/
@[expose] def FirstAccurate (cycles :
  Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CycleSample normal readings) (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.EvaluatedArea normal word)
    (common : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.CommonReadings components
      requested sampleFloor)
    (pair : Handle.Basic.PivotIndices wordData.alphabet.count) : Prop :=
  Data.Gaussian.Norm.Basic.normSq ((periods.first pair).period.approximation.sample common.common.stage -
    ((evaluated.points pair.1).right - (cycles.physical pair.2).right)) < rowTarget

/-- The last original handle period meets its requested comparison to the transformed word coordinate with the original
physical correction added. -/
@[expose] def LastAccurate (cycles : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CycleSample
  normal readings) (evaluated : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.EvaluatedArea
  normal word)
    (common : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.CommonReadings components
      requested sampleFloor)
    (pair : Handle.Basic.PivotIndices wordData.alphabet.count) : Prop :=
  Data.Gaussian.Norm.Basic.normSq ((periods.last pair).period.approximation.sample common.common.stage -
    ((evaluated.points pair.2).right + (cycles.physical pair.1).right)) < rowTarget

end

/-- Actual cut increments and the original period streams are compared on
one common stage, with path, integration and movement errors all paid. -/
theorem component_accurate
    {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
      Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Hyperelliptic.Differentials.Basic.Differential genus}
  {pairing : Topology.Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {wordData : Topology.Surface.Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {routes : Topology.Surface.Sewing.ChordCycleBank wordData}
  {programBank : Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgramBank lifted source routes.cycles}
  {boundary : Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms.LiftedPuncturedGrid.BoundaryProgram lifted source}
    {boundarySegments : Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank boundary.program.period}
  {differential : Fin genus} {comparison :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank.ofSegments boundary.program boundarySegments)
    differential}
  {segments : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.ProgramSegments programBank}
  {contacts : Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch
    pairing
    (Periods.PeriodMatrix.standardDifferential differential) comparison.domains}
  {reference : Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences.BoundaryReference boundary comparison
    contacts.prepared}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord wordData}
  {raw : List (Handle.Basic.PivotIndices wordData.alphabet.count)} {normal : LinearAlgebra.Alternating.NormalForm
    integral.paired
    raw}
  {components : Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples programBank differential}
  {family : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily programBank.programs
    comparison.domains differential}
  {periods : NormalFormPeriods components
    normal} {profile : Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.Profile periods}
  {rowTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate}
  {floors : Data.Vector Nat wordData.alphabet.count} {surfaceFloor : Nat}
  {targets : Data.Vector Normalization.InverseRootPolynomial.Coordinate wordData.alphabet.count}
  (allocation : Topology.Surface.Word.NormalFormBudgets.RowAllocation profile.rows
    (Topology.Surface.Cut.WordAreaBounds.CutWordArea.areaWeight reference.bound boundary.count) rowTarget areaTarget)
  (area : Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests.WordAreaBudget family contacts reference
    boundary.count allocation.component allocation.area targets surfaceFloor)
  (movement : Budget.SynchronizedSamples.StageRequest components.streams allocation.component floors)
  (targets_eq : ∀ index, targets index = allocation.component)
  (banks_eq : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.BanksAligned family segments)
  {requested : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.PeriodRequest area
    movement.stages}
  {surface : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.SurfaceSample requested} {centered
    : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CenteredSample surface}
  {sampleFloor : Nat}
  (common : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.CommonReadings components
    requested sampleFloor)
  (sources : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.ProgramSources programBank)
  (positive : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.SourcesPositive sources)
  (routedPositive : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.RoutesPositive
    programBank)
    (index : Fin wordData.alphabet.count) :
    Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.ComponentAccurate centered common index
      := by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.ComponentAccurate]
  have lengths (next : Fin wordData.alphabet.count) :
      (programBank.programs next).cycle.path.cutEdges.length ≤ boundary.count := by
    rw [programBank.cycles_eq, boundary.count_eq]
    exact Topology.Surface.Cut.ChordErrors.ChordCycleBank.cycle_length_le routes next
  have estimate := common.path_accurate segments (contact := area.word.request) (movement := movement)
    banks_eq surface sources positive routedPositive lengths index
  have cost := (congrArg (fun target : Normalization.InverseRootPolynomial.Coordinate => 2 * (2 * (allocation.component
    + target) + allocation.component))
    (targets_eq index)).trans (Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.component_cost
      allocation.component)
  have actual := congrArg (fun cycle => (cycle.increment centered.energyValues).right) (programBank.cycles_eq index)
  have increment := actual.symm.trans (CenteredSewnSamples.Centered.cycle_increment_right surface.surface centered
    (programBank.programs index).cycle)
  exact (congrArg (fun value => Data.Gaussian.Norm.Basic.normSq (value - common.common.values index))
    increment).trans_lt (estimate.trans_eq cost)

/-- The row cache is exactly a weighted sample of those same original
streams. No comparison premise or second numerical surface is supplied. -/
theorem rows_bounded
    {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
      Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Hyperelliptic.Differentials.Basic.Differential genus}
  {pairing : Topology.Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {wordData : Topology.Surface.Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {routes : Topology.Surface.Sewing.ChordCycleBank wordData}
  {programBank : Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgramBank lifted source routes.cycles}
  {boundary : Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms.LiftedPuncturedGrid.BoundaryProgram lifted source}
    {boundarySegments : Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank boundary.program.period}
  {differential : Fin genus} {comparison :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank.ofSegments boundary.program boundarySegments)
    differential}
  {segments : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.ProgramSegments programBank}
  {contacts : Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch
    pairing
    (Periods.PeriodMatrix.standardDifferential differential) comparison.domains}
  {reference : Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences.BoundaryReference boundary comparison
    contacts.prepared}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord wordData}
  {raw : List (Handle.Basic.PivotIndices wordData.alphabet.count)} {normal : LinearAlgebra.Alternating.NormalForm
    integral.paired
    raw}
  {components : Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples programBank differential}
  {family : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily programBank.programs
    comparison.domains differential}
  {periods : NormalFormPeriods components
    normal} {profile : Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.Profile periods}
  {rowTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate}
  {floors : Data.Vector Nat wordData.alphabet.count} {surfaceFloor : Nat}
  {targets : Data.Vector Normalization.InverseRootPolynomial.Coordinate wordData.alphabet.count}
  (allocation : Topology.Surface.Word.NormalFormBudgets.RowAllocation profile.rows
    (Topology.Surface.Cut.WordAreaBounds.CutWordArea.areaWeight reference.bound boundary.count) rowTarget areaTarget)
  (area : Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests.WordAreaBudget family contacts reference
    boundary.count allocation.component allocation.area targets surfaceFloor)
  (movement : Budget.SynchronizedSamples.StageRequest components.streams allocation.component floors)
  (targets_eq : ∀ index, targets index = allocation.component)
  (banks_eq : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.BanksAligned family segments)
  {requested : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.PeriodRequest area
    movement.stages}
  {surface : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.SurfaceSample requested} {centered
    : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CenteredSample surface}
  {word : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.WordSample wordData centered}
  {readings : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.ChordSample routes integral word}
  {sampleFloor : Nat}
  (common : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.CommonReadings components
    requested sampleFloor)
  (sources : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.ProgramSources programBank)
  (positive : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.SourcesPositive sources)
  (routedPositive : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.RoutesPositive
    programBank)
    (cycles : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CycleSample normal readings)
    (rows : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.RowSample periods common) (row :
      Fin wordData.alphabet.count) :
    Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.RowsBounded cycles rows row := by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.RowsBounded]
  apply Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.sampled_rows_bounded rows cycles ?_ row
  intro index
  have equal := (rows.components_eq index).trans (common.common.values_eq index).symm
  exact (congrArg (fun value => Data.Gaussian.Norm.Basic.normSq (((routes.cycles index).increment
    centered.energyValues).right - value)) equal).le.trans
    (Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.component_accurate allocation area
      movement targets_eq banks_eq (centered := centered) common sources positive routedPositive index).le

/-- Both actual handle periods now have the requested accuracy relative to
the transformed word coordinates, retaining the physical-boundary terms. -/
theorem first_accurate
    {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
      Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Hyperelliptic.Differentials.Basic.Differential genus}
  {pairing : Topology.Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {wordData : Topology.Surface.Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {routes : Topology.Surface.Sewing.ChordCycleBank wordData}
  {programBank : Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgramBank lifted source routes.cycles}
  {boundary : Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms.LiftedPuncturedGrid.BoundaryProgram lifted source}
    {boundarySegments : Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank boundary.program.period}
  {differential : Fin genus} {comparison :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank.ofSegments boundary.program boundarySegments)
    differential}
  {segments : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.ProgramSegments programBank}
  {contacts : Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch
    pairing
    (Periods.PeriodMatrix.standardDifferential differential) comparison.domains}
  {reference : Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences.BoundaryReference boundary comparison
    contacts.prepared}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord wordData}
  {raw : List (Handle.Basic.PivotIndices wordData.alphabet.count)} {normal : LinearAlgebra.Alternating.NormalForm
    integral.paired
    raw}
  {components : Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples programBank differential}
  {family : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily programBank.programs
    comparison.domains differential}
  {periods : NormalFormPeriods components
    normal} {profile : Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.Profile periods}
  {rowTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate}
  {floors : Data.Vector Nat wordData.alphabet.count} {surfaceFloor : Nat}
  {targets : Data.Vector Normalization.InverseRootPolynomial.Coordinate wordData.alphabet.count}
  (allocation : Topology.Surface.Word.NormalFormBudgets.RowAllocation profile.rows
    (Topology.Surface.Cut.WordAreaBounds.CutWordArea.areaWeight reference.bound boundary.count) rowTarget areaTarget)
  (area : Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests.WordAreaBudget family contacts reference
    boundary.count allocation.component allocation.area targets surfaceFloor)
  (movement : Budget.SynchronizedSamples.StageRequest components.streams allocation.component floors)
  (targets_eq : ∀ index, targets index = allocation.component)
  (banks_eq : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.BanksAligned family segments)
  {requested : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.PeriodRequest area
    movement.stages}
  {surface : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.SurfaceSample requested} {centered
    : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CenteredSample surface}
  {word : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.WordSample wordData centered}
  {readings : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.ChordSample routes integral word}
  {sampleFloor : Nat}
  (common : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.CommonReadings components
    requested sampleFloor)
  (sources : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.ProgramSources programBank)
  (positive : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.SourcesPositive sources)
  (routedPositive : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.RoutesPositive
    programBank)
    (word_eq : wordData = (Topology.Surface.Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord pairing)) (cycles :
      Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CycleSample normal readings)
    (rows : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.RowSample periods common)
      (evaluated : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.EvaluatedArea normal word)
    (pair : Handle.Basic.PivotIndices wordData.alphabet.count) (member : pair ∈ raw) :
    Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.FirstAccurate cycles evaluated common
      pair := by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.FirstAccurate]
  have equal := (periods.first_sample pair common.common.stage).trans (congrArg Neg.neg (rows.row_eq_period
    pair.2).symm)
  have estimate := Topology.Surface.Boundary.NormalFormErrorBounds.first_sample_bounded cycles evaluated rows.rows
    (Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.rows_bounded allocation area movement
      targets_eq banks_eq common sources positive routedPositive cycles rows)
    (fun row => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
      (Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.row_errors_bounded allocation area
        word_eq cycles row).2) pair member
  have paid := (estimate.trans_eq (Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.row_cost
    (profile.rows.coefficients.get pair.2).mass allocation.component)).trans_lt
    (allocation.row_charge_lt pair.2)
  exact (congrArg (fun value => Data.Gaussian.Norm.Basic.normSq (value - ((evaluated.points pair.1).right -
    (cycles.physical pair.2).right))) equal).trans_lt paid

/-- The actual last handle period has the requested accuracy against the transformed word coordinate and its retained
physical-boundary correction. -/
theorem last_accurate
    {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
      Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Hyperelliptic.Differentials.Basic.Differential genus}
  {pairing : Topology.Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {wordData : Topology.Surface.Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {routes : Topology.Surface.Sewing.ChordCycleBank wordData}
  {programBank : Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgramBank lifted source routes.cycles}
  {boundary : Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms.LiftedPuncturedGrid.BoundaryProgram lifted source}
    {boundarySegments : Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank boundary.program.period}
  {differential : Fin genus} {comparison :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank.ofSegments boundary.program boundarySegments)
    differential}
  {segments : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.ProgramSegments programBank}
  {contacts : Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch
    pairing
    (Periods.PeriodMatrix.standardDifferential differential) comparison.domains}
  {reference : Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences.BoundaryReference boundary comparison
    contacts.prepared}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord wordData}
  {raw : List (Handle.Basic.PivotIndices wordData.alphabet.count)} {normal : LinearAlgebra.Alternating.NormalForm
    integral.paired
    raw}
  {components : Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples programBank differential}
  {family : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily programBank.programs
    comparison.domains differential}
  {periods : NormalFormPeriods components
    normal} {profile : Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.Profile periods}
  {rowTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate}
  {floors : Data.Vector Nat wordData.alphabet.count} {surfaceFloor : Nat}
  {targets : Data.Vector Normalization.InverseRootPolynomial.Coordinate wordData.alphabet.count}
  (allocation : Topology.Surface.Word.NormalFormBudgets.RowAllocation profile.rows
    (Topology.Surface.Cut.WordAreaBounds.CutWordArea.areaWeight reference.bound boundary.count) rowTarget areaTarget)
  (area : Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests.WordAreaBudget family contacts reference
    boundary.count allocation.component allocation.area targets surfaceFloor)
  (movement : Budget.SynchronizedSamples.StageRequest components.streams allocation.component floors)
  (targets_eq : ∀ index, targets index = allocation.component)
  (banks_eq : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.BanksAligned family segments)
  {requested : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.PeriodRequest area
    movement.stages}
  {surface : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.SurfaceSample requested} {centered
    : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CenteredSample surface}
  {word : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.WordSample wordData centered}
  {readings : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.ChordSample routes integral word}
  {sampleFloor : Nat}
  (common : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.CommonReadings components
    requested sampleFloor)
  (sources : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.ProgramSources programBank)
  (positive : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.SourcesPositive sources)
  (routedPositive : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.RoutesPositive
    programBank)
    (word_eq : wordData = (Topology.Surface.Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord pairing)) (cycles :
      Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CycleSample normal readings)
    (rows : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.RowSample periods common)
      (evaluated : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.EvaluatedArea normal word)
    (pair : Handle.Basic.PivotIndices wordData.alphabet.count) (member : pair ∈ raw) :
    Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.LastAccurate cycles evaluated common pair
      := by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.LastAccurate]
  have equal := (periods.last_sample pair common.common.stage).trans (rows.row_eq_period pair.1).symm
  have estimate := Topology.Surface.Boundary.NormalFormErrorBounds.last_sample_bounded cycles evaluated rows.rows
    (Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.rows_bounded allocation area movement
      targets_eq banks_eq common sources positive routedPositive cycles rows)
    (fun row => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
      (Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.row_errors_bounded allocation area
        word_eq cycles row).2) pair member
  have paid := (estimate.trans_eq (Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.row_cost
    (profile.rows.coefficients.get pair.1).mass allocation.component)).trans_lt
    (allocation.row_charge_lt pair.1)
  exact (congrArg (fun value => Data.Gaussian.Norm.Basic.normSq (value - ((evaluated.points pair.2).right +
    (cycles.physical pair.1).right))) equal).trans_lt paid

end NormalFormRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons
