module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Energy.Polygon
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Boundary.DualCoordinateBounds
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Purelib.Topology.Surface.Boundary.HandleAreaBudgets
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.GeneratorBounds
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.WordAreaBounds
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.NormalFormCycles
import Purelib.Topology.Surface.Word.NormalFormBudgets
import Purelib.Topology.Surface.Word.NormalFormMagnitude
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormMagnitude
public import Purelib.Riemann.Periods.CorrectedPeriodArea
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.Alternating.Reduction.CycleRows
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Boundary.NormalFormArea
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Sewing.CenteredSewnSamples
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Curves.Hyperelliptic.Meshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Topology.Surface

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Integration

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

public section

/-!
# Requested comparison with the actual common-stage period area

All magnitudes are fixed by the coarse boundary reference and the cached
dual-coordinate profile before sampling. The resulting area uses the actual
period rows. Physical row corrections and the complete remaining matrix
stay explicit; neither is asserted to vanish by polynomial refinement.
-/

section

open Purelib.Topology.Polygon.Stokes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (NormalFormPeriods)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Hyperelliptic.Differentials.Basic.Differential genus}
  {pairing : Word.ProjectedEdgePairs.ProjectedEdgePairing lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {wordData : Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {routes : Sewing.ChordCycleBank wordData}
  {programBank : CyclePrograms.CutCycleProgramBank lifted source routes.cycles}
  {boundary : PuncturedGrid.BoundaryPrograms.LiftedPuncturedGrid.BoundaryProgram lifted source}
    {boundarySegments : PuncturedGrid.PeriodSegmentBanks.SegmentBank boundary.program.period}
  {differential : Fin genus} {comparison :
    PeriodPrimitiveComparison.PrimitiveBank
    (FaceBanks.FaceBank.ofSegments boundary.program boundarySegments)
    differential}
  {segments : Vector.DependentVector (fun index =>
    PuncturedGrid.PeriodSegmentBanks.SegmentBank (programBank.programs index).period)}
  {contacts : PuncturedGrid.BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch
    pairing
    (Periods.PeriodMatrix.standardDifferential differential) comparison.domains}
  {reference : PuncturedGrid.BoundaryPrimitiveReferences.BoundaryReference boundary comparison
    contacts.prepared}
  {integral : Cut.IntegralPairing.CutBoundaryWord wordData}
  {raw : List (Handle.Basic.PivotIndices wordData.alphabet.count)} {normal : NormalForm
    integral.paired
    raw}
  {components : ChainPeriods.ComponentSamples programBank differential}
  {family : PeriodFamilies.PrimitiveFamily programBank.programs
    comparison.domains differential}
  {periods : NormalFormPeriods components
    normal} {profile : PuncturedGrid.NormalFormSamples.Profile periods}
  {floors : Data.Vector Nat wordData.alphabet.count} {surfaceFloor : Nat}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.Sample

/-- The cached corrected handle area equals the area of the actual original period samples with their retained physical
row corrections. -/
theorem corrected_area_eq {stage :
  Nat}
    {primitive : Fin lifted.cutPolygon.patch.cut.count → PrimitivePoint}
    {values : Data.Vector PrimitivePoint wordData.alphabet.count}
    {readings : routes.Sample integral primitive values} {cycles :
      Sewing.NormalFormCycles normal readings}
    (rows : Sample periods stage) (corrected :
      Periods.CorrectedPeriodArea cycles rows.rows) :
    corrected.area = Boundary.HandleAreaBounds.sampledHandleArea raw
      (fun pair => Energy.Polygon.energyPrimitivePoint ((periods.first pair).period.approximation.sample stage +
        (cycles.physical pair.2).right))
      (fun pair => Energy.Polygon.energyPrimitivePoint ((periods.last pair).period.approximation.sample stage -
        (cycles.physical pair.1).right)) := by
  apply corrected.area_eq.trans
  apply Boundary.HandleAreaBounds.sampledHandleArea_congr raw
  · intro pair _
    have equal := (periods.first_sample pair stage).trans (congrArg Neg.neg (rows.row_eq_period pair.2).symm)
    exact (corrected.first_eq_energy pair).trans
      (congrArg (fun value => Energy.Polygon.energyPrimitivePoint (value + (cycles.physical pair.2).right)) equal.symm)
  · intro pair _
    have equal := (periods.last_sample pair stage).trans (rows.row_eq_period pair.1).symm
    exact (corrected.last_eq_energy pair).trans
      (congrArg (fun value => Energy.Polygon.energyPrimitivePoint (value - (cycles.physical pair.1).right)) equal.symm)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.Sample

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea

/-- The first original handle-period comparison transfers to the negative retained second row reading. -/
private theorem first_row_readback {stage : Nat} {point : Gaussian.Basic.Canonical} {error :
  Normalization.InverseRootPolynomial.Coordinate}
    (rows : NormalFormSamples.Sample periods stage) (pair : Handle.Basic.PivotIndices
      wordData.alphabet.count)
    (accurate : Gaussian.Norm.Basic.normSq ((periods.first pair).period.approximation.sample stage - point) <
      error) :
    Gaussian.Norm.Basic.normSq (-rows.rows pair.2 - point) < error := by
  have equal := (periods.first_sample pair stage).trans (congrArg Neg.neg (rows.row_eq_period pair.2).symm)
  exact (congrArg (fun value => Gaussian.Norm.Basic.normSq (value - point)) equal).symm.trans_lt accurate

/-- The last original handle-period comparison transfers to the retained first row reading. -/
private theorem last_row_readback {stage : Nat} {point : Gaussian.Basic.Canonical} {error :
  Normalization.InverseRootPolynomial.Coordinate}
    (rows : NormalFormSamples.Sample periods stage) (pair : Handle.Basic.PivotIndices
      wordData.alphabet.count)
    (accurate : Gaussian.Norm.Basic.normSq ((periods.last pair).period.approximation.sample stage - point) <
      error) :
    Gaussian.Norm.Basic.normSq (rows.rows pair.1 - point) < error := by
  have equal := (periods.last_sample pair stage).trans (rows.row_eq_period pair.1).symm
  exact (congrArg (fun value => Gaussian.Norm.Basic.normSq (value - point)) equal).symm.trans_lt accurate

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea

section

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest

/-- The original handle-area budget using the retained dual-coordinate magnitude and coarse boundary reference. -/
@[expose] def HandleBudget (dual : Boundary.DualCoordinateBounds.DualMagnitude normal.reduction)
  (target : Normalization.InverseRootPolynomial.Coordinate) :=
  Boundary.HandleAreaBudgets.HandleAreaBudget (dual.factor * (4 * reference.bound)) raw.length target

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest

variable {target : Normalization.InverseRootPolynomial.Coordinate} {dual :
  Boundary.DualCoordinateBounds.DualMagnitude normal.reduction}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest

/-- The component, row and boundary allowance allocation for the original normal-form profile and handle target. -/
@[expose] def Allocation (profile : NormalFormSamples.Profile periods)
    (handle : HandleBudget (reference :=
      reference) dual target) :=
  Word.NormalFormBudgets.RowAllocation profile.rows
    (Cut.WordAreaBounds.CutWordArea.areaWeight reference.bound boundary.count)
    handle.rowTarget handle.boundaryTarget

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest

variable {handle :
  NormalFormAreaRequest.HandleBudget (reference
  := reference) dual target}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest

/-- The actual shared-surface word-area request on the retained component allowances and supplied stage floor. -/
@[expose] def SurfaceBudget
    (allocation : Allocation (reference :=
      reference) (boundary := boundary) profile handle)
    (targets : Data.Vector Normalization.InverseRootPolynomial.Coordinate wordData.alphabet.count) (floor :
      Nat) :=
  WordAreaRequests.WordAreaBudget family contacts reference boundary.count
    allocation.component allocation.area targets floor

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest

variable {target : Normalization.InverseRootPolynomial.Coordinate} {targets : Data.Vector
  Normalization.InverseRootPolynomial.Coordinate wordData.alphabet.count}
  (dual : Boundary.DualCoordinateBounds.DualMagnitude normal.reduction)
  (handle : NormalFormAreaRequest.HandleBudget
    (reference := reference) dual target)
  (allocation : NormalFormAreaRequest.Allocation
    (reference := reference) (boundary := boundary) profile handle)
  (area : NormalFormAreaRequest.SurfaceBudget
    (family := family) (contacts := contacts) allocation targets surfaceFloor)
  (movement : Budget.SynchronizedSamples.StageRequest components.streams allocation.component floors)
  (targets_eq : ∀ index, targets index = allocation.component)
  (banks_eq : BanksAligned family segments)
  {requested : PeriodRequest area
    movement.stages}
  {surface : SurfaceSample requested} {centered
    : CenteredSample surface}
  {word : WordSample wordData centered}
  {readings : ChordSample routes integral word}
  {sampleFloor : Nat}
  (common : CommonReadings components
    requested sampleFloor)
  (sources : ProgramSources programBank)
  (positive : SourcesPositive sources)
  (routedPositive : RoutesPositive
    programBank)
  (word_eq : wordData = (Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord pairing))
  (cycles : CycleSample normal readings)
  (rows : RowSample periods common)
  (evaluated : EvaluatedArea normal word)

section
variable {dual handle allocation area movement common cycles rows evaluated}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest

/-- The actual original period-row area sample with the same retained physical corrections. -/
@[expose] def CorrectedSample (cycles :
  CycleSample normal readings) (rows :
  RowSample periods common) :=
  Periods.CorrectedPeriodArea cycles rows.rows

/-- The corrected original period area approximates the retained transformed-word area within the supplied error. -/
@[expose] def HandleAccurate (corrected :
  CorrectedSample cycles rows)
    (evaluated : EvaluatedArea normal word)
      (error : Normalization.InverseRootPolynomial.Coordinate) : Prop :=
  Gaussian.Norm.Basic.normSq (corrected.area - evaluated.area) < error

/-- The actual boundary area approximates twice the corrected period area plus the original remaining-matrix
contraction. -/
@[expose] def PeriodAccurate (corrected :
  CorrectedSample cycles rows) (error :
  Normalization.InverseRootPolynomial.Coordinate) : Prop :=
  Gaussian.Norm.Basic.normSq (surface.surface.boundaryArea - (2 * corrected.area +
    Word.Pairing.contract (fun row column => integral.remaining row column) word.values)) < error

/-- The actual boundary area satisfies the explicit original period formula with physical corrections and the complete
remaining contraction retained. -/
@[expose] def FormulaAccurate (periods :
  NormalFormPeriods components normal)
    (cycles : CycleSample normal readings)
      (common : CommonReadings components
      requested sampleFloor)
    (error : Normalization.InverseRootPolynomial.Coordinate) : Prop :=
  Gaussian.Norm.Basic.normSq (surface.surface.boundaryArea - (2 *
    Boundary.HandleAreaBounds.sampledHandleArea raw
    (fun pair => Energy.Polygon.energyPrimitivePoint ((periods.first pair).period.approximation.sample
      common.common.stage + (cycles.physical pair.2).right))
    (fun pair => Energy.Polygon.energyPrimitivePoint ((periods.last pair).period.approximation.sample
      common.common.stage - (cycles.physical pair.1).right)) +
    Word.Pairing.contract (fun row column => integral.remaining row column) word.values)) < error

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest

end

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest

/-- The original corrected period area meets its requested handle-area target using the retained row bounds and dual
magnitude. -/
theorem handle_area_accurate
    {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
      Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Differentials.Basic.Differential genus}
  {pairing : Word.ProjectedEdgePairs.ProjectedEdgePairing lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {wordData : Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {routes : Sewing.ChordCycleBank wordData}
  {programBank : CyclePrograms.CutCycleProgramBank lifted source routes.cycles}
  {boundary : BoundaryPrograms.LiftedPuncturedGrid.BoundaryProgram lifted source}
    {boundarySegments : PeriodSegmentBanks.SegmentBank boundary.program.period}
  {differential : Fin genus} {comparison :
    PeriodPrimitiveComparison.PrimitiveBank
    (FaceBanks.FaceBank.ofSegments boundary.program boundarySegments)
    differential}
  {segments : ProgramSegments programBank}
  {contacts : BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch
    pairing
    (Periods.PeriodMatrix.standardDifferential differential) comparison.domains}
  {reference : BoundaryPrimitiveReferences.BoundaryReference boundary comparison
    contacts.prepared}
  {integral : Cut.IntegralPairing.CutBoundaryWord wordData}
  {raw : List (Handle.Basic.PivotIndices wordData.alphabet.count)} {normal : NormalForm
    integral.paired
    raw}
  {components : ChainPeriods.ComponentSamples programBank differential}
  {family : PeriodFamilies.PrimitiveFamily programBank.programs
    comparison.domains differential}
  {periods : NormalFormPeriods components
    normal} {profile : NormalFormSamples.Profile periods}
  {floors : Data.Vector Nat wordData.alphabet.count} {surfaceFloor : Nat}
  {target : Normalization.InverseRootPolynomial.Coordinate} {targets : Data.Vector
    Normalization.InverseRootPolynomial.Coordinate wordData.alphabet.count}
  (dual : Boundary.DualCoordinateBounds.DualMagnitude normal.reduction)
  (handle : HandleBudget (reference :=
    reference) dual target)
  (allocation : Allocation (reference :=
    reference) (boundary := boundary) profile handle)
  (area : SurfaceBudget (family := family)
    (contacts := contacts) allocation targets surfaceFloor)
  (movement : Budget.SynchronizedSamples.StageRequest components.streams allocation.component floors)
  (targets_eq : ∀ index, targets index = allocation.component)
  (banks_eq : BanksAligned family segments)
  {requested : PeriodRequest area
    movement.stages}
  {surface : SurfaceSample requested} {centered
    : CenteredSample surface}
  {word : WordSample wordData centered}
  {readings : ChordSample routes integral word}
  {sampleFloor : Nat}
  (common : CommonReadings components
    requested sampleFloor)
  (sources : ProgramSources programBank)
  (positive : SourcesPositive sources)
  (routedPositive : RoutesPositive
    programBank)
  (word_eq : wordData = (Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord pairing))
  (cycles : CycleSample normal readings)
  (rows : RowSample periods common)
  (evaluated : EvaluatedArea normal word)
    (corrected : CorrectedSample cycles
      rows) :
    HandleAccurate corrected evaluated
      handle.handleTarget :=
  corrected.accurate evaluated handle
    (NormalFormMagnitude.WordAreaBudget.normal_values_bounded area surface centered
    word word_eq dual evaluated)
    (Word.NormalFormMagnitude.NormalFormArea.conjugate evaluated
      (Cut.GeneratorBounds.CutBoundaryWord.AreaSample.values_conjugate word centered.conjugate))
    (fun pair member => (NormalFormPeriodArea.first_row_readback rows pair
      (NormalFormComparisons.NormalFormRequest.first_accurate allocation area
      movement targets_eq banks_eq common sources positive routedPositive
      word_eq cycles rows evaluated pair member)).le)
    (fun pair member => (NormalFormPeriodArea.last_row_readback rows pair
      (NormalFormComparisons.NormalFormRequest.last_accurate allocation area movement
      targets_eq banks_eq common sources positive routedPositive
      word_eq cycles rows evaluated pair member)).le)

/-- The actual boundary area meets the requested period-area bound with the original physical and remaining-matrix terms
retained. -/
theorem period_area_accurate
    {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
      Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Differentials.Basic.Differential genus}
  {pairing : Word.ProjectedEdgePairs.ProjectedEdgePairing lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {wordData : Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {routes : Sewing.ChordCycleBank wordData}
  {programBank : CyclePrograms.CutCycleProgramBank lifted source routes.cycles}
  {boundary : BoundaryPrograms.LiftedPuncturedGrid.BoundaryProgram lifted source}
    {boundarySegments : PeriodSegmentBanks.SegmentBank boundary.program.period}
  {differential : Fin genus} {comparison :
    PeriodPrimitiveComparison.PrimitiveBank
    (FaceBanks.FaceBank.ofSegments boundary.program boundarySegments)
    differential}
  {segments : ProgramSegments programBank}
  {contacts : BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch
    pairing
    (Periods.PeriodMatrix.standardDifferential differential) comparison.domains}
  {reference : BoundaryPrimitiveReferences.BoundaryReference boundary comparison
    contacts.prepared}
  {integral : Cut.IntegralPairing.CutBoundaryWord wordData}
  {raw : List (Handle.Basic.PivotIndices wordData.alphabet.count)} {normal : NormalForm
    integral.paired
    raw}
  {components : ChainPeriods.ComponentSamples programBank differential}
  {family : PeriodFamilies.PrimitiveFamily programBank.programs
    comparison.domains differential}
  {periods : NormalFormPeriods components
    normal} {profile : NormalFormSamples.Profile periods}
  {floors : Data.Vector Nat wordData.alphabet.count} {surfaceFloor : Nat}
  {target : Normalization.InverseRootPolynomial.Coordinate} {targets : Data.Vector
    Normalization.InverseRootPolynomial.Coordinate wordData.alphabet.count}
  (dual : Boundary.DualCoordinateBounds.DualMagnitude normal.reduction)
  (handle : HandleBudget (reference :=
    reference) dual target)
  (allocation : Allocation (reference :=
    reference) (boundary := boundary) profile handle)
  (area : SurfaceBudget (family := family)
    (contacts := contacts) allocation targets surfaceFloor)
  (movement : Budget.SynchronizedSamples.StageRequest components.streams allocation.component floors)
  (targets_eq : ∀ index, targets index = allocation.component)
  (banks_eq : BanksAligned family segments)
  {requested : PeriodRequest area
    movement.stages}
  {surface : SurfaceSample requested} {centered
    : CenteredSample surface}
  {word : WordSample wordData centered}
  {readings : ChordSample routes integral word}
  {sampleFloor : Nat}
  (common : CommonReadings components
    requested sampleFloor)
  (sources : ProgramSources programBank)
  (positive : SourcesPositive sources)
  (routedPositive : RoutesPositive
    programBank)
  (word_eq : wordData = (Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord pairing))
  (cycles : CycleSample normal readings)
  (rows : RowSample periods common)
  (evaluated : EvaluatedArea normal word)
    (corrected : CorrectedSample cycles
      rows) :
    PeriodAccurate corrected target :=
  handle.combine surface.surface.boundaryArea evaluated.area corrected.area
    (Word.Pairing.contract (fun row column => integral.remaining row column) word.values)
    (NormalFormRequests.NormalFormRequest.area_accurate allocation area word_eq
      evaluated)
    (handle_area_accurate dual handle
      allocation area movement targets_eq banks_eq common sources positive routedPositive
      word_eq cycles rows evaluated corrected)

/-- The executable cache is literally the original period-area expression,
with no remaining analytic inequality premise supplied by the caller. -/
@[expose] def PeriodFormulaAccurateStatement : Prop :=
  ∀ {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
    Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Differentials.Basic.Differential genus}
  {pairing : Word.ProjectedEdgePairs.ProjectedEdgePairing lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {wordData : Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {routes : Sewing.ChordCycleBank wordData}
  {programBank : CyclePrograms.CutCycleProgramBank lifted source routes.cycles}
  {boundary : BoundaryPrograms.LiftedPuncturedGrid.BoundaryProgram lifted source}
    {boundarySegments : PeriodSegmentBanks.SegmentBank boundary.program.period}
  {differential : Fin genus} {comparison :
    PeriodPrimitiveComparison.PrimitiveBank
    (FaceBanks.FaceBank.ofSegments boundary.program boundarySegments)
    differential}
  {segments : ProgramSegments programBank}
  {contacts : BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch
    pairing
    (Periods.PeriodMatrix.standardDifferential differential) comparison.domains}
  {reference : BoundaryPrimitiveReferences.BoundaryReference boundary comparison
    contacts.prepared}
  {integral : Cut.IntegralPairing.CutBoundaryWord wordData}
  {raw : List (Handle.Basic.PivotIndices wordData.alphabet.count)} {normal : NormalForm
    integral.paired
    raw}
  {components : ChainPeriods.ComponentSamples programBank differential}
  {family : PeriodFamilies.PrimitiveFamily programBank.programs
    comparison.domains differential}
  {periods : NormalFormPeriods components
    normal} {profile : NormalFormSamples.Profile periods}
  {floors : Data.Vector Nat wordData.alphabet.count} {surfaceFloor : Nat}
  {target : Normalization.InverseRootPolynomial.Coordinate} {targets : Data.Vector
    Normalization.InverseRootPolynomial.Coordinate wordData.alphabet.count}
  (dual : Boundary.DualCoordinateBounds.DualMagnitude normal.reduction)
  (handle : HandleBudget (reference :=
    reference) dual target)
  (allocation : Allocation (reference :=
    reference) (boundary := boundary) profile handle)
  (area : SurfaceBudget (family := family)
    (contacts := contacts) allocation targets surfaceFloor)
  (movement : Budget.SynchronizedSamples.StageRequest components.streams allocation.component floors)
  (_targets_eq : ∀ index, targets index = allocation.component)
  (_banks_eq : BanksAligned family segments)
  {requested : PeriodRequest area
    movement.stages}
  {surface : SurfaceSample requested} {centered
    : CenteredSample surface}
  {word : WordSample wordData centered}
  {readings : ChordSample routes integral word}
  {sampleFloor : Nat}
  (common : CommonReadings components
    requested sampleFloor)
  (sources : ProgramSources programBank)
  (_positive : SourcesPositive sources)
  (_routedPositive : RoutesPositive
    programBank)
  (_word_eq : wordData = (Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord pairing))
  (cycles : CycleSample normal readings)
  (rows : RowSample periods common)
  (_evaluated : EvaluatedArea normal word)
    (_corrected : CorrectedSample cycles
      rows),
    FormulaAccurate periods cycles common
      target

/-- The explicit actual common-stage period formula satisfies the requested boundary-area accuracy under the retained
ownership and orientation certificates. -/
theorem period_formula_accurate : PeriodFormulaAccurateStatement := by
  dsimp only
    [PeriodFormulaAccurateStatement]
  intro genus curve branches higher base lifted source pairing wordData routes programBank boundary boundarySegments
    differential comparison segments contacts reference integral raw normal components family periods profile floors
    surfaceFloor target targets dual handle allocation area movement targets_eq banks_eq requested surface centered word
    readings sampleFloor common sources positive routedPositive word_eq cycles rows evaluated corrected
  dsimp only [FormulaAccurate]
  have equal := congrArg (fun value => Gaussian.Norm.Basic.normSq (surface.surface.boundaryArea - (2 * value +
    Word.Pairing.contract (fun row column => integral.remaining row column) word.values)))
      (rows.corrected_area_eq corrected)
  exact equal.symm.trans_lt
    (period_area_accurate dual handle
    allocation area movement targets_eq banks_eq common sources positive routedPositive
    word_eq cycles rows evaluated corrected)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest

end
end
