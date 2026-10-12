module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Surface.Boundary.NormalFormArea
import Purelib.Topology.Surface.Boundary.NormalFormErrorBounds
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Cut.WordAreaBounds
import Purelib.Topology.Surface.Sewing.CenteredSewnSamples
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.NormalFormCycles
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests
public import Purelib.Topology.Surface.Word.NormalFormBudgets
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Budget.WeightedRowBudgets
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.Alternating.Reduction.CycleRows
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

public section

/-!
# One joint request for actual normal-form periods and surface area

The row profile, boundary magnitude and movement scales are fixed before
requesting a shared numerical surface. Word error, path error and common-stage
movement all fit the same positive component allowance.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests

open Purelib.Topology.Polygon.Stokes

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
  {segments : Purelib.Data.Vector.DependentVector (fun index =>
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

namespace NormalFormRequest

variable {periods : NormalFormPeriods
  components normal} {profile : Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples.Profile periods}
  {rowTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate} {floors : Data.Vector Nat
    wordData.alphabet.count}
  {surfaceFloor : Nat} {targets : Data.Vector Normalization.InverseRootPolynomial.Coordinate
    wordData.alphabet.count}
  (allocation : Topology.Surface.Word.NormalFormBudgets.RowAllocation profile.rows
    (Topology.Surface.Cut.WordAreaBounds.CutWordArea.areaWeight reference.bound boundary.count) rowTarget areaTarget)
  (area : Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests.WordAreaBudget family contacts reference
    boundary.count allocation.component allocation.area targets surfaceFloor)

/-- The original word-error allowance fits the common retained component allowance. -/
theorem word_le : area.wordTarget ≤ allocation.component := open Purelib.Approximation in by
  have equal := area.wordTarget_eq.trans
    (congrArg (Rational.Budget.Weighted.allowance allocation.area) area.weight_eq)
  exact equal.le.trans allocation.word_le

variable {minimumStages : Data.Vector Nat wordData.alphabet.count}

section
variable {allocation area}
/-- The exact requested period family from the original word-area budget at the supplied minimum stages. -/
@[expose] def PeriodRequest
    (area : Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests.WordAreaBudget family contacts reference
      boundary.count allocation.component allocation.area targets surfaceFloor)
    (stages : Data.Vector Nat wordData.alphabet.count) :=
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.Requested area.word.request.periods stages
end

variable {requested :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.PeriodRequest area
  minimumStages}

section
variable {allocation area}

/-- Exact dependent surface types keep theorem signatures compact. -/
@[expose] def SurfaceSample (requested :
  Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.PeriodRequest area minimumStages) :=
  Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles.Requested.Sewn requested lifted.cutPolygon.patch

variable {surface : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.SurfaceSample
  requested}

/-- The original centered view of the retained shared sewn surface. -/
@[expose] def CenteredSample (surface :
  Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.SurfaceSample requested) :=
  Topology.Surface.Sewing.CenteredSewnSamples.Centered surface.surface

variable {centered :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CenteredSample surface}

/-- The actual cut-word area sample on the retained centered values and original cut anchor. -/
@[expose] def WordSample (wordData : Topology.Surface.Cut.BoundaryWord.CutBoundaryWord
  lifted.cutPolygon.patch.cut.vertexLabels lifted.cutPolygon.patch.cut.boundary)
    (centered : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CenteredSample surface) :=
  Topology.Surface.Cut.WordArea.CutBoundaryWord.AreaSample wordData centered.energyValues
    (centered.energyValues lifted.cutPolygon.patch.cut.anchor)

variable {word : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.WordSample
  wordData centered}

/-- The exact original chord-bank sample on the retained integral pairing and centered word values. -/
@[expose] def ChordSample (routes : Topology.Surface.Sewing.ChordCycleBank wordData)
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord wordData) (word :
      Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.WordSample wordData centered) :=
  routes.Sample integral centered.energyValues word.values

variable {readings : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.ChordSample
  routes integral word}

/-- The normal-form cycles evaluated from the actual retained chord readings. -/
@[expose] def CycleSample (normal : LinearAlgebra.Alternating.NormalForm integral.paired raw) (readings :
  Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.ChordSample routes integral word) :=
  Topology.Surface.Sewing.NormalFormCycles normal readings

/-- The original normal-form area evaluated on the retained word values. -/
@[expose] def EvaluatedArea (normal : LinearAlgebra.Alternating.NormalForm integral.paired raw) (word :
  Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.WordSample wordData centered) :=
  Topology.Surface.Boundary.NormalFormArea normal word.values

/-- Both coordinates of one actual chord error satisfy the supplied magnitude allowance. -/
@[expose] def ChordErrorsBounded (readings :
  Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.ChordSample routes integral word)
    (index : Fin wordData.alphabet.count) (amount : Normalization.InverseRootPolynomial.Coordinate) : Prop :=
  Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (readings.errors index) amount

/-- Both coordinates of one actual transformed row error satisfy the supplied allowance. -/
@[expose] def RowErrorsBounded (cycles :
  Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CycleSample normal readings)
    (row : Fin wordData.alphabet.count) (amount : Normalization.InverseRootPolynomial.Coordinate) : Prop :=
  Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (cycles.errors row) amount

/-- The actual surface boundary area is within the target of twice the retained handle area plus the original remaining
pairing contraction. -/
@[expose] def BoundaryAreaAccurate (surface :
  Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.SurfaceSample requested)
    (centered : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CenteredSample surface) (word :
      Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.WordSample wordData centered)
    (evaluated : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.EvaluatedArea normal word)
      (target : Normalization.InverseRootPolynomial.Coordinate) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (surface.surface.boundaryArea - (2 * evaluated.area +
    Topology.Surface.Word.Pairing.contract (fun row column => integral.remaining row column) word.values)) < target

end

variable
  {surface : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.SurfaceSample
    requested} {centered :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CenteredSample surface}
  {word : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.WordSample wordData
    centered}
  {readings : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.ChordSample routes
    integral word}

/-- The original chord errors fit the common component allowance on the actual shared surface. -/
theorem chord_errors_bounded (word_eq : wordData = Topology.Surface.Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord
  pairing)
    (surface : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.SurfaceSample requested)
      (centered : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CenteredSample surface)
    (word : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.WordSample wordData centered)
    (readings : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.ChordSample routes integral
      word) (index : Fin wordData.alphabet.count) :
    Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.ChordErrorsBounded readings index
      allocation.component := by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.ChordErrorsBounded]
  cases word_eq
  have estimate := area.word.chords_accurate surface centered word readings index
  simpa only [Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded,
    Gaussian.Norm.Basic.normSq_eq_canonical] using
    (show _ ∧ _ from ⟨estimate.1.le.trans
      (Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.word_le allocation area),
      estimate.2.le.trans (Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.word_le allocation
        area)⟩)

/-- Each actual transformed row error fits its retained coefficient mass times the common component allowance. -/
theorem row_errors_bounded (word_eq : wordData = Topology.Surface.Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord
  pairing)
    (cycles : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CycleSample normal readings) (row
      : Fin wordData.alphabet.count) :
    Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.RowErrorsBounded cycles row
      ((profile.rows.coefficients.get row).mass * allocation.component) :=
  Topology.Surface.Boundary.NormalFormErrorBounds.errors_bounded cycles profile.rows
    (Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.chord_errors_bounded allocation area
      word_eq surface centered word readings) row

/-- The retained handle-area evaluation approximates the actual boundary area within the original allocated area target.
-/
theorem area_accurate (word_eq : wordData = Topology.Surface.Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord pairing)
  (evaluated : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.EvaluatedArea normal word) :
    Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.BoundaryAreaAccurate surface centered word
      evaluated areaTarget := by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.BoundaryAreaAccurate]
  cases word_eq
  exact (area.handles_accurate surface centered word integral normal evaluated).trans_le allocation.area_le

end NormalFormRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests
