module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
import Purelib.Integration.Energy.Polygon
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic

import Purelib.Approximation.Budget.SynchronizedSamples
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Surface.Boundary.DualCoordinateBounds
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.LinearAlgebra.Alternating.Reduction.CycleRows
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.CorrectedPeriodArea
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.HandleAreaBudgets
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Cut.WordAreaBounds
import Purelib.Topology.Surface.Sewing.CenteredSewnSamples
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.NormalFormCycles
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.NormalFormBudgets

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Integration

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

public section

/-!
# One shared request for period area and all physical Newton holes

The all-hole threshold is included in the period surface floor before any
shared primitives are evaluated. Both comparisons consume the same triangle
and sewing caches. The full normal-form expression retains its physical
row shifts and remaining matrix, together with the explicit annular cut
correction. No analytic comparison inequality is supplied by the caller.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea

open Purelib.Topology.Polygon.Stokes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Normalization.InverseRootPolynomial.Coordinate}

/-- The original all-hole area request allocated one quarter of the supplied period target at the retained radius. -/
@[expose] def NewtonRequest (preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation
  original) (target radius : Normalization.InverseRootPolynomial.Coordinate) :=
  Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest preparation (target / 4)
    radius

variable {newton : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonRequest preparation target
  radius}

/-- Read the retained punctured grid without exposing its construction in types. -/
@[expose] def NewtonBase (newton : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonRequest preparation target
  radius) :=
  newton.single.grid.punctured

variable {lifted : Meshes.LiftedPuncturedGrid
  (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonBase newton)}
  {source : Hyperelliptic.Differentials.Basic.Differential genus}
  {pairing : Topology.Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {wordData : Topology.Surface.Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {routes : Topology.Surface.Sewing.ChordCycleBank wordData}
  {programBank : Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgramBank lifted source routes.cycles}
  {boundary : Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms.LiftedPuncturedGrid.BoundaryProgram lifted source}
    {boundarySegments : Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank boundary.program.period}
  {differential : Fin genus}

/-- The original boundary primitive bank on its retained segment-derived face domains and selected basis differential.
-/
@[expose] def BoundaryComparison (boundary :
  Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms.LiftedPuncturedGrid.BoundaryProgram lifted source)
    (boundarySegments : Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank boundary.program.period)
      (differential : Fin genus) :=
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank.ofSegments boundary.program boundarySegments)
    differential

variable {comparison : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.BoundaryComparison boundary
  boundarySegments differential}
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
  {floors : Data.Vector Nat wordData.alphabet.count} {surfaceFloor : Nat}

namespace NewtonAreaRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest

/-- The original all-hole excision on the exact punctured grid retained by the Newton request. -/
@[expose] def Excision (newton : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonRequest preparation target
  radius)
    (lifted : Meshes.LiftedPuncturedGrid (Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonBase newton)) :=
  Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision newton.single.grid lifted

variable {excision : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.Excision
  newton lifted}

/-- The actual outer-boundary preparations of the retained original all-hole excision. -/
@[expose] def Preparations (excision : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.Excision
  newton lifted) :=
  Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations excision

variable {prepared : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.Preparations
  excision}

/-- The original all-hole comparison on the retained preparations, differential and shared face domains. -/
@[expose] def HoleComparison (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.Preparations excision)
    (differential : Fin genus) (domains : _) :=
  Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison prepared
    differential domains

variable {excision : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.Excision
  newton lifted}
  {prepared : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.Preparations
    excision}
  (holes : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.HoleComparison prepared
    differential comparison.domains)

/-- The common surface floor including the original all-hole comparison threshold. -/
@[expose] def SurfaceFloor (holes : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.HoleComparison
  prepared differential comparison.domains) (floor : Nat) :=
  max floor holes.index

variable {targets : Data.Vector Normalization.InverseRootPolynomial.Coordinate wordData.alphabet.count}
  (dual : Topology.Surface.Boundary.DualCoordinateBounds.DualMagnitude normal.reduction)
  (handle : Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest.HandleBudget (reference :=
    reference) dual (target / 4))
  (allocation : Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest.Allocation (reference :=
    reference) (boundary := boundary) profile handle)
  (area : Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest.SurfaceBudget (family := family)
    (contacts := contacts) allocation targets
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.SurfaceFloor holes
    surfaceFloor))

section
variable {holes dual handle allocation area}

/-- The synchronized component-period request at the original allocated tolerance and supplied stage floors. -/
@[expose] def Movement (components : Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples programBank
  differential)
    (allocation : Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest.Allocation (reference :=
      reference) (boundary := boundary) profile handle)
    (floors : Data.Vector Nat wordData.alphabet.count) :=
  Budget.SynchronizedSamples.StageRequest components.streams allocation.component floors

variable {movement : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.Movement
  components allocation floors}

/-- The actual component stages retained by the synchronized movement request. -/
@[expose] def StageIndices (movement : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.Movement
  components allocation floors) := movement.stages

end

variable
  (movement : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.Movement components
    allocation floors)

section
variable {dual handle allocation area movement holes}

/-- Every original component target agrees with the common retained allocation. -/
@[expose] def TargetsAligned (targets : Data.Vector Normalization.InverseRootPolynomial.Coordinate
  wordData.alphabet.count)
    (allocation : Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest.Allocation (reference :=
      reference) (boundary := boundary) profile handle) : Prop :=
  ∀ index, targets index = allocation.component

/-- The retained cut word is exactly the boundary word of the original projected edge pairing. -/
@[expose] def WordAligned (wordData : Topology.Surface.Cut.BoundaryWord.CutBoundaryWord
  lifted.cutPolygon.patch.cut.vertexLabels lifted.cutPolygon.patch.cut.boundary)
    (pairing : Topology.Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing lifted.cutPolygon.patch.cut.vertexLabels
      lifted.cutPolygon.patch.cut.boundary) : Prop :=
  wordData = (Topology.Surface.Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord pairing)

end

variable
  (targets_eq : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.TargetsAligned
    targets allocation)
  (banks_eq : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.BanksAligned family segments)
  {requested : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.PeriodRequest area
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.StageIndices movement)}
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
  (word_eq : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.WordAligned wordData
    pairing)
  (cycles : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CycleSample normal readings)
  (rows : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.RowSample periods common)
  (evaluated : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.EvaluatedArea normal word)

section
variable {holes dual handle allocation area movement}

/-- The original annular comparison sample on the exact triangle cache of the shared period surface. -/
@[expose] def AnnularSource (surface :
  Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.SurfaceSample requested) :=
  Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison.Sample holes
    surface.triangles

variable {annularSource :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.AnnularSource (holes := holes)
  surface}

/-- The sewn annular comparison on the same original retained surface cache. -/
@[expose] def AnnularSample (annularSource :
  Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.AnnularSource (holes := holes) surface) :=
  Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison.SewnSample
    annularSource surface.surface

/-- Build the original annular source comparison from the already retained shared triangle values. -/
@[expose] def sourceSample (surface :
  Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.SurfaceSample requested) :
  Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.AnnularSource (holes := holes) surface :=
  Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison.Sample.build
    holes surface.triangles

end

/-- Construct the annular consumer from the exact surface already used by
all period rows. The shared request has already paid its contact threshold. -/
@[expose] def sample : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.AnnularSample
  (Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.sourceSample (holes := holes) surface) :=

    Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest.Comparison.SewnSample.build
    (Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.sourceSample (holes := holes) surface)
    surface.surface

/-- The shared period-reading index meets the original all-hole comparison threshold. -/
@[expose] def HolesLater : Prop := holes.index ≤ area.word.request.periods.index

include area in
/-- The common surface floor ensures the original all-hole comparison is ready at the retained period-reading stage. -/
theorem holes_later : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.HolesLater holes dual handle
  allocation area :=
  (Data.Nat.Order.le_max_right surfaceFloor holes.index).trans area.floor_le

variable {annularSource :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.AnnularSource (holes := holes)
  surface}

section
variable {holes dual handle allocation area movement common cycles rows evaluated}

/-- The retained remaining-surface area approximates the corrected period area and full remaining contraction, minus the
actual annular correction. -/
@[expose] def RetainedAccurate (corrected :
  Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest.CorrectedSample cycles rows)
    (annular : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.AnnularSample annularSource) (error
      : Normalization.InverseRootPolynomial.Coordinate) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (annular.retained.remaining.area - ((2 * corrected.area +
    Topology.Surface.Word.Pairing.contract (fun row column => integral.remaining row column) word.values) -
      annular.correction)) < error

/-- The explicit original period formula approximates the remaining-surface area with the physical row shifts, remaining
matrix and annular correction retained. -/
@[expose] def RetainedFormulaAccurate (periods :
  NormalFormPeriods components normal)
    (cycles : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CycleSample normal readings)
      (common : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.CommonReadings components
      requested sampleFloor)
    (annular : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.AnnularSample annularSource) (error
      : Normalization.InverseRootPolynomial.Coordinate) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (annular.retained.remaining.area - ((2 *
    Topology.Surface.Boundary.HandleAreaBounds.sampledHandleArea raw
    (fun pair => Energy.Polygon.energyPrimitivePoint
      ((periods.first pair).period.approximation.sample common.common.stage + (cycles.physical pair.2).right))
    (fun pair => Energy.Polygon.energyPrimitivePoint
      ((periods.last pair).period.approximation.sample common.common.stage - (cycles.physical pair.1).right)) +
    Topology.Surface.Word.Pairing.contract (fun row column => integral.remaining row column) word.values) -
      annular.correction)) < error

end

/-- The complete retained-surface estimate is obtained from the two actual
procedures. Only the displayed physical correction remains to be cancelled
or bounded in the final bilinear argument. -/
theorem period_area_accurate
    {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
      Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Normalization.InverseRootPolynomial.Coordinate}
  {newton : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonRequest preparation target radius}
  {lifted : Meshes.LiftedPuncturedGrid (Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonBase newton)}
  {source : Hyperelliptic.Differentials.Basic.Differential genus}
  {pairing : Topology.Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {wordData : Topology.Surface.Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {routes : Topology.Surface.Sewing.ChordCycleBank wordData}
  {programBank : Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgramBank lifted source routes.cycles}
  {boundary : Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms.LiftedPuncturedGrid.BoundaryProgram lifted source}
    {boundarySegments : Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank boundary.program.period}
  {differential : Fin genus} {comparison : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.BoundaryComparison
    boundary boundarySegments differential}
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
  {floors : Data.Vector Nat wordData.alphabet.count} {surfaceFloor : Nat}
  {excision : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.Excision newton lifted}
  {prepared : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.Preparations excision}
  (holes : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.HoleComparison prepared differential
    comparison.domains)
  {targets : Data.Vector Normalization.InverseRootPolynomial.Coordinate wordData.alphabet.count}
  (dual : Topology.Surface.Boundary.DualCoordinateBounds.DualMagnitude normal.reduction)
  (handle : Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest.HandleBudget (reference :=
    reference) dual (target / 4))
  (allocation : Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest.Allocation (reference :=
    reference) (boundary := boundary) profile handle)
  (area : Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest.SurfaceBudget (family := family)
    (contacts := contacts) allocation targets
    (Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.SurfaceFloor holes surfaceFloor))
  (movement : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.Movement components allocation
    floors)
  (targets_eq : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.TargetsAligned targets allocation)
  (banks_eq : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.BanksAligned family segments)
  {requested : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.PeriodRequest area
    (Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.StageIndices movement)}
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
  (word_eq : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.WordAligned wordData pairing)
  (cycles : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.CycleSample normal readings)
  (rows : Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest.RowSample periods common)
  (evaluated : Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest.EvaluatedArea normal word)
  {annularSource : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.AnnularSource (holes := holes)
    surface}
    (corrected : Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest.CorrectedSample cycles
      rows)
    (annular : Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.AnnularSample annularSource) :
    Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.RetainedAccurate corrected annular target :=
      by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.RetainedAccurate]
  have bounded := @Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest.period_area_accurate
    genus curve branches higher newton.single.grid.punctured lifted
    source pairing wordData routes programBank boundary boundarySegments differential comparison segments contacts
      reference integral raw normal
    components family periods profile floors
      (Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.SurfaceFloor holes surfaceFloor) (target /
      4) targets dual handle allocation area movement
    targets_eq banks_eq requested surface centered word readings sampleFloor common sources positive routedPositive
      word_eq cycles rows evaluated corrected
  exact (annular.period_accurate (Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.holes_later
    holes dual handle allocation area)
    (2 * corrected.area + Topology.Surface.Word.Pairing.contract (fun row column => integral.remaining row column)
      word.values) bounded).trans_eq
      ((mul_comm _ _).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

end NewtonAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea
