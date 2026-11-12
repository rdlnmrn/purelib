module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
import Purelib.Integration.Energy.Polygon
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodAreaCore
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.HandleAreaBudgets
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Curves

open Purelib.Data.Rat

open Purelib

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea

open Purelib.Topology.Polygon.Stokes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormRequests.NormalFormRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest

namespace NewtonAreaRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormComparisons.NormalFormRequest

/-- The handle values here are the actual common-stage period samples,
including the physical shifts required by the integral normal form. -/
theorem period_formula_accurate
    {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
      Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Normalization.InverseRootPolynomial.Coordinate}
  {newton : NewtonRequest preparation target radius}
  {lifted : Meshes.LiftedPuncturedGrid (NewtonBase newton)}
  {source : Differentials.Basic.Differential genus}
  {pairing : Topology.Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {wordData : Topology.Surface.Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
    lifted.cutPolygon.patch.cut.boundary}
  {routes : Topology.Surface.Sewing.ChordCycleBank wordData}
  {programBank : Cut.CyclePrograms.CutCycleProgramBank lifted source routes.cycles}
  {boundary : BoundaryPrograms.LiftedPuncturedGrid.BoundaryProgram lifted source}
    {boundarySegments : PeriodSegmentBanks.SegmentBank boundary.program.period}
  {differential : Fin genus} {comparison : BoundaryComparison
    boundary boundarySegments differential}
  {segments : ProgramSegments programBank}
  {contacts : BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch
    pairing
    (Periods.PeriodMatrix.standardDifferential differential) comparison.domains}
  {reference : BoundaryPrimitiveReferences.BoundaryReference boundary comparison
    contacts.prepared}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord wordData}
  {raw : List (Handle.Basic.PivotIndices wordData.alphabet.count)} {normal : NormalForm
    integral.paired
    raw}
  {components : Cut.ChainPeriods.ComponentSamples programBank differential}
  {family : Cut.PeriodFamilies.PrimitiveFamily programBank.programs
    comparison.domains differential}
  {periods : NormalFormPeriods components
    normal} {profile : NormalFormSamples.Profile periods}
  {floors : Data.Vector Nat wordData.alphabet.count} {surfaceFloor : Nat}
  {excision : Excision newton lifted}
  {prepared : Preparations excision}
  (holes : HoleComparison prepared differential
    comparison.domains)
  {targets : Data.Vector Normalization.InverseRootPolynomial.Coordinate wordData.alphabet.count}
  (dual : Topology.Surface.Boundary.DualCoordinateBounds.DualMagnitude normal.reduction)
  (handle : NormalFormPeriodArea.NormalFormAreaRequest.HandleBudget (reference :=
    reference) dual (target / 4))
  (allocation : NormalFormPeriodArea.NormalFormAreaRequest.Allocation (reference :=
    reference) (boundary := boundary) profile handle)
  (area : NormalFormPeriodArea.NormalFormAreaRequest.SurfaceBudget (family := family)
    (contacts := contacts) allocation targets
    (SurfaceFloor holes surfaceFloor))
  (movement : Movement components allocation
    floors)
  (targets_eq : TargetsAligned targets allocation)
  (banks_eq : BanksAligned family segments)
  {requested : PeriodRequest area
    (StageIndices movement)}
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
  (word_eq : WordAligned wordData pairing)
  (cycles : CycleSample normal readings)
  (rows : RowSample periods common)
  (evaluated : EvaluatedArea normal word)
  {annularSource : AnnularSource (holes := holes)
    surface}
    (corrected : NormalFormPeriodArea.NormalFormAreaRequest.CorrectedSample cycles
      rows)
    (annular : AnnularSample annularSource) :
    RetainedFormulaAccurate periods cycles common
      annular target := open Purelib.Integration in by
  dsimp only [RetainedFormulaAccurate]
  have bounded := @NormalFormPeriodArea.NormalFormAreaRequest.period_formula_accurate
    genus curve branches higher newton.single.grid.punctured lifted
    source pairing wordData routes programBank boundary boundarySegments differential comparison segments contacts
      reference integral raw normal
    components family periods profile floors
      (SurfaceFloor holes surfaceFloor) (target /
      4) targets dual handle allocation area movement
    targets_eq banks_eq requested surface centered word readings sampleFloor common sources positive routedPositive
      word_eq cycles rows evaluated corrected
  exact (annular.period_accurate (NewtonAreaRequest.holes_later
    holes dual handle allocation area)
    (2 * Topology.Surface.Boundary.HandleAreaBounds.sampledHandleArea raw
      (fun pair => Energy.Polygon.energyPrimitivePoint
        ((periods.first pair).period.approximation.sample common.common.stage + (cycles.physical pair.2).right))
      (fun pair => Energy.Polygon.energyPrimitivePoint
        ((periods.last pair).period.approximation.sample common.common.stage - (cycles.physical pair.1).right)) +
      Topology.Surface.Word.Pairing.contract (fun row column => integral.remaining row column) word.values)
        bounded).trans_eq
      ((mul_comm _ _).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

end NewtonAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea
