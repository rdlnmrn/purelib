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
    Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.RetainedFormulaAccurate periods cycles common
      annular target := open Purelib.Integration in by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.NewtonPeriodArea.NewtonAreaRequest.RetainedFormulaAccurate]
  have bounded := @Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriodArea.NormalFormAreaRequest.period_formula_accurate
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
