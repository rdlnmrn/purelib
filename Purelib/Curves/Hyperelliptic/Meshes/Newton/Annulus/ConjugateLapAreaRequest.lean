module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.ConjugateSubwordArea
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LapSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateChartAreaRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Data.Gaussian.Basic
import Init.Data.List.Lemmas
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

/-! Small paired polygons on the two actual outer Newton-band laps.
Each lap is compared separately, retaining the concatenation cross term
rather than inferring lap smallness from the full double-tour area. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.ConjugateLapAreaRequest

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.ConjugateSubwordArea.NewtonPreparation
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests.NewtonPreparation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted (OuterPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation (AreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests.NewtonPreparation.AreaRequest
  (PairedComparison)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LapSources (firstLap secondLap firstLap_member secondLap_member
  firstLap_length_le secondLap_length_le firstLap_project secondLap_project sources_nonloop)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests (PairedChartAreaRequest)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : NewtonPreparation original} {target radius : Data.Rat.Fraction.Rational}
  {request : Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.AreaRequest preparation target
    radius}
  {index : Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {annulus :
    Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces request.grid index}
  {lifted : LiftedPuncturedGrid request.grid.punctured} {region :
    Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted}
  {prepared : Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region}
  {domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    request.grid.faces.regulars} {i j : Fin genus}

/-- One common threshold controls the sum of the canonical lap polygons. The grid was already selected by the request's
pre-grid count budget. -/
@[expose] def conjugateLapAreaRequest (comparison : AreaRequest.PairedComparison request prepared i j domains)
    (first : FaceMagnitudeBank domains (standardDifferential i))
    (second : FaceMagnitudeBank domains (standardDifferential j)) (floor : Nat) :
    {threshold : Nat // floor ≤ threshold ∧
      ∀ stage (cache : RegularMeshes.Numerics domains stage)
        (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
          TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh),
        threshold ≤ stage →
        let value := fun edge => (⟨Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation lifted.mesh
          left.values edge),
          CanonicalEdgeValues.edgeValuation lifted.mesh right.values edge⟩ : PrimitivePoint)
        let area := fun sheet => PairedIncrementArea.area
          ((lifted.edges.indexedEdges lifted.vertices annulus.boundary sheet).map value)
        Data.Gaussian.Norm.Basic.normSq (area 0 + area 1) ≤ 16 * target } := by
  let zero := PairedChartAreaRequest.build first second (LapSources.firstLap prepared)
    (fun source member => LapSources.sources_nonloop prepared source (LapSources.firstLap_member prepared member))
    target request.budget.positive
  let one := PairedChartAreaRequest.build first second (LapSources.secondLap prepared)
    (fun source member => LapSources.sources_nonloop prepared source (LapSources.secondLap_member prepared member))
    target request.budget.positive
  let threshold := max floor (max comparison.stage (max zero.index one.index))
  refine ⟨threshold, Data.Nat.Order.le_max_left _ _, ?_⟩
  intro stage cache left right later value area
  have references := (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans later)
  have leftLater := (Data.Nat.Order.le_max_left _ _).trans (comparison.stage_eq ▸ references)
  have rightLater := (Data.Nat.Order.le_max_right _ _).trans (comparison.stage_eq ▸ references)
  have charts := (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans later)
  have bound (sources : List (SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length))
      (members : ∀ source ∈ sources, source ∈ prepared.sources)
      (length : sources.length ≤ region.outer.length)
      (chart : PairedChartAreaRequest first second sources target)
      (chartLater : chart.index ≤ stage) :
      Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area
        (sources.map (fun source => value (source.project lifted.mesh.triangulation.faces)))) ≤ 4 * target := by
    let sourceArea := PairedIncrementArea.area (sources.map (fun source =>
      (⟨Data.Gaussian.Basic.conj (SourceEdge.increment source left.values), SourceEdge.increment source
        right.values⟩ : PrimitivePoint)))
    let projected := PairedIncrementArea.area
      (sources.map (fun source => value (source.project lifted.mesh.triangulation.faces)))
    have small := AreaRequest.conjugate_subword_area_accurate request comparison.left comparison.right sources members
      length
      leftLater rightLater left right
    let closeComparison := chart.realize .conjugate left right chartLater
    have close := closeComparison.pay
    rw [closeComparison.residual_readback] at close
    change Data.Gaussian.Norm.Basic.normSq sourceArea < target at small
    change Data.Gaussian.Norm.Basic.normSq (sourceArea - projected) ≤ target at close
    have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two sourceArea (sourceArea - projected)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct small.le
        close) (by decide))
    rw [show sourceArea - (sourceArea - projected) = projected by ring1] at estimate
    exact estimate.trans_eq (by ring1)
  have zeroBound := bound (LapSources.firstLap prepared) (fun _ member => LapSources.firstLap_member prepared member)
    (LapSources.firstLap_length_le prepared) zero ((Data.Nat.Order.le_max_left _ _).trans charts)
  have oneBound := bound (LapSources.secondLap prepared) (fun _ member => LapSources.secondLap_member prepared member)
    (LapSources.secondLap_length_le prepared) one ((Data.Nat.Order.le_max_right _ _).trans charts)
  have zeroMap := congrArg (List.map value) (LapSources.firstLap_project prepared)
  have oneMap := congrArg (List.map value) (LapSources.secondLap_project prepared)
  rw [Data.List.Map.map_map] at zeroMap oneMap
  have zeroScalar := congrArg (fun values => Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area values))
    zeroMap
  have oneScalar := congrArg (fun values => Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area values))
    oneMap
  have zeroFinal : Data.Gaussian.Norm.Basic.normSq (area 0) ≤ 4 * target := zeroScalar.symm.trans_le zeroBound
  have oneFinal : Data.Gaussian.Norm.Basic.normSq (area 1) ≤ 4 * target := oneScalar.symm.trans_le oneBound
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two (area 0) (area 1)).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct zeroFinal
      oneFinal) (by decide)).trans_eq (by ring1))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.ConjugateLapAreaRequest
