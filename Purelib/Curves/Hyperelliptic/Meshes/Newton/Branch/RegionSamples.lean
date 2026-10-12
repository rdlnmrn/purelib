module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.NewtonCutPrimitiveArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalCutBalance
public import Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

public section

/-! Original branch-region requests reuse the retained Newton annuli.
The receipts retain inner boundaries, cut jumps and occurrence offsets. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionSamples

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.Newton
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalCutBalance
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests
open Purelib.Data.Rat
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces
open Purelib.Riemann.Branches.NewtonCutPrimitiveArea
open Purelib.Riemann.Branches.NewtonCutPrimitiveArea.CutSourceWord
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition
open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank
open Purelib.Topology.Mesh
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Cut.PrimitiveJumps
open Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing
open Purelib.Topology.Surface.Sewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AnnularEntry)
open Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces (OriginalAnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing (IncludedHoleSewing)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests (IncludedStemRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleRequests (IncludedHoleRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Polygon.Stokes (edgeListArea)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition.NewtonGrid (originalCellMask)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_neg)
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_le_mul_of_nonneg_left_direct add_le_add_direct)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
  {preparation : NewtonPreparation
    base.bank.toBranchCellBank} {target radius : Rational}
  {grid : NewtonGrid preparation target radius}
    {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {differential : Differential genus}

set_option genInjectivity false in
/-- The retained annulus, stem, hole and sewing requests for one original branch region.

The inner comparisons share the supplied magnitude bank and allocate explicit fractions of the requested error. -/
structure BranchRegionRequest (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (entry : Excision.AnnularEntry grid
  current) (sheet : Fin 2)
    (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (error : Fraction.Rational) (floor : Nat) where
  /-- The retained original annular faces around this branch cell. -/ outer :
    NewtonOriginalAnnularFaces.OriginalAnnularFaces grid entry.hole.index
  /-- The stem comparison request for the original branch and selected sheet. -/ stems :
    StemRequests.IncludedStemRequest bank grid.shrunk.included fixed entry.hole.index sheet (error / 4 / 10)
  /-- The doubled-hole comparison request on the retained included grid. -/ holes : HoleRequests.IncludedHoleRequest
    bank grid.shrunk.included fixed entry.hole.index (error / 4 / 10)
  /-- The actual included-hole sewing geometry. -/ geometry : HoleSewing.IncludedHoleSewing bank grid.shrunk.included
    entry.hole.index domains differential
  /-- The retained sewing comparison at the requested floor. -/ sewing : IncludedHoleSewing.Request geometry fixed
    (error / 4) floor

constructive_injectivity BranchRegionRequest

namespace BranchRegionRequest

variable {entry : AnnularEntry grid current} {sheet : Fin
  2}
  {fixed : FaceMagnitudeBank domains differential}
    {error : Rational} {floor : Nat}

/-- Prepare the actual original annulus and all positive stem, hole and sewing budgets for one branch region. -/
@[expose] def build (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (entry : Excision.AnnularEntry grid current)
  (sheet : Fin 2)
    (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (error : Fraction.Rational) (positive : 0 < error)
      (floor : Nat) :
    Curves.Hyperelliptic.Meshes.Newton.Branch.RegionSamples.BranchRegionRequest bank entry sheet fixed error floor :=
  have quarter : 0 < error / 4 := Fraction.Order.Field.div_pos_direct positive (by decide)
  have inner : 0 < error / 4 / 10 := Fraction.Order.Field.div_pos_direct quarter (by decide)
  let geometry := IncludedHoleSewing.build bank grid.shrunk.included entry.hole.index domains differential
  ⟨OriginalAnnularFaces.build grid entry.hole.index,
    IncludedStemRequest.build bank grid.shrunk.included fixed entry.hole.index sheet _ inner,
    IncludedHoleRequest.build bank grid.shrunk.included fixed entry.hole.index _ inner,
    geometry, IncludedHoleSewing.Request.build geometry fixed _ quarter floor⟩

/-- The common stage paying the retained stem, hole and sewing requests. -/
@[expose] def index (prepared : Curves.Hyperelliptic.Meshes.Newton.Branch.RegionSamples.BranchRegionRequest bank entry
  sheet fixed error floor) : Nat :=
  max (max prepared.stems.index prepared.holes.index) prepared.sewing.index

set_option genInjectivity false in
/-- The actual selected-region balance and all retained cut corrections.

Pairing, occurrence readback, inner boundary and canonical polygon are evaluated on the same supplied primitive readings
and sewn surface. -/
structure Sample (prepared : Curves.Hyperelliptic.Meshes.Newton.Branch.RegionSamples.BranchRegionRequest bank entry
  sheet fixed error floor)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
    (surface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values) where
  /-- The original selected-region cut balance on the actual sewn surface. -/ balance :
    OriginalCutBalance prepared.outer entry.region prepared.geometry surface
  /-- The retained primitive sample for every projected cut-edge pair. -/ pairing : ProjectedEdgePairing.PrimitiveSample
    balance.complete.pairing surface.energyValues
  /-- The actual cut-word occurrence-area readback. -/ readback : CutSourceWord.AreaReadback prepared.geometry.word
    surface.sewn.values
  /-- The cached signed inner-boundary area. -/ inner : Data.Gaussian.Basic.Canonical
  /-- The inner area is exactly the edge-list area of the retained inner word. -/ inner_eq : inner = Stokes.edgeListArea
    surface.energyValues balance.inner.word.edges
  /-- The cached canonical polygon area of the original resplit based walk. -/ polygon : Data.Gaussian.Basic.Canonical
  /-- The polygon retains the original walk, sheet and canonical edge valuation. -/ polygon_eq : polygon =
    RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values)
    (current.edges.indexedEdges current.vertices
      (grid.shrunk.included.resplit (bank.rows.get entry.hole.index).reference.walk (FramedBranchCellBank.baseMember
        base.bank)) sheet)

constructive_injectivity Sample

namespace Sample

variable {prepared : Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionSamples.BranchRegionRequest bank entry
  sheet fixed error floor}
  {stage : Nat} {shared : FacePrimitiveBank
    differential stage domains} {readings :
    TriangleReadings shared current.mesh}
  {surface : CachedSample current.cutPolygon.patch readings.values}

/-- Cache the original region balance, pairing and occurrence readbacks, inner boundary and canonical polygon on the
supplied readings. -/
@[expose] def build (prepared : Curves.Hyperelliptic.Meshes.Newton.Branch.RegionSamples.BranchRegionRequest bank entry
  sheet fixed error floor)
    (readings : TrianglePrimitiveReadings.TriangleReadings shared current.mesh) (surface :
      SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values) :
    prepared.Sample readings surface :=
  let balance := OriginalCutBalance.build prepared.outer entry.region prepared.geometry surface
  ⟨balance, PrimitiveSample.build balance.complete.pairing surface.energyValues,
    AreaReadback.build prepared.geometry.word surface.sewn.values,
    Stokes.edgeListArea surface.energyValues balance.inner.word.edges, rfl,
    RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values)
      (current.edges.indexedEdges current.vertices
        (grid.shrunk.included.resplit (bank.rows.get entry.hole.index).reference.walk (FramedBranchCellBank.baseMember
          base.bank)) sheet), rfl⟩

/-- The complete inner-boundary, cut-jump, pairing-defect and occurrence correction. -/
@[expose] def correction (sample : prepared.Sample readings surface) : Gaussian :=
  sample.inner + sample.pairing.jumpSum + sample.pairing.defectSum + sample.readback.correction

/-- The corrected selected-region area minus twice the retained canonical polygon area. -/
@[expose] def residual (sample : prepared.Sample readings surface) : Gaussian :=
  sample.balance.selected.area - sample.correction - (sample.polygon + sample.polygon)

/-- The retained selected-region area equals any sample of the same original cell mask. -/
theorem selected_area (sample : prepared.Sample readings surface)
    (selected : CachedSample.FaceSelection surface (NewtonGrid.originalCellMask current (base.bank.cell
      entry.hole.index))) :
    sample.balance.selected.area = selected.area :=
  sample.balance.selected.area_readback.trans selected.area_readback.symm

/-- After the common stage, the complete corrected branch-region residual fits the requested error.

The estimate combines the retained stem, doubled-hole and sewing comparisons without discarding any inner-boundary or
cut correction. -/
theorem accurate (sample : prepared.Sample readings surface) (later : prepared.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq sample.residual ≤ error := by
  let value := CanonicalEdgeValues.edgeValuation current.mesh readings.values
  let walk := grid.shrunk.included.resplit (bank.rows.get entry.hole.index).boundary
    ((base.bank.cell entry.hole.index).anchor_mem (base.bank.cell_mem entry.hole.index))
  let arrival := RootEdgeBank.target current.edges (grid.shrunk.included.resplit (bank.rows.get entry.hole.index).stem
    ((base.bank.cell entry.hole.index).anchor_mem (base.bank.cell_mem entry.hole.index))) sheet
  let lap := RetracingWords.wordArea value (current.edges.indexedEdges current.vertices walk arrival)
  let double := RetracingWords.wordArea value (current.edges.indexedEdges current.vertices walk 0 ++
    current.edges.indexedEdges current.vertices walk 1)
  have stemBound := prepared.stems.loop_area_accurate readings
    ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_left _ _).trans later))
  have oldBound {point : Data.Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Data.Gaussian.Basic.Canonical.normSq point ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact h
  have stem : Data.Gaussian.Norm.Basic.normSq (sample.polygon - lap) ≤ error / 4 / 10 :=
    (congrArg (fun polygon => Data.Gaussian.Norm.Basic.normSq (polygon - lap)) sample.polygon_eq).trans_le
      (oldBound stemBound)
  have hole : Data.Gaussian.Norm.Basic.normSq (lap + lap - double) ≤ error / 4 / 10 :=
    oldBound (prepared.holes.lap_accurate readings
      ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_left _ _).trans later)) arrival)
  have twice : Data.Gaussian.Norm.Basic.normSq ((sample.polygon - lap) + (sample.polygon - lap)) ≤ 4 * (error /
    4 / 10) :=
    ((Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct stem
        stem) (by decide))).trans_eq (by ring1)
  have branch := (Data.Gaussian.Norm.Bounds.normSq_add_le_two
    ((sample.polygon - lap) + (sample.polygon - lap)) (lap + lap - double)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct twice
        hole) (by decide))
  have equal : (sample.polygon - lap) + (sample.polygon - lap) + (lap + lap - double) =
      sample.polygon + sample.polygon - double := by ring1
  rw [equal] at branch
  have branchBound : Data.Gaussian.Norm.Basic.normSq (sample.polygon + sample.polygon - double) ≤ error / 4 :=
    branch.trans_eq ((by ring1 : 2 * (4 * (error / 4 / 10) + error / 4 / 10) = error / 4 / 10 * 10).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))
  have sewn := prepared.sewing.accurate readings surface sample.readback ((Data.Nat.Order.le_max_right _ _).trans later)
  erw [HoleRequests.resplit_hole_double_indexed bank grid.shrunk.included entry.hole.index] at sewn
  have reversed : Data.Gaussian.Norm.Basic.normSq (double - (sample.polygon + sample.polygon)) ≤ error / 4 :=
    by
    rw [show double - (sample.polygon + sample.polygon) = -(sample.polygon + sample.polygon - double) by ring1,
      Data.Gaussian.Norm.Basic.normSq_neg]
    exact branchBound
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via (sample.readback.raw - sample.readback.correction)
      double (sample.polygon + sample.polygon)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct sewn
      reversed) (by decide))
  have corrected : sample.balance.selected.area - sample.correction = sample.readback.raw - sample.readback.correction
    := by
    unfold Branch.RegionSamples.BranchRegionRequest.Sample.correction
    rw [sample.inner_eq]
    have balance := sample.balance.corrected_area sample.pairing sample.readback
    calc
      _ = sample.balance.selected.area - Stokes.edgeListArea surface.energyValues sample.balance.inner.word.edges -
          sample.pairing.jumpSum - sample.pairing.defectSum - sample.readback.correction := by ring1
      _ = _ := balance
  unfold Branch.RegionSamples.BranchRegionRequest.Sample.residual
  rw [corrected]
  exact estimate.trans_eq ((by ring1 : 2 * (error / 4 + error / 4) = error / 4 * 4).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

end Sample
end BranchRegionRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionSamples
