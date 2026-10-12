module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedOccurrenceArea
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedBalance
public import Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Branches.NewtonCutPrimitiveArea
import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Riemann.Branches.NewtonPairedCutRequests
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance.AllHoleExcision

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance.AllHoleExcision.SewnAnnulus

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedBalance.AllHoleExcision.SewnAnnulus

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison

open Purelib.Integration.Path

open Purelib.Integration.Path.PairedOccurrenceArea
open _root_.Purelib.Integration.Path renaming PairedOccurrenceArea -> PairedOccurrenceArea

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests

open Purelib.Riemann.Topology.NewtonSewnExcision

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing

open Purelib.Topology.Surface.Sewing

public section

/-! The actual selected annular triangles retain their paired inner area,
cut jumps, defects and occurrence offsets in one cached correction. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedTriangle PrimitivePoint edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation (AreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted (OuterPreparation)
open Purelib.Riemann.Branches.NewtonPairedCutRequests (PairedCutRequest)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (SewnAnnulus)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus (CutBalance)
open Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests (PairedSewnRequest)
open _root_.Purelib.Integration.Path (PairedOccurrenceArea)
open Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing (PrimitiveSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {error
    radius : Rational}
  {request : AreaRequest preparation
    (error / 4) radius} {lifted : LiftedPuncturedGrid request.grid.punctured}
  {differential other : Fin genus} {domains :
    FaceDomainBank lifted.frames
    request.grid.faces.regulars} {stage floor : Nat}
  {shared : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential) stage domains}
  {readings : TriangleReadings shared
    lifted.mesh} {surface : CachedSample lifted.cutPolygon.patch
    readings.values}
  {otherShared : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential other) stage domains}
  {otherReadings : TriangleReadings
    otherShared lifted.mesh}
  {otherSurface : CachedSample lifted.cutPolygon.patch
    otherReadings.values}

set_option genInjectivity false in
/-- The actual paired annular triangle area and complete retained cut correction.

The original inner area, paired jumps, defects and occurrence offsets remain explicit in the cached residual. -/
structure AnnularSample (annulus : AllHoleExcision.SewnAnnulus surface) (prepared : Lifted.OuterPreparation
  annulus.source.region)
    (requested : NewtonPairedSewnAreaRequests.PairedSewnRequest request prepared differential other domains floor)
    (otherSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch otherReadings.values) where
  /-- The exact retained cut balance of the original annulus and requested outer word. -/ balance :
    CutBalance annulus prepared requested.sewing.first.word
  /-- The actual paired occurrence-area sample on the original sewn outer word. -/ outer :
    Integration.Path.PairedOccurrenceArea (fun vertex =>
    (⟨surface.sewn.values vertex, otherSurface.sewn.values vertex⟩ : Stokes.PrimitivePoint))
      requested.sewing.first.word.edges
  /-- The retained primitive sample on the actual complete projected edge pairing. -/ paired :
    ProjectedEdgePairing.PrimitiveSample balance.complete.pairing (fun vertex =>
    (⟨surface.sewn.values vertex, otherSurface.sewn.values vertex⟩ : Stokes.PrimitivePoint))
  /-- The cached paired area of the original inner boundary word. -/ innerArea : Data.Gaussian.Basic.Canonical
  /-- The inner-area cache is exactly the original inner word's area under both retained sewn readings. -/ innerArea_eq
    : innerArea = Stokes.edgeListArea (fun vertex =>
    (⟨surface.sewn.values vertex, otherSurface.sewn.values vertex⟩ : Stokes.PrimitivePoint)) balance.inner.word.edges
  /-- The cached paired boundary area of the actual selected annular triangles. -/ selectedArea :
    Data.Gaussian.Basic.Canonical
  /-- The selected-area cache is exactly the boundary area of the original retained triangle selection. -/
    selectedArea_eq : selectedArea = Stokes.edgeListArea (fun vertex =>
    (⟨surface.sewn.values vertex, otherSurface.sewn.values vertex⟩ : Stokes.PrimitivePoint))
    (annulus.selected.triangles.flatMap OrientedTriangle.boundary)
  /-- The cached complete inner-boundary, jump, defect and occurrence-offset correction. -/ correction :
    Data.Gaussian.Basic.Canonical
  /-- The correction cache is exactly the sum of the retained original inner area, paired jumps, defects and outer
    occurrence correction. -/ correction_eq : correction = innerArea + paired.jumpSum + paired.defectSum +
    outer.correction

constructive_injectivity AnnularSample

namespace AnnularSample

variable {annulus : SewnAnnulus surface} {prepared :
  OuterPreparation annulus.source.region}
  {requested : PairedSewnRequest request prepared differential
    other domains floor}

/-- Cache the actual paired annular area and all original cut contributions on the supplied sewn samples. -/
@[expose] def build (annulus : AllHoleExcision.SewnAnnulus surface) (prepared : Lifted.OuterPreparation
  annulus.source.region)
    (requested : NewtonPairedSewnAreaRequests.PairedSewnRequest request prepared differential other domains floor)
    (otherSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch otherReadings.values) :
    Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests.AnnularSample annulus prepared requested otherSurface
      :=
  let primitive := fun vertex => (⟨surface.sewn.values vertex, otherSurface.sewn.values vertex⟩ : Stokes.PrimitivePoint)
  let balance := CutBalance.build annulus prepared requested.sewing.first.word
  let outer := PairedOccurrenceArea.build primitive requested.sewing.first.word.edges
  let paired := PrimitiveSample.build balance.complete.pairing primitive
  let innerArea := Stokes.edgeListArea primitive balance.inner.word.edges
  let selectedArea := Stokes.edgeListArea primitive (annulus.selected.triangles.flatMap OrientedTriangle.boundary)
  ⟨balance, outer, paired, innerArea, rfl, selectedArea, rfl,
    innerArea + paired.jumpSum + paired.defectSum + outer.correction, rfl⟩

/-- The selected annular area minus its complete retained correction equals the actual corrected outer occurrence area.
-/
theorem corrected_eq (sample : Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests.AnnularSample annulus
  prepared requested otherSurface) :
    sample.selectedArea - sample.correction = sample.outer.raw - sample.outer.correction := by
  rw [sample.selectedArea_eq, CutBalance.paired_area_balance sample.balance _ sample.paired,
    sample.correction_eq, sample.innerArea_eq, sample.outer.raw_eq]
  ring1

/-- At every stage meeting the original paired sewing request, the actual corrected annular area satisfies its target.
-/
theorem accurate (sample : Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests.AnnularSample annulus prepared
  requested otherSurface)
    (later : requested.sewing.stage ≤ stage) : Data.Gaussian.Norm.Basic.normSq (sample.selectedArea -
      sample.correction) < error := by
  rw [sample.corrected_eq]
  exact PairedSewnRequest.corrected_area_accurate requested later readings otherReadings surface otherSurface
    sample.outer

end AnnularSample
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests
