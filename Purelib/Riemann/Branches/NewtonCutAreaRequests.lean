module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Riemann.Branches.NewtonCutPrimitiveArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPathComparison
import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Vector.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Surface.Sewing.SewnPathAreaRequests
import Purelib.Topology.Polygon.Stokes
import Purelib.RootIsolation.State.Raw
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Polynomial.Dense.Basic
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Data.Gaussian.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Requested Newton boundary areas with explicit cut-offset corrections

The existing geometry-first Newton request pays the source polygon. A
second automatic budget pays its actual inherited sewing errors on the same
primitive bank. The resulting raw cut-edge area is small after subtracting
the retained occurrence-offset terms. Their cancellation in the global
surface formula remains a separate obligation.
-/

namespace Purelib.Riemann.Branches.NewtonCutAreaRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (edgeListArea)
open Purelib.Data.Rat.Fraction (Rational)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted (OuterPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation (AreaRequest)
open Purelib.Riemann.Branches.NewtonCutPrimitiveArea.OuterPreparation (CutComparison)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {error radius : Rational}
  {request : AreaRequest preparation
    (error / 4) radius} {index : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {annulus : AnnularFaces request.grid index} {lifted :
    LiftedPuncturedGrid request.grid.punctured}
  {region : Lifted annulus lifted} {prepared :
    OuterPreparation region} {differential
    : Fin genus}
  {domains : FaceDomainBank lifted.frames
    request.grid.faces.regulars} {floor : Nat}

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Branches in
set_option genInjectivity false in
/-- An original annular area request with its exact cut comparison and paid sewing request.

The sewing error is one quarter of the original target and retains the same differential, domains and requested stage
floor. -/
structure SewnRequest (request : Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.AreaRequest preparation (error /
  4) radius)
    {index : BranchIsolation.Data.Index branches} {annulus : Meshes.Newton.Annulus.Faces.AnnularFaces request.grid
      index}
    {lifted : LiftedPuncturedGrid request.grid.punctured} {region : Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus
      lifted}
    (prepared : Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region) (differential : Fin genus)
    (domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames request.grid.faces.regulars) (floor :
      Nat) where
  /-- The retained cut comparison from the original annular area request. -/ comparison : CutComparison prepared
    differential domains request.budget.scale
  /-- The exact quarter-target sewing request at the original stage floor. -/ sewing : CutComparison.Request comparison
    (error / 4) floor

constructive_injectivity SewnRequest

namespace SewnRequest

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Branches in
/-- Construct the original cut comparison and its quarter-target sewing request. -/
@[expose] def build (request : Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.AreaRequest preparation (error / 4)
  radius)
    {index : BranchIsolation.Data.Index branches} {annulus : Meshes.Newton.Annulus.Faces.AnnularFaces request.grid
      index}
    {lifted : LiftedPuncturedGrid request.grid.punctured} {region : Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus
      lifted}
    (prepared : Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region) (differential : Fin genus)
    (domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames request.grid.faces.regulars) (floor :
      Nat) :
    SewnRequest request prepared differential domains floor :=
  let comparison := CutComparison.ofComparison (request.compare prepared differential domains)
  ⟨comparison, CutComparison.Request.build comparison (error / 4) request.budget.positive floor⟩

/-- The retained sewing contact stage meets the original requested floor. -/
theorem floor_le (sewn : SewnRequest request prepared differential domains floor) : floor ≤ sewn.sewing.contact.index :=
  sewn.sewing.floor_le

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Topology.Surface in
/-- The sewn increment area has squared norm below the original target at every sufficient stage.

The original source area and the sewn-to-source difference each consume a quarter-target allowance; the exact two-term
estimate pays the full target. -/
theorem corrected_area_small (sewn : SewnRequest request prepared differential domains floor)
    {stage : Nat} (later : sewn.sewing.contact.index ≤ stage)
    {shared : Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank (standardDifferential differential) stage
      domains}
    {readings : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh} {surface :
      Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch readings.values}
    (sample : CutComparison.Sample sewn.comparison readings surface) :
    Data.Gaussian.Norm.Basic.normSq (sample.occurrences.raw - sample.occurrences.correction) < error := by
  have source := request.source_area_accurate sewn.comparison.original (sewn.sewing.reference_later later) readings
  rw [← sample.source_area] at source
  have difference := sample.accurate sewn.sewing later
  rw [sample.corrected_area]
  have estimate := (Norm.Bounds.normSq_add_le_two (sample.area.sewn.area - sample.area.source.area)
    sample.area.source.area).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct difference source))
  rw [sub_add_cancel] at estimate
  exact estimate.trans_eq (by
    calc
      2 * (error / 4 + error / 4) = (error / 4) * 4 := by ring1
      _ = error := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Topology.Surface in
/-- The original energy-value boundary area minus its retained occurrence correction meets the requested target. -/
theorem surface_area_small (sewn : SewnRequest request prepared differential domains floor)
    {stage : Nat} (later : sewn.sewing.contact.index ≤ stage)
    {shared : Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank (standardDifferential differential) stage
      domains}
    {readings : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh} {surface :
      Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch readings.values}
    (sample : CutComparison.Sample sewn.comparison readings surface) :
    Data.Gaussian.Norm.Basic.normSq (edgeListArea surface.energyValues sewn.comparison.word.edges -
      sample.occurrences.correction) < error := by
  rw [← sample.raw_area]
  exact sewn.corrected_area_small later sample

end SewnRequest
end Purelib.Riemann.Branches.NewtonCutAreaRequests
