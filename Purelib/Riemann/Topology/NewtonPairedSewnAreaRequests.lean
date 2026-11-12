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
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Riemann.Branches.NewtonPairedCutRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests
public import Purelib.Integration.Path.PairedOccurrenceArea
import Purelib.Tactic.Ring

public section

/-! The shared Newton and contact budgets pay the actual sewn paired
increment polygon. Raw cut-edge occurrence offsets remain separate. -/

namespace Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted (OuterPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation (AreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests.NewtonPreparation.AreaRequest
  (PairedComparison paired_source_area_accurate)
open Purelib.Riemann.Branches.NewtonPairedCutRequests (PairedCutRequest)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open _root_.Purelib.Integration.Path (PairedOccurrenceArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {error radius : Rational}
  {request : AreaRequest preparation
    (error / 4) radius} {index : Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {annulus : AnnularFaces request.grid index} {lifted :
    LiftedPuncturedGrid request.grid.punctured}
  {region : Lifted annulus lifted} {prepared :
    OuterPreparation region} {differential
    other : Fin genus}
  {domains : FaceDomainBank lifted.frames
    request.grid.faces.regulars} {floor : Nat}

open Purelib.Curves in
set_option genInjectivity false in
/-- Retain shared Newton and contact budgets for the actual sewn paired increment polygon.

The original paired primitive comparison and cut request use quarter-target allowances on the same prepared annulus and
face domains. -/
structure PairedSewnRequest (request : AreaRequest
  preparation (error / 4) radius)
    {index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {annulus :
      AnnularFaces request.grid index}
    {lifted : LiftedPuncturedGrid request.grid.punctured} {region :
      Lifted annulus lifted}
    (prepared : OuterPreparation region) (first second :
      Fin genus)
    (domains : FaceDomainBank lifted.frames
      request.grid.faces.regulars) (floor : Nat) where
  /-- The original paired Newton-annulus primitive comparison. -/ comparison :
    PairedComparison request
    prepared first second domains
  /-- The retained paired cut request joining those exact two comparison owners. -/ sewing : PairedCutRequest
    comparison.left comparison.right (error / 4) floor

constructive_injectivity PairedSewnRequest

namespace PairedSewnRequest

open Purelib.Curves in
/-- Build the paired sewn request from the same retained Newton comparison.

The original positive Newton budget supplies the contact allowance and requested numerical floor. -/
@[expose] def build (prepared : OuterPreparation region)
  (first second : Fin genus)
    (domains : FaceDomainBank lifted.frames
      request.grid.faces.regulars) (floor : Nat) :
    PairedSewnRequest request prepared first second domains floor :=
  let comparison :=
    PairedComparison.build prepared
    first second domains
  ⟨comparison, PairedCutRequest.build comparison.left comparison.right (error / 4) request.budget.positive floor⟩

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
/-- The actual sewn paired increment polygon has squared area below the requested error.

Both original triangle-reading banks and sewn surfaces are used at a permitted common stage, paying the source and
contact quarter-budgets. -/
theorem accurate (sewn : PairedSewnRequest request prepared differential other domains floor)
    {stage : Nat} (later : sewn.sewing.stage ≤ stage)
    {firstBank : FacePrimitiveBank (standardDifferential
      differential) stage domains}
    {secondBank : FacePrimitiveBank (standardDifferential other)
      stage domains}
    (firstReadings : TriangleReadings firstBank
      lifted.mesh)
    (secondReadings : TriangleReadings secondBank
      lifted.mesh)
    (firstSurface : CachedSample lifted.cutPolygon.patch firstReadings.values)
    (secondSurface : CachedSample lifted.cutPolygon.patch secondReadings.values) :
    normSq (Path.PairedIncrementArea.area (sewn.sewing.first.word.edges.map (fun edge =>
      (⟨firstSurface.sewn.values edge.finish - firstSurface.sewn.values edge.start,
        secondSurface.sewn.values edge.finish - secondSurface.sewn.values edge.start⟩ : PrimitivePoint)))) < error := by
  have references := PairedCutRequest.references_later sewn.sewing later
  have source :=
    paired_source_area_accurate
    request sewn.comparison.left sewn.comparison.right
    references.1 references.2 firstReadings secondReadings
  have difference := PairedCutRequest.accurate sewn.sewing later firstReadings
    secondReadings firstSurface secondSurface
  have estimate := (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rational) < 2)
      (Rat.Fraction.Order.Arithmetic.add_lt_add_direct difference source))
  rw [sub_add_cancel] at estimate
  exact estimate.trans_eq (by
    calc
      2 * (error / 4 + error / 4) = (error / 4) * 4 := by ring1
      _ = error := Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))

open Purelib.Curves in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
/-- The retained raw occurrence area minus its exact offset correction satisfies the same strict target.

The occurrence readback identifies this corrected area with the actual sewn increment polygon. -/
theorem corrected_area_accurate (sewn : PairedSewnRequest request prepared differential other domains floor)
    {stage : Nat} (later : sewn.sewing.stage ≤ stage)
    {firstBank : FacePrimitiveBank (standardDifferential
      differential) stage domains}
    {secondBank : FacePrimitiveBank (standardDifferential other)
      stage domains}
    (firstReadings : TriangleReadings firstBank
      lifted.mesh)
    (secondReadings : TriangleReadings secondBank
      lifted.mesh)
    (firstSurface : CachedSample lifted.cutPolygon.patch firstReadings.values)
    (secondSurface : CachedSample lifted.cutPolygon.patch secondReadings.values)
    (sample : PairedOccurrenceArea (fun vertex =>
      (⟨firstSurface.sewn.values vertex, secondSurface.sewn.values vertex⟩ : PrimitivePoint))
      sewn.sewing.first.word.edges) : normSq (sample.raw - sample.correction) < error := by
  rw [PairedOccurrenceArea.corrected sample]
  exact accurate sewn later firstReadings secondReadings firstSurface secondSurface

end PairedSewnRequest
end Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests
