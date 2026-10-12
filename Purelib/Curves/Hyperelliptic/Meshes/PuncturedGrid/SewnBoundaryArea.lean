module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Surface.Sewing.SewnPathArea
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences
public import Purelib.Topology.Surface.Sewing.SewnPathAreaRequests
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Purelib.Topology.Surface.Sewing.VertexSewing
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Normalization

open Purelib.Riemann.Periods

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnPathArea

open Purelib.Topology.Surface.Sewing.SewnPathArea.PathSources.Sample

open Purelib.Topology.Surface.Sewing.SewnPathAreaRequests

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces

@[expose] public section

/-!
# Requested full boundary area on the actual shared primitive bank

The existing coarse boundary reference fixes the source magnitude. An
automatic contact request then pays the entire cumulative-area discrepancy,
including all inherited sewing offsets. The numerical surface, its source
occurrences, and the original primitive bank are reused unchanged.
-/

open Purelib.Data

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBoundaryArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms.LiftedPuncturedGrid (BoundaryProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks (ContactPreparations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks (FaceBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison (PrimitiveBank)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceContact)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPathAreaRequests (PathAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences (BoundaryReference)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {source :
    Differential genus} {boundary :
    BoundaryProgram lifted
    source}
  {segments : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank boundary.program.period}
    {differential : Fin genus}
  {comparison : PrimitiveBank
    (FaceBank.ofSegments boundary.program segments)
    differential}
  {contacts : List (SourceContact
    lifted.mesh.triangulation.faces)}
  {covered : ContactPreparations contacts
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential) comparison.domains}

set_option genInjectivity false in
/-- A paid complete boundary-area comparison on the original shared primitive bank.

The original coarse reference supplies the magnitude and assembly profile, while one retained contact request pays all
cumulative sewing offsets. -/
structure BoundaryAreaRequest (reference : BoundaryPrimitiveReferences.BoundaryReference boundary comparison covered)
  (target : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The retained full-path area budget on the original assembly, boundary count and coarse magnitude. -/ budget :
    SewnPathAreaRequests.PathAreaRequest lifted.cutPolygon.patch.assembly boundary.count
    (2 * reference.reference.locals.profile.total) target
  /-- The covered contact request above both the caller floor and original boundary-reference stage. -/ contactRequest :
    ContactPreparations.Request covered budget.path.tolerance
    (max floor reference.reference.contactRequest.index)

constructive_injectivity BoundaryAreaRequest

namespace BoundaryAreaRequest

variable {reference : BoundaryReference
  boundary comparison covered} {target : Coordinate} {floor : Nat}

/-- Reuse the original boundary reference and assembly profile to prepare the requested full cumulative area comparison.
-/
def build (reference : BoundaryPrimitiveReferences.BoundaryReference boundary comparison covered) (target :
  InverseRootPolynomial.Coordinate) (positive : 0 < target)
    (floor : Nat) : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBoundaryArea.BoundaryAreaRequest reference target
      floor :=
  let budget := PathAreaRequest.ofProfile reference.reference.path.profile reference.reference.path.profile_eq
    boundary.count (2 * reference.reference.locals.profile.total) target
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) reference.reference.locals.total_nonnegative) positive
  ⟨budget, ContactPreparations.Request.build covered budget.path.tolerance budget.path.tolerance_positive
    (max floor reference.reference.contactRequest.index)⟩

/-- The retained boundary-area contact request meets the original caller floor. -/
theorem floor_le (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBoundaryArea.BoundaryAreaRequest reference
  target floor) : floor ≤ request.contactRequest.index :=
  (Nat.Order.le_max_left _ _).trans request.contactRequest.floor_le

/-- Any stage paying the retained area request also pays the original boundary reference. -/
theorem reference_later (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBoundaryArea.BoundaryAreaRequest
  reference target floor) {index : Nat}
    (later : request.contactRequest.index ≤ index) : reference.reference.contactRequest.index ≤ index :=
  (Nat.Order.le_max_right _ _).trans (request.contactRequest.floor_le.trans later)

/-- The actual cached sewn and source path areas satisfy the original target at every paid contact stage. -/
theorem accurate (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBoundaryArea.BoundaryAreaRequest reference
  target floor) {index : Nat}
    (later : request.contactRequest.index ≤ index)
    {shared : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) index comparison.domains}
    (triangles : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) (surface :
      SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch triangles.values)
    (area : PathSources.Sample.AreaSample
      (CachedSample.pathSample surface boundary.sources)) : Data.Gaussian.Norm.Basic.normSq (area.sewn.area -
        area.source.area) < target := by
  have locallyAccurate := request.contactRequest.localAccuracy_of_coverage reference.reference.coverage le_rfl
    later triangles surface.sewn.readings
  have small := request.budget.path.cached_accurate surface locallyAccurate boundary.sources boundary.count_eq.symm.le
  exact request.budget.accurate area boundary.count_eq.symm
    (reference.source_normSum_bounded (request.reference_later later) triangles) small

/-- This is the cached area consumed by the cut-word and period formula, compared to the full polygon of the very same
shared source increments. -/
theorem boundary_accurate (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBoundaryArea.BoundaryAreaRequest
  reference target floor) {index : Nat}
    (later : request.contactRequest.index ≤ index)
    {shared : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) index comparison.domains}
    (triangles : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) (surface :
      SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch triangles.values)
    (area : PathSources.Sample.AreaSample
      (CachedSample.pathSample surface boundary.sources)) : Data.Gaussian.Norm.Basic.normSq
        (surface.boundaryArea - area.source.area) < target := by
  rw [← CachedSample.boundary_pathArea surface boundary.sources area]
  exact request.accurate later triangles surface area

/-- The actual sewn boundary area agrees with the full polygon of its original shared source increments within the
retained target. -/
theorem source_polygon_accurate (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBoundaryArea.BoundaryAreaRequest reference target floor) {index : Nat}
    (later : request.contactRequest.index ≤ index)
    {shared : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) index comparison.domains}
    (triangles : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) (surface :
      SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch triangles.values) :
    Data.Gaussian.Norm.Basic.normSq (surface.boundaryArea - IncrementArea.pathArea
      (boundary.sources.sources.map (fun source => source.increment triangles.values))) < target := by
  let area := AreaSample.build
    (CachedSample.pathSample surface boundary.sources)
  have estimate := request.boundary_accurate later triangles surface area
  rw [AreaSample.source_path area] at estimate
  exact estimate

end BoundaryAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBoundaryArea
