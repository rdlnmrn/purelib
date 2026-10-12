module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SourceComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
public import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
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
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.VertexSewing
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Curves

open Purelib.Data

open Purelib.Riemann

open Purelib

@[expose] public section

/-!
# Uniform bounds on actual sewn cut jumps

The coarse reference and contact request fix a scalar floor before any later
face bank is sampled. At every later index the actual sewn jump is bounded
by the same cached rational, including inherited sewing errors and retained
diagonal detours. No extra local-accuracy or numerical-matching premise is
required. Absolute primitive values still need an anchor-path construction.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveReferences

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Hyperelliptic.Differentials.Basic.Differential genus} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram lifted source}
  {segments : Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank prepared.period} {differential : Fin
    genus}
  {comparison : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank.ofSegments prepared segments) differential}
  {contacts : List (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact lifted.mesh.triangulation.faces)}

set_option genInjectivity false in
/-- A uniform reference for the actual sewn cut jump, including original source bounds and contact allowance.

The source cache, path-length budget and common contact floor remain fixed for all later readings. -/
structure JumpReference (comparison : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
  (Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank.ofSegments prepared segments) differential)
    (covered : Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations contacts
      (Periods.PeriodMatrix.standardDifferential differential) comparison.domains)
    (lengthBound : Nat) where
  /-- The retained prepared contacts cover every original sewing contact. -/ coverage : ∀ contact ∈
    Topology.Surface.Sewing.SewnPrimitiveContacts.sourceContacts lifted.cutPolygon.patch.assembly, contact ∈ contacts
  /-- The original coarse reference bank on the assigned segments. -/ locals :
    Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.ReferenceBank (Periods.PeriodMatrix.standardDifferential
    differential) 0
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank.ofSegments prepared segments).assigned
      comparison.compared
  /-- The retained unit-target path request with its original length bound. -/ path :
    Topology.Surface.Sewing.SewnPathRequests.PathRequest lifted.cutPolygon.patch.assembly lengthBound 1
  /-- The actual contact request paying the path tolerance and original reference floor. -/ contactRequest :
    Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request covered path.tolerance
    locals.profile.index
  /-- The cached uniform bound for the original sewn jump. -/ bound : Normalization.InverseRootPolynomial.Coordinate
  /-- The bound is exactly twice one plus the original local-source bound. -/ bound_eq : bound = 2 * (1 + locals.bound)

constructive_injectivity JumpReference

namespace JumpReference

variable {covered : Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations contacts
  (Periods.PeriodMatrix.standardDifferential differential) comparison.domains}
  {lengthBound : Nat}

/-- Supplied references and the geometry profile are reused literally.
Only the coarse contact tolerances and their maximum are new calculations. -/
def ofReferences (covered : Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations contacts
  (Periods.PeriodMatrix.standardDifferential differential) comparison.domains)
    (coverage : ∀ contact ∈ Topology.Surface.Sewing.SewnPrimitiveContacts.sourceContacts
      lifted.cutPolygon.patch.assembly, contact ∈ contacts)
    (locals : Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences.ReferenceBank
      (Periods.PeriodMatrix.standardDifferential differential) 0
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank.ofSegments prepared segments).assigned
        comparison.compared)
    (profile : Topology.Surface.Sewing.SewnPrimitiveAccounting.Shape) (profileEq : profile =
      Topology.Surface.Sewing.SewnPrimitiveAccounting.shape lifted.cutPolygon.patch.assembly) (lengthBound : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveReferences.JumpReference comparison covered lengthBound :=
  let path := Topology.Surface.Sewing.SewnPathRequests.PathRequest.ofProfile profile profileEq lengthBound 1 (by decide)
  let contactRequest := Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request.build covered
    path.tolerance path.tolerance_positive locals.profile.index
  ⟨coverage, locals, path, contactRequest, (2 : Normalization.InverseRootPolynomial.Coordinate) * (1 + locals.bound),
    rfl⟩

/-- Every stage meeting the retained contact request also meets the original local reference floor. -/
theorem local_later (reference : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveReferences.JumpReference comparison
  covered lengthBound) {index : Nat}
    (later : reference.contactRequest.index ≤ index) : reference.locals.profile.index ≤ index :=
  reference.contactRequest.floor_le.trans later

/-- At every sufficiently late common reading, the actual original source increments satisfy the cached reference bound.
-/
theorem source_sum_bounded (reference : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveReferences.JumpReference
  comparison covered lengthBound) {index : Nat}
    (later : reference.contactRequest.index ≤ index)
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) index comparison.domains}
    (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.routed.spine.values (fun _
      route => route.sourceEdge.increment triangles.values))) ≤
      reference.locals.bound := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourValues.BranchCellBank.LiftedMesh.RouteSpine.triangle_values
    triangles prepared.routed.spine, ←
    Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourValues.FaceBank.ofSegments_corner_sum prepared segments shared]
  exact reference.locals.bounded comparison.sharedDomains
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveReferences.JumpReference.local_later reference later) shared

/-- The result concerns the original cut endpoints, not an independently
sampled period or a re-sewn substitute surface. All finer shared banks are
allowed, while the reference value, bound and contact floor stay fixed. -/
theorem bounded (reference : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveReferences.JumpReference comparison covered
  lengthBound) {index : Nat}
    (later : reference.contactRequest.index ≤ index)
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) index comparison.domains}
    (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch triangles.values)
    (routedPositive : Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.RouteSpine.Positive
      prepared.routed.spine)
    (sources : Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources lifted.cutPolygon.patch.cut
      prepared.cycle.path.cutEdges) (positive : sources.Positive)
    (length_le : prepared.cycle.path.cutEdges.length ≤ lengthBound) :
    Data.Gaussian.Norm.Basic.normSq (surface.sewn.values prepared.cycle.finish - surface.sewn.values
      prepared.cycle.start) ≤ reference.bound := open Purelib.Data.Rat in by
  have aligned := Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.RouteSpine.sources_eq
    prepared.routed.spine routedPositive sources.sources positive
    (sources.sources_project.trans prepared.cycle.path.projection_eq.symm)
  have localAccuracy := reference.contactRequest.localAccuracy_of_coverage
    reference.coverage le_rfl later triangles surface.sewn.readings
  have paid := reference.path.cached_accurate surface localAccuracy sources length_le
  have sourceBound : Data.Gaussian.Norm.Basic.normSq
    (Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.CachedSample.pathSample surface sources).value ≤
    reference.locals.bound := by
    rw [(Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.CachedSample.pathSample surface
      sources).value_eq_sources, ← aligned,
      Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.RouteSpine.source_increments]
    exact Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveReferences.JumpReference.source_sum_bounded reference later
      triangles
  have bound := (Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.CachedSample.pathSample surface
    sources).magnitude_bound prepared.cycle.path.endpoints sourceBound
  exact bound.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add paid.le le_rfl) (by decide)).trans_eq reference.bound_eq.symm)

end JumpReference
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveReferences
