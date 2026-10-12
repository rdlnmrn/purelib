module
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourNorms
import Purelib.Topology.Surface.Sewing.SewnBoundaryMagnitude
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
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveReferences

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourNorms

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourValues.BranchCellBank.LiftedMesh

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

open Purelib.Riemann.Periods

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut.JumpPaths

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnBoundaryMagnitude

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces

public section

/-!
# Uniform anchored magnitudes at every cut-boundary endpoint

One complete boundary preparation and one coarse reference bank control all
prefixes of every sufficiently fine shared sewn surface. The cached bound
pays diagonal detours, the full boundary length and all inherited sewing
errors. Endpoints do not acquire independent integrations or root owners.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms.LiftedPuncturedGrid (BoundaryProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks (ContactPreparations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathPrimitiveReferences (ReferenceBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutCycleProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks (FaceBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison (PrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveReferences (JumpReference)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceContact sourceContacts)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting (Shape shape)
open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes (BoundarySplit)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)

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

set_option genInjectivity false in
/-- A fixed original boundary-reference bank controlling every actual cut-boundary endpoint relative to its retained
anchor.

The cached magnitude pays the original boundary length, diagonal detours and inherited sewing errors at all sufficient
later stages. -/
structure BoundaryReference (boundary : LiftedPuncturedGrid.BoundaryProgram lifted source)
    {segments : PeriodSegmentBanks.SegmentBank boundary.program.period}
    (comparison : PeriodPrimitiveComparison.PrimitiveBank (FaceBank.ofSegments boundary.program segments) differential)
    (covered : ContactBanks.ContactPreparations contacts (PeriodMatrix.standardDifferential differential)
      comparison.domains) where
  /-- The retained jump-reference request on the actual original segment and contact banks. -/ reference :
    PrimitiveReferences.JumpReference comparison covered boundary.count
  /-- The cached stage-independent anchored boundary magnitude ceiling. -/ bound : InverseRootPolynomial.Coordinate
  /-- The cached ceiling is exactly the original boundary-count and local-reference norm-sum formula. -/ bound_eq :
    bound = 2 * (1 + 2 * (boundary.count : InverseRootPolynomial.Coordinate) * reference.locals.profile.total)

constructive_injectivity BoundaryReference

namespace BoundaryReference

variable {covered : ContactPreparations contacts
  (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential) comparison.domains}

/-- Reuse the original local reference bank, actual contact coverage and retained sewing shape to cache the complete
boundary magnitude ceiling. -/
@[expose] def ofReferences (covered : ContactBanks.ContactPreparations contacts (PeriodMatrix.standardDifferential
  differential) comparison.domains)
    (coverage : ∀ contact ∈ SewnPrimitiveContacts.sourceContacts lifted.cutPolygon.patch.assembly, contact ∈ contacts)
    (locals : PathPrimitiveReferences.ReferenceBank (PeriodMatrix.standardDifferential differential) 0
      (FaceBank.ofSegments boundary.program segments).assigned comparison.compared)
    (profile : SewnPrimitiveAccounting.Shape) (profileEq : profile = SewnPrimitiveAccounting.shape
      lifted.cutPolygon.patch.assembly) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences.BoundaryReference boundary comparison
      covered :=
  let reference := JumpReference.ofReferences covered coverage locals profile profileEq boundary.count
  ⟨reference, 2 * (1 + 2 * Aggregate.countCoordinate boundary.count * locals.profile.total),
    by rw [Aggregate.countCoordinate_eq]; rfl⟩

/-- The actual retained boundary source increments have squared-norm sum at most twice the original local-reference
total. -/
theorem source_normSum_bounded (bounded :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences.BoundaryReference boundary comparison covered)
  {index : Nat}
    (later : bounded.reference.contactRequest.index ≤ index)
    {shared : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) index comparison.domains}
    (triangles : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) :
    Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum (boundary.sources.sources.map (fun source => source.increment
      triangles.values)) ≤
      2 * bounded.reference.locals.profile.total := by
  have projected := boundary.program.cycle.path.projection_eq
  rw [boundary.edges_eq] at projected
  have aligned := RouteSpine.sources_eq boundary.program.routed.spine boundary.positive boundary.sources.sources
    boundary.sources_positive
    (boundary.sources.sources_project.trans projected.symm)
  rw [← aligned, RouteSpine.source_increments, RouteSpine.triangle_values triangles boundary.program.routed.spine]
  exact (FaceBank.ofSegments_norm_sum boundary.program segments shared).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (bounded.reference.locals.normSum_bounded comparison.sharedDomains (bounded.reference.local_later later) shared)
        (by decide))

/-- The cached original boundary magnitude ceiling is strictly positive. -/
theorem bound_positive (bounded :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences.BoundaryReference boundary comparison covered) :
  0 < bounded.bound := by
  have nonnegative : (0 : InverseRootPolynomial.Coordinate) ≤ 2 * (boundary.count : InverseRootPolynomial.Coordinate) *
    bounded.reference.locals.profile.total :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))
      bounded.reference.locals.total_nonnegative
  have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 1)
    (2 * (boundary.count : InverseRootPolynomial.Coordinate) * bounded.reference.locals.profile.total)
  rw [zero_add] at shifted
  rw [bounded.bound_eq]
  exact Fraction.Order.Arithmetic.mul_pos_direct (by decide) (nonnegative.trans_lt shifted)

/-- Every actual cut-boundary prefix endpoint satisfies the fixed anchored magnitude ceiling at sufficiently late shared
stages. -/
theorem prefix_bounded (bounded :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences.BoundaryReference boundary comparison covered)
  {index : Nat}
    (later : bounded.reference.contactRequest.index ≤ index)
    {shared : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) index comparison.domains}
    (triangles : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) (surface :
      SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch triangles.values)
    (first last : List (Stokes.OrientedEdge lifted.cutPolygon.patch.cut.count))
    (equal : first ++ last = lifted.cutPolygon.patch.cut.boundary) {finish : Fin lifted.cutPolygon.patch.cut.count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish first lifted.cutPolygon.patch.cut.anchor
      finish) :
    Data.Gaussian.Norm.Basic.normSq (surface.sewn.values finish - surface.sewn.values
      lifted.cutPolygon.patch.cut.anchor) ≤ bounded.bound := by
  have localAccuracy := bounded.reference.contactRequest.localAccuracy_of_coverage
    bounded.reference.coverage le_rfl later triangles surface.sewn.readings
  have paid := bounded.reference.path.cached_accurate surface localAccuracy boundary.sources boundary.count_eq.symm.le
  have estimate := PathSources.Sample.prefix_magnitude_bound (CachedSample.pathSample surface boundary.sources) first
    last equal path
    (bounded.source_normSum_bounded later triangles)
  have total := estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add paid.le le_rfl)
    (by decide))
  have countEq := congrArg (fun count : Nat => (count : InverseRootPolynomial.Coordinate)) boundary.count_eq
  exact total.trans_eq (by rw [bounded.bound_eq, countEq]; ring1)

/-- Both kinds of exposed endpoint are controlled relative to the retained cut anchor, not an assumed normalization of
the original local primitives. -/
theorem start_bounded (bounded : Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences.BoundaryReference
  boundary comparison covered) {index : Nat}
    (later : bounded.reference.contactRequest.index ≤ index)
    {shared : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) index comparison.domains}
    (triangles : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) (surface :
      SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch triangles.values)
    (edge : Stokes.OrientedEdge lifted.cutPolygon.patch.cut.count) (member : edge ∈
      lifted.cutPolygon.patch.cut.boundary) :
    Data.Gaussian.Norm.Basic.normSq (surface.sewn.values edge.start - surface.sewn.values
      lifted.cutPolygon.patch.cut.anchor) ≤ bounded.bound := by
  let selected := BoundarySplit.select edge lifted.cutPolygon.patch.cut.boundary member
  have estimate := bounded.prefix_bounded later triangles surface selected.split.before (selected.split.edge ::
    selected.split.after)
    selected.split.equation.symm (BoundarySplit.before_path selected.split lifted.cutPolygon.patch.cut.closed)
  rw [selected.edge_eq] at estimate
  exact estimate

/-- Every actual cut-boundary edge's final endpoint satisfies the fixed magnitude bound relative to the retained cut
anchor. -/
theorem finish_bounded (bounded :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences.BoundaryReference boundary comparison covered)
  {index : Nat}
    (later : bounded.reference.contactRequest.index ≤ index)
    {shared : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) index comparison.domains}
    (triangles : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) (surface :
      SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch triangles.values)
    (edge : Stokes.OrientedEdge lifted.cutPolygon.patch.cut.count) (member : edge ∈
      lifted.cutPolygon.patch.cut.boundary) :
    Data.Gaussian.Norm.Basic.normSq (surface.sewn.values edge.finish - surface.sewn.values
      lifted.cutPolygon.patch.cut.anchor) ≤ bounded.bound := by
  let selected := BoundarySplit.select edge lifted.cutPolygon.patch.cut.boundary member
  have equal : (selected.split.before ++ [selected.split.edge]) ++ selected.split.after =
    lifted.cutPolygon.patch.cut.boundary := by
    rw [Data.List.Append.append_assoc]
    exact selected.split.equation.symm
  have estimate := bounded.prefix_bounded later triangles surface (selected.split.before ++ [selected.split.edge])
    selected.split.after
    equal (BoundarySplit.through_path selected.split lifted.cutPolygon.patch.cut.closed)
  rw [selected.edge_eq] at estimate
  exact estimate

end BoundaryReference
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrimitiveReferences
