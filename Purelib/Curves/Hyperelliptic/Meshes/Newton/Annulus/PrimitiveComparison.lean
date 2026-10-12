module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Geometry.Grid.Boundary.Segments
import Purelib.Polynomial.Geometry.Grid.Winding
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Paths.PreparedSegmentParentBanks
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPathComparison
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedOwnerAlignment
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

public section

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

/-!
# The actual two-lap Newton tour in the shared primitive bank

The cached outer word used by annular excision supplies the face placements.
One covered preparation starts at its actual shared-frame owner and returns
to that owner after both laps. Each differential consumes its original
parent cache and the very band retained when constructing the grid.

The bounds below control the full polygon of original triangle-source
increments. They do not identify original grid vertices with cut vertices,
or erase the offset term using projected closure alone.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {index :
    Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {annulus : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index} {lifted : Meshes.LiftedPuncturedGrid
    grid.punctured}

/-- Both laps of the original annular boundary stay on the retained Newton box boundary. -/
theorem doubleBoundary_segments (annulus : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) :
    Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary (grid.bands.box index)
      (Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.doubleBoundary annulus).path :=
  Polynomial.Geometry.Grid.Boundary.Segments.Walk.boundary_append _ _ annulus.window.boundary_segments
    annulus.window.boundary_segments

/-- The original doubled annular boundary has raw winding eight. -/
theorem doubleBoundary_winding (annulus : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) :
    Paths.PreparedPathWinding.ClearPath.rawWinding (Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.doubleBoundary
      annulus).path = 8 := by
  rw [Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.doubleBoundary, Geometry.Grid.Winding.Walk.append_winding,
    (Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces.boundary_winding annulus)]
  decide

/-- Select the actual sheet-zero root owner from the shared frame at the original annular anchor. -/
@[expose] def outerOwner (annulus : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) (lifted :
  Meshes.LiftedPuncturedGrid grid.punctured) :
    Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval (grid.bands.box index).anchor) :=
  (lifted.frames.frameAt _ (Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.anchor_onGrid annulus)).owners 0

namespace Lifted

/-- Read the excision cache instead of replaying the edge-bank transitions. -/
@[expose] def outerFaces (region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces lifted.mesh
      (Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.doubleBoundary annulus)
      ((Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.outerOwner annulus lifted)) :=
  let geometry := Meshes.GridLiftedMesh.LiftedMesh.PathFaces.ofIndexed lifted.mesh
    (Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.doubleBoundary annulus) region.outer ⟨0, region.outer_eq⟩
    (by
      rw [region.outer_eq]; exact Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments.indexedWalk_supported
        lifted.mesh (Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.doubleBoundary annulus) 0)
  ⟨(Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.anchor_onGrid annulus), 0, ⟨NamedEquivalent.refl _⟩, geometry,
    (Meshes.GridLiftedMesh.LiftedMesh.PathFaces.ofIndexed_indexed _ _ _ _ _).trans region.outer_eq⟩

/-- The prepared outer-face assignment reads back to the exact cached original excision word. -/
theorem outerFaces_indexed (region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted) :
  (Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.outerFaces region).geometry.indexed = region.outer :=
  Meshes.GridLiftedMesh.LiftedMesh.PathFaces.ofIndexed_indexed _ _ _ _ _

set_option genInjectivity false in
/-- Geometry and owner continuation are materialized once, before any
differential or later face accuracy is chosen. Generated covers are accepted. -/
structure OuterPreparation (region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted) where
  /-- The actual covered original two-lap tour from its retained initial owner. -/ covered :
    Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
    (Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.doubleBoundary annulus).path
    ((Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.outerOwner annulus lifted))
  /-- The original covered segment decomposition. -/ pieces :
    Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments covered.traced.prepared
  /-- The actual original face assignment of the covered segments. -/ assigned :
    Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments lifted.mesh pieces
  /-- The assigned word is exactly the original cached outer excision word. -/ indexed_eq : assigned.indexed =
    region.outer
  /-- The original assigned pieces retain their exact aligned owners. -/ ownersAligned : assigned.OwnersAligned
  /-- The cached original triangle-source occurrences. -/ sources : List
    (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length)
  /-- The source list is the exact projection of the original segment assignment. -/ sources_eq : sources =
    Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.AssignedSegments.sourceEdges assigned

constructive_injectivity OuterPreparation

namespace OuterPreparation

variable {region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted}

/-- Reuse the supplied original covered tour to assign its segments and retain the exact excision sources. -/
@[expose] def ofCovered (region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted)
    (covered : Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
      (Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.doubleBoundary annulus).path
      ((Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.outerOwner annulus lifted))) :
      Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region :=
  let geometry := (Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.outerFaces region)
  let pieces := Paths.PreparedPathDecomposition.CoveredTracedPath.segments covered
  let assigned := geometry.assign pieces
  ⟨covered, pieces, assigned,
    (geometry.assign_indexed pieces).trans
      (Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.outerFaces_indexed region), geometry.ownersAligned
      pieces,
    Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.AssignedSegments.sourceEdges assigned, rfl⟩

/-- Prepare the original doubled outer tour once from its actual shared-frame owner. -/
@[expose] def build (region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted) :
  Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region :=
  Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.ofCovered region
    (Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.build
    (Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.doubleBoundary annulus).path
    (Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.doubleBoundary annulus).withinAmbient
    ((Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.outerOwner annulus lifted)))

/-- The original two-lap continuation returns a root name equivalent to its retained initial owner. -/
theorem returned (prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region) :
    Nonempty (Gaussian.Equivalence.NamedEquivalent (Paths.OwnerTraceReadings.ownerName
      prepared.covered.traced.finishOwner) (Paths.OwnerTraceReadings.ownerName
      ((Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.outerOwner annulus lifted)))) :=
  ⟨Paths.PreparedPathClosure.TracedPath.rootEquivalent_of_original_even
    (RootContinuation.NewtonPuncturedGrid.NewtonBandBounds.Sample.branchState (grid.bands.entries.get
      index).selection.sample)
    prepared.covered.traced
    1 ((Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.doubleBoundary_winding annulus).trans (by decide))⟩

/-- The original assigned word starts and ends at the actual retained outer anchor. -/
theorem closed (prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region) :
    Topology.Chain.PathBoundary.PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start
      Topology.Polygon.Stokes.OrientedEdge.finish prepared.assigned.indexed region.outerAnchor region.outerAnchor := by
  rw [prepared.indexed_eq]
  exact region.outer_closed

/-- The source occurrences project to the literal two-lap excision word. -/
theorem sources_project (prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation
  region) :
    prepared.sources.map (fun source => source.project lifted.mesh.triangulation.faces) = region.outer := by
  rw [prepared.sources_eq]
  exact (Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.AssignedSegments.sourceEdges_project
    prepared.assigned).trans prepared.indexed_eq

/-- Read the selected differential's original Newton band from the retained grid entry. -/
@[expose] def band (_prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region)
  (differential : Fin genus) :=
  (grid.bands.entries.get index).forDifferential differential

set_option genInjectivity false in
/-- The original whole-path parent list is retained alongside its split
caches, comparisons, and the common Newton reference stage. -/
structure Comparison (prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region)
  (differential : Fin genus)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars)
      (tolerance : Fraction.Rational) where
  /-- The original whole-path parent cache for the selected differential and sheet. -/ parents :
    Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache prepared.covered
    (Periods.PeriodMatrix.standardDifferential differential) 0
  /-- The dependent original split-parent caches. -/ caches :
    Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments.ParentCaches
    (Periods.PeriodMatrix.standardDifferential differential) 0 prepared.pieces
  /-- The split caches reuse the exact retained original whole-path parent list. -/ parents_eq :
    Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments.ParentCaches.parents caches =
    parents.parents
  /-- The actual original assigned-segment comparisons. -/ compared :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons
    (Periods.PeriodMatrix.standardDifferential differential) 0 prepared.assigned
  /-- The comparisons use the supplied original shared domain bank. -/ shared :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.UsesDomains domains
    (Periods.PeriodMatrix.standardDifferential differential) 0 prepared.assigned compared
  /-- The original Newton reference bank with its retained tolerance and actual band. -/ reference :
    Hyperelliptic.Meshes.PuncturedGrid.NewtonPathComparison.NewtonReferenceBank (prepared.band differential) tolerance
    prepared.assigned compared

constructive_injectivity Comparison

namespace Comparison

variable {prepared : Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation
  region} {differential : Fin genus}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
    {tolerance : Fraction.Rational}

/-- Build the original whole-path parent cache once, split that exact cache and prepare the retained Newton references.
-/
@[expose] def build (prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region)
  (differential : Fin genus)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars)
      (positive : 0 < tolerance) :
    Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared differential
      domains tolerance :=
  let parents := Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache.build prepared.covered
    (Periods.PeriodMatrix.standardDifferential differential) 0
  let equal := parents.parents_eq.trans (Paths.PreparedSegmentParentBanks.PreparedPath.CoveredSegments.parents_eq _ _
    prepared.pieces).symm
  let caches := Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments.ParentCaches.build _
    _ prepared.pieces parents.parents equal parents.covered
  let compared := Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.build
    domains _ _ prepared.assigned caches prepared.ownersAligned
  { parents := parents
    caches := caches
    parents_eq :=
      Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments.ParentCaches.build_parents
      prepared.pieces parents.parents equal parents.covered
    compared := compared
    shared :=
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.build_usesDomains
      domains _ _ prepared.assigned caches prepared.ownersAligned
    reference := Hyperelliptic.Meshes.PuncturedGrid.NewtonPathComparison.NewtonReferenceBank.build (prepared.band
      differential) positive prepared.assigned compared
      (Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.doubleBoundary_segments annulus) }

/-- The comparison-bank parents are exactly the retained original whole-path parents. -/
theorem original_parents (comparison :
  Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared differential
  domains tolerance) :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.parents
      (Periods.PeriodMatrix.standardDifferential differential) 0 prepared.assigned comparison.compared =
      comparison.parents.parents :=
  (Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.parents_eq _ _ _
    _).trans
    ((Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments.ParentCaches.parents_eq
      comparison.caches).symm.trans comparison.parents_eq)

/-- The full original triangle-source polygon meets the retained Newton area bound using its actual word length. -/
theorem source_area_bound (comparison :
  Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared differential
  domains tolerance)
    {stage : Nat} (later : comparison.reference.index ≤ stage)
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea
      (prepared.sources.map (fun source => source.increment readings.values))) ≤
      4 * ((region.outer.length : Fraction.Rational) ^ 2 * (3 * tolerance + 4 * (target / 16))) ^ 2 := by
  have bounded := comparison.reference.source_area_bound comparison.shared later readings
  rw [prepared.indexed_eq] at bounded
  rw [prepared.sources_eq]
  exact bounded

/-- The complete original source trace meets the Newton bound with the supplied anchor term retained explicitly. -/
theorem source_trace_bound (comparison :
  Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared differential
  domains tolerance) (anchor : Gaussian.Basic.Canonical)
    {stage : Nat} (later : comparison.reference.index ≤ stage)
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.traceArea anchor
      (prepared.sources.map (fun source => source.increment readings.values))) ≤
      8 * ((region.outer.length : Fraction.Rational) ^ 2 * (3 * tolerance + 4 * (target / 16))) ^ 2 +
        8 * Data.Gaussian.Norm.Basic.normSq anchor * ((region.outer.length : Fraction.Rational) ^ 2 * (3 * tolerance
          + 4 * (target / 16))) := by
  have bounded := comparison.reference.source_trace_bound anchor comparison.shared later readings
  rw [prepared.indexed_eq] at bounded
  rw [prepared.sources_eq]
  exact bounded

end Comparison
end OuterPreparation
end Lifted
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
