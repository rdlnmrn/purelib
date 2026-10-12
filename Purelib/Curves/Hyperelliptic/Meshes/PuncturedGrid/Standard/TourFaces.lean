module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedOwnerAlignment
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.JumpPaths
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Riemann.Paths.PreparedPathWinding
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Branches.BranchGridPaths
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Topology.PreparedCycleModels

open Purelib

open Purelib.Approximation

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Branches.BranchGridPaths

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments

open Purelib.Geometry

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Riemann

open Purelib.Riemann.Branches

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedOwnerClosedBridges

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathDecomposition

open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath

open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments

open Purelib.Riemann.Paths.PreparedPathWinding

open Purelib.Riemann.Readings.PreparedBoundaryClosure

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.Topology

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.RootIsolation.State

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut.JumpPaths

@[expose] public section

/-!
# Original A/B tour geometry in the shared lifted face bank

The retained owner-closed A/B tours are split on the existing framed grid.
One classification identifies their original starting owner in the shared
frame. Actual edge transport then supplies a closed indexed word and face
assignments for every occurrence. Any retained covered preparation of that
very split path enters the existing local primitive comparisons, preserving
its parent caches and all sheet handoffs.

This is the geometric/owner interface for standard-tour comparison, not yet
an intersection theorem, a cut-chain spanning theorem, or equality with the
legacy independently seeded period names. No new period stream is defined.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerSelection)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments (ParentCaches)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (PathFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments (AssignedSegments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments (Comparisons)
open Purelib.Topology.Surface.Cut.JumpPaths.CutPath (Supported)
open Purelib.Curves.Hyperelliptic.Branches.BranchGridPaths.Grid (splitTour splitTour_winding)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid (branchGrid_aTour branchGrid_bTour)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid.Grid (ContainsTourVertices)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments (walkFaces walkFaces_indexed)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearPath (rawWinding)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}

set_option genInjectivity false in
/-- The selected shared-frame index certifies the original owner. Face lookups and later analytic requests reuse this
one materialized selection. -/
structure OwnerWalkFaces (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces)
    {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk base.bank.grid start finish)
    (owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)) where
  /-- The retained starting point is an actual vertex of the original grid. -/ first :
    Polynomial.Geometry.Grid.FromStates.ContainsVertex
    base.bank.grid start
  /-- The cached shared-frame sheet of the actual incoming owner. -/ sheet : Fin 2
  /-- The original incoming root name is operationally equivalent to this exact retained frame owner. -/ aligned :
    Nonempty (Gaussian.Equivalence.NamedEquivalent
    (OwnerTraceReadings.ownerName owner) (OwnerTraceReadings.ownerName ((frames.frameAt start first).owners sheet)))
  /-- The cached face assignments for every occurrence of the actual grid walk. -/ geometry : LiftedMesh.PathFaces mesh
    walk.path
  /-- The assigned indexed edges are exactly those obtained from the retained walk and selected sheet. -/ indexed_eq :
    geometry.indexed = edges.indexedEdges vertices walk sheet

constructive_injectivity OwnerWalkFaces

namespace OwnerWalkFaces

variable {start finish : Purelib.Data.Gaussian.Basic.Canonical} {walk : Purelib.Polynomial.Geometry.Grid.Walks.Walk
  base.bank.grid start finish}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}

/-- Attach actual walk-face geometry to a supplied retained starting-sheet agreement. -/
def ofSheet (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (walk : Walks.Walk base.bank.grid start finish) (first : Polynomial.Geometry.Grid.FromStates.ContainsVertex
      base.bank.grid start)
    (sheet : Fin 2) (aligned : Nonempty (Gaussian.Equivalence.NamedEquivalent
      (OwnerTraceReadings.ownerName owner) (OwnerTraceReadings.ownerName ((frames.frameAt start first).owners sheet))))
        : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces mesh walk
        owner :=
  ⟨first, sheet, aligned, SkeletonFaceAssignments.walkFaces mesh walk sheet, SkeletonFaceAssignments.walkFaces_indexed
    mesh walk sheet⟩

/-- Reuse a cached owner selection when constructing the actual walk-face assignments. -/
def ofSelection (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (walk : Walks.Walk base.bank.grid start finish) (first : Polynomial.Geometry.Grid.FromStates.ContainsVertex
      base.bank.grid start)
    (selection : RootOwnerFrames.OwnerSelection (frames.frameAt start first).owners owner) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces mesh walk owner :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces.ofSheet mesh walk
    first selection.index ⟨selection.equivalent⟩

/-- Classify the incoming owner once and cache its actual walk-face assignments. -/
def build (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (walk : Walks.Walk base.bank.grid start finish) (first : Polynomial.Geometry.Grid.FromStates.ContainsVertex
      base.bank.grid start)
    (owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces mesh walk owner :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces.ofSelection mesh walk
    first ((frames.frameAt start first).select owner)

/-- The retained indexed face word has exactly the original walk's edge count. -/
theorem count (faces : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces
  mesh walk owner) : faces.geometry.indexed.length = walk.edgeCount := by
  rw [faces.indexed_eq, edges.indexedEdges_length]

/-- Every retained indexed edge occurrence belongs to an actual lifted triangle in one orientation. -/
theorem supported (faces :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces mesh walk owner) :
    CutPath.Supported (Stokes.triangleEdgeOccurrences mesh.triangulation.faces) faces.geometry.indexed := by
  rw [faces.indexed_eq]
  exact SkeletonFaceAssignments.indexedWalk_supported mesh walk faces.sheet

/-- A coordinate loop closes on its original root sheet only after paying the actual even-winding obligation. Canonical
A and B below discharge it. -/
theorem closed {point : Data.Gaussian.Basic.Canonical} {walk : Walks.Walk base.bank.grid point point}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval point)} (faces :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces mesh walk owner)
    (turns : Int) (winding : ClearPath.rawWinding walk.path = 8 * turns) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish faces.geometry.indexed
      (vertices.index point faces.first faces.sheet) (vertices.index point faces.first faces.sheet) := by
  rw [faces.indexed_eq]
  exact (edges.indexedEdges_endpoints vertices walk faces.first faces.first faces.sheet).castFinish
    (congrArg (vertices.index point faces.first)
      (RootEdgeBank.target_even edges (BranchCellBank.referenceAt base.bank.toBranchCellBank point faces.first).toLoop
        walk faces.first turns winding faces.sheet))

variable {prepared : Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath walk.path owner}

/-- Attach geometry to the supplied preparation, with no re-preparation. -/
def assign (faces : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces mesh
  walk owner) (pieces : PreparedPath.CoveredSegments prepared) : PreparedFaceSegments.AssignedSegments mesh pieces :=
  AssignedSegments.build pieces faces.geometry

/-- Assigning the supplied covered segments preserves the actual indexed face word. -/
theorem assign_indexed (faces :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces mesh walk owner)
  (pieces : PreparedPath.CoveredSegments prepared) :
    (faces.assign pieces).indexed = faces.geometry.indexed := AssignedSegments.build_indexed pieces faces.geometry

/-- The covered segments retain the incoming-owner alignments induced by the original selected sheet. -/
theorem ownersAligned (faces :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces mesh walk owner)
  (pieces : PreparedPath.CoveredSegments prepared) :
    (faces.assign pieces).OwnersAligned :=
  AssignedSegments.ownersAligned_of_indexed mesh walk faces.sheet faces.first (faces.assign pieces)
    ((faces.assign_indexed pieces).trans faces.indexed_eq) faces.aligned

/-- The shared analytic bank consumes the supplied actual parent caches. In particular selecting a surface face does not
acquire a replacement root. -/
def comparisons (faces : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces
  mesh walk owner) (pieces : PreparedPath.CoveredSegments prepared)
    (domains : DomainBanks.FaceDomainBank frames base.faces.regulars) (differential : Differentials.Basic.Differential
      genus) (parentSheet : Fin 2)
    (caches : CoveredSegments.ParentCaches differential parentSheet pieces) :
    AssignedSegments.Comparisons differential parentSheet (faces.assign pieces) :=
  Comparisons.build domains differential parentSheet (faces.assign pieces) caches (faces.ownersAligned pieces)

/-- Every local comparison uses exactly the supplied shared finite face-domain bank. -/
theorem comparisons_shared (faces :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces mesh walk owner)
  (pieces : PreparedPath.CoveredSegments prepared)
    (domains : DomainBanks.FaceDomainBank frames base.faces.regulars) (differential : Differentials.Basic.Differential
      genus) (parentSheet : Fin 2)
    (caches : CoveredSegments.ParentCaches differential parentSheet pieces) :
    Comparisons.UsesDomains domains differential parentSheet (faces.assign pieces)
      (faces.comparisons pieces domains differential parentSheet caches) :=
  Comparisons.build_usesDomains domains differential parentSheet (faces.assign pieces) caches (faces.ownersAligned
    pieces)

/-- The local comparisons retain the exact ordered parent list of the supplied original caches. -/
theorem comparisons_parents (faces :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces mesh walk owner)
  (pieces : PreparedPath.CoveredSegments prepared)
    (domains : DomainBanks.FaceDomainBank frames base.faces.regulars) (differential : Differentials.Basic.Differential
      genus) (parentSheet : Fin 2)
    (caches : CoveredSegments.ParentCaches differential parentSheet pieces) :
    Comparisons.parents differential parentSheet (faces.assign pieces)
      (faces.comparisons pieces domains differential parentSheet caches) = ParentCaches.parents caches :=
  (Comparisons.parents_eq differential parentSheet (faces.assign pieces) _).trans
    (ParentCaches.parents_eq caches).symm

end OwnerWalkFaces
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Readings.PreparedBoundaryClosure (ClosedBoundaryDoublePath)
open Purelib.Riemann.Integration.PreparedOwnerClosedBridges (OwnerClosedCyclePair)
open Purelib.Topology.Polygon.Stokes (OrientedEdge triangleEdgeOccurrences)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid.Grid (ContainsTourVertices)
open FramedPuncturedGrid (OwnerWalkFaces)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}

/-- The return check preserves both supplied winding-one boundaries. -/
private theorem total_boundaryWindings {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {leftAmbient rightAmbient connectorAmbient : Rational.Box}
    (leftState : WindingOne.Basic.WindingOneState curve.polynomial leftAmbient)
    (rightState : WindingOne.Basic.WindingOneState curve.polynomial rightAmbient)
    (connector : Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient leftState.box.anchor
      rightState.box.anchor)
    (within : connector.WithinAmbient)
    (owner : PreparedSheetContinuation.Owner (curve.polynomial.eval leftState.box.anchor)) :
    ClearPath.rawWinding
      (Purelib.Riemann.Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath.total leftState rightState connector
        within owner).joined.data.rightBoundaryPath = 4 ∧
      ClearPath.rawWinding
      (Purelib.Riemann.Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath.total leftState rightState connector
        within owner).joined.data.leftBoundaryPath = 4 := by
  unfold ClosedBoundaryDoublePath.total
  dsimp only
  split
  · rename_i closed accepted
    rw [ClosedBoundaryDoublePath.checkReturn_joined _ closed accepted]
    exact ⟨BranchCutLifts.ownerBoundaryPath_rawWinding rightState,
      BranchCutLifts.ownerBoundaryPath_rawWinding leftState⟩
  · exact ⟨BranchCutLifts.ownerBoundaryPath_rawWinding rightState,
      BranchCutLifts.ownerBoundaryPath_rawWinding leftState⟩

/-- Each retained A boundary changes sheets once, independently of the chosen bank depths and the root-return proof. -/
theorem aTourOfData_boundaryWindings {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) (index : Fin genus) :
    ClearPath.rawWinding
      (OwnerClosedCyclePair.ofData curve branches index).aTour.joined.data.rightBoundaryPath = 4 ∧
      ClearPath.rawWinding
      (OwnerClosedCyclePair.ofData curve branches index).aTour.joined.data.leftBoundaryPath = 4 :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.total_boundaryWindings _ _ _ _ _

/-- Both retained B boundaries have their original separate winding. -/
theorem bTourOfData_boundaryWindings {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) (index : Fin genus) :
    ClearPath.rawWinding
      (OwnerClosedCyclePair.ofData curve branches index).bTour.joined.data.rightBoundaryPath = 4 ∧
      ClearPath.rawWinding
      (OwnerClosedCyclePair.ofData curve branches index).bTour.joined.data.leftBoundaryPath = 4 :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.total_boundaryWindings _ _ _ _ _

/-- Every actual vertex of the retained A tour lies in the framed grid. -/
theorem aOnGrid (base : Meshes.FramedPuncturedGrid curve (BranchConfiguration.configurationOfData curve
  branches).branches higher)
    (index : Fin genus) : Grid.ContainsTourVertices base.bank.grid (OwnerClosedCyclePair.ofData curve branches
      index).aTour :=
  base.bank.baseIncluded.tour _ (BranchGrid.branchGrid_aTour curve branches higher index)

/-- Every actual vertex of the retained B tour lies in the framed grid. -/
theorem bOnGrid (base : Meshes.FramedPuncturedGrid curve (BranchConfiguration.configurationOfData curve
  branches).branches higher)
    (index : Fin genus) : Grid.ContainsTourVertices base.bank.grid (OwnerClosedCyclePair.ofData curve branches
      index).bTour :=
  base.bank.baseIncluded.tour _ (BranchGrid.branchGrid_bTour curve branches higher index)

/-- Equal actual coordinates give equal retained frame-owner names at the same sheet. -/
public theorem frameNames_eq {first last : Data.Gaussian.Basic.Canonical} (frames :
    RootIsolation.SquareRoot.Grid.RootFrames
  base.bank.grid)
    (equal : first = last) (firstMember : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid first)
    (lastMember : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid last) (sheet : Fin 2) :
    OwnerTraceReadings.ownerName ((frames.frameAt first firstMember).owners sheet) = OwnerTraceReadings.ownerName
      ((frames.frameAt last lastMember).owners sheet) := by
  cases equal
  rfl

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours in
set_option genInjectivity false in
/-- One retained source pair, both split walks, and their actual face assignments. Reading A and B never prepares their
source tours again. -/
structure Pair (lifted : Meshes.LiftedPuncturedGrid base) (index : Fin genus) where
  /-- The cached original owner-closed A/B source-tour pair. -/ source : PreparedOwnerClosedBridges.OwnerClosedCyclePair
    curve
  /-- The retained source is exactly the canonical pair for this original curve, branch data and index. -/ source_eq :
    source = OwnerClosedCyclePair.ofData curve branches index
  /-- Every actual vertex of the retained A tour lies in the framed grid. -/ aOnGrid : Grid.ContainsTourVertices
    base.bank.grid source.aTour
  /-- Every actual vertex of the retained B tour lies in the framed grid. -/ bOnGrid : Grid.ContainsTourVertices
    base.bank.grid source.bTour
  /-- The cached split A tour on the actual retained grid. -/ aWalk : Walks.Walk base.bank.grid
    source.aTour.joined.data.leftState.box.anchor source.aTour.joined.data.leftState.box.anchor
  /-- The cached split B tour on the actual retained grid. -/ bWalk : Walks.Walk base.bank.grid
    source.bTour.joined.data.leftState.box.anchor source.bTour.joined.data.leftState.box.anchor
  /-- The A walk is exactly the split of its retained original source tour. -/ aWalk_eq : aWalk = Grid.splitTour
    base.bank.grid source.aTour aOnGrid
  /-- The B walk is exactly the split of its retained original source tour. -/ bWalk_eq : bWalk = Grid.splitTour
    base.bank.grid source.bTour bOnGrid
  /-- The actual retained A-walk face assignments and original incoming owner. -/ aFaces : OwnerWalkFaces lifted.mesh
    aWalk source.aTour.joined.data.forwardOwner
  /-- The actual retained B-walk face assignments and original incoming owner. -/ bFaces : OwnerWalkFaces lifted.mesh
    bWalk source.bTour.joined.data.forwardOwner
  /-- Both retained tours use the same materialized starting-sheet selection. -/ sheets_eq : aFaces.sheet = bFaces.sheet

constructive_injectivity Pair

namespace Pair

variable {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {index : Fin genus}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours in
/-- Reuse a supplied canonical source cache. Classification is performed once for the common starting root; B consumes
A's selected frame index. -/
def ofSource (lifted : Meshes.LiftedPuncturedGrid base) (index : Fin genus) (source :
  PreparedOwnerClosedBridges.OwnerClosedCyclePair curve)
    (sourceEq : source = OwnerClosedCyclePair.ofData curve branches index) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index := by
  have aOnGrid : Grid.ContainsTourVertices base.bank.grid source.aTour := sourceEq ▸
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.aOnGrid base index
  have bOnGrid : Grid.ContainsTourVertices base.bank.grid source.bTour := sourceEq ▸
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.bOnGrid base index
  let aWalk := Grid.splitTour base.bank.grid source.aTour aOnGrid
  let bWalk := Grid.splitTour base.bank.grid source.bTour bOnGrid
  let aFaces := OwnerWalkFaces.build lifted.mesh aWalk (Polynomial.Geometry.Grid.FromStates.ContainsPathVertices.start
    base.bank.grid _ aOnGrid.1)
    source.aTour.joined.data.forwardOwner
  let bFirst := Polynomial.Geometry.Grid.FromStates.ContainsPathVertices.start base.bank.grid _ bOnGrid.1
  have bAligned : Nonempty (Gaussian.Equivalence.NamedEquivalent
      (OwnerTraceReadings.ownerName source.bTour.joined.data.forwardOwner)
      (OwnerTraceReadings.ownerName ((lifted.frames.frameAt _ bFirst).owners aFaces.sheet))) := by
    rw [source.bRoot_eq, ← source.aRoot_eq, ←
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.frameNames_eq lifted.frames
      source.base_eq aFaces.first bFirst aFaces.sheet]
    exact aFaces.aligned
  let bFaces := OwnerWalkFaces.ofSheet lifted.mesh bWalk bFirst aFaces.sheet bAligned
  exact ⟨source, sourceEq, aOnGrid, bOnGrid, aWalk, bWalk, rfl, rfl, aFaces, bFaces, rfl⟩

/-- Cache the canonical owner-closed A/B source pair and its actual grid walks and face assignments. -/
def build (lifted : Meshes.LiftedPuncturedGrid base) (index : Fin genus) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair.ofSource lifted index
    (OwnerClosedCyclePair.ofData curve branches index) rfl

/-- The actual split A walk has raw winding eight. -/
theorem aWalk_winding (pair : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted
  index) : ClearPath.rawWinding pair.aWalk.path = 8 := by
  rw [pair.aWalk_eq, Grid.splitTour_winding, pair.source_eq]
  simpa only [BranchGridPaths.aTourWalkOfData, Grid.splitTour_winding] using
    BranchGridPaths.aTourWalkOfData_winding curve branches higher index

/-- The actual split B walk has raw winding eight. -/
theorem bWalk_winding (pair : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted
  index) : ClearPath.rawWinding pair.bWalk.path = 8 := by
  rw [pair.bWalk_eq, Grid.splitTour_winding, pair.source_eq]
  simpa only [BranchGridPaths.bTourWalkOfData, Grid.splitTour_winding] using
    BranchGridPaths.bTourWalkOfData_winding curve branches higher index

/-- The actual indexed A word closes on its original selected lifted vertex. -/
theorem a_closed (pair : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish pair.aFaces.geometry.indexed
      (lifted.vertices.index _ pair.aFaces.first pair.aFaces.sheet) (lifted.vertices.index _ pair.aFaces.first
        pair.aFaces.sheet) :=
  pair.aFaces.closed 1 pair.aWalk_winding

/-- The actual indexed B word closes on its original selected lifted vertex. -/
theorem b_closed (pair : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish pair.bFaces.geometry.indexed
      (lifted.vertices.index _ pair.bFaces.first pair.bFaces.sheet) (lifted.vertices.index _ pair.bFaces.first
        pair.bFaces.sheet) :=
  pair.bFaces.closed 1 pair.bWalk_winding

/-- Equal actual coordinates give equal retained vertex indices at the same sheet. -/
private theorem vertexIndex_eq {first last : Data.Gaussian.Basic.Canonical} (vertices : LiftedVertices.VertexBank
  base.bank.grid)
    (equal : first = last) (firstMember : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid first)
    (lastMember : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid last) (sheet : Fin 2) :
    vertices.index first firstMember sheet = vertices.index last lastMember sheet := by cases equal; rfl

/-- The retained indexed A and B words share the same actual lifted starting vertex. -/
theorem common_base (pair : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted
  index) :
    lifted.vertices.index _ pair.aFaces.first pair.aFaces.sheet = lifted.vertices.index _ pair.bFaces.first
      pair.bFaces.sheet := by
  rw [pair.sheets_eq]
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair.vertexIndex_eq lifted.vertices
    pair.source.base_eq pair.aFaces.first pair.bFaces.first pair.bFaces.sheet

end Pair

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours
