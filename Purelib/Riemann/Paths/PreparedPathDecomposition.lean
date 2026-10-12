module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Paths.OwnerTracePath
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathTrace

import Purelib.Riemann.Integration.PreparedCoveredParentLists
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Data.Gaussian.Basic

@[expose] public section

/-!
# Exact segment decomposition of a retained covered preparation

The cached trace lineage supplies each original segment budget and terminal
owner. Decomposition reads those caches; it does not prepare a new path or
recover a terminal owner by replaying subdivision. Each resulting piece is
itself a covered traced path, ready for a contained-face comparison.
-/

namespace Purelib.Riemann.Paths.PreparedPathDecomposition

open Purelib.Data.List

open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (Mesh)
open Purelib.Riemann.Paths.PreparedClearPathModels
  (GaussianPolynomial Gaussian Box Owner CompleteSegment PreparedPath zeroEndpoint oneEndpoint)
open _root_.Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedSegment TracedPath)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.PreparedPath (PrimitiveCover)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

namespace TracedSegment

open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- Retain a traced original prepared segment with the supplied exact moving-vertex and finish-owner caches.

The deferred owner trace is transported to the cached terminal owner, while the original request-fit certificate and
winding equation remain attached to the same preparation. -/
def ofMovingVertices {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)}
    (budget : PreparedTraceBudget segment zeroEndpoint oneEndpoint)
    (prepared : CompleteSegment segment within owner)
    (fits : budget.RequestsFit zeroEndpoint prepared.subdivision.requests)
    (finishOwner : Owner (polynomial.eval finish)) (finishEq : finishOwner = prepared.finishOwner)
    (vertices : List Gaussian)
    (verticesEq : vertices = PreparedPathTrace.CompleteSegment.movingVertices prepared) :
    TracedSegment segment within owner :=
  { budget := budget, prepared := prepared, fits := fits
    finishOwner := finishOwner, finishOwner_eq := finishEq
    movingVertices := vertices, movingVertices_eq := verticesEq
    trace := ⟨fun _ => (PreparedPathTrace.CompleteSegment.ownerPath prepared budget fits).castEndpoints
      rfl rfl HEq.rfl (heq_of_eq finishEq.symm)⟩
    winding_eq := by
      change Winding.Polygon.Basic.chainRaw polynomial start
        ((PreparedPathTrace.CompleteSegment.ownerPath prepared budget fits).castEndpoints
          rfl rfl HEq.rfl (heq_of_eq finishEq.symm)).vertices = _
      rw [OwnerTracePath.OwnerPath.castEndpoints_vertices]
      exact PreparedPathTrace.CompleteSegment.ownerPath_chainRaw prepared budget fits }

end TracedSegment

set_option genInjectivity false in
open Purelib.Polynomial in
/-- An original traced prepared segment retaining its exact primitive bounds and mesh-edge equation.

The original cleared segment and starting owner remain indices; the stored mesh covers precisely its retained
subdivision. -/
structure CoveredSegment {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (owner : Owner (polynomial.eval start))
      where
  /-- The original cleared segment lies in its retained ambient box. -/ within : segment.WithinAmbient
  /-- The retained original traced segment and its exact caches. -/ traced : TracedSegment segment within owner
  /-- The original uniform primitive bounds for the retained segment. -/ bounds : Bounds segment
  /-- The retained primitive mesh for those exact bounds. -/ mesh : Mesh bounds
  /-- The original prepared subdivision edges equal the retained mesh edges exactly. -/ mesh_eq :
    traced.prepared.subdivision.parameterEdges = mesh.edges

constructive_injectivity CoveredSegment

namespace CoveredSegment

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
  {segment : ClearSegment polynomial ambient start finish} {owner : Owner
    (polynomial.eval start)}

open Purelib.Riemann.Paths in
/-- View the original covered segment as a one-segment covered traced path with an exact empty tail. -/
def path (piece : CoveredSegment segment owner) : CoveredTracedPath (.cons segment (.nil finish)) owner :=
  let tail := TracedPath.build (.nil (ambient := ambient) finish) (.nil finish) piece.traced.finishOwner
  ⟨TracedPath.cons piece.traced tail,
    .cons piece.bounds piece.mesh piece.mesh_eq
      (PreparedPathPrimitiveCover.PreparedClearPathModels.PreparedPath.PrimitiveCover.castOwner
        piece.traced.finishOwner_eq
        (PreparedPathPrimitiveCover.PreparedClearPathModels.PreparedPath.PrimitiveCover.nil
          finish piece.traced.finishOwner))⟩

/-- The one-segment covered path retains exactly the original segment's cached finish owner. -/
theorem path_finishOwner (piece : CoveredSegment segment owner) :
    (path piece).traced.finishOwner = piece.traced.finishOwner := rfl

end CoveredSegment

namespace PreparedPath

section
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- Recover the original primitive cover from transport along equality of starting owners. -/
private def PrimitiveCover.uncastOwner {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} {first second : Owner (polynomial.eval
      start)}
    (equal : first = second) {prepared : PreparedPath path first}
    (cover : PrimitiveCover (PreparedPathTrace.PreparedPath.castOwner equal prepared)) :
    PrimitiveCover prepared := by
  cases equal
  exact cover

/-- Recover the original primitive cover from transport along equality of starting owners. -/
def PrimitiveCover.uncastOwnerForBuild {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} {first second : Owner (polynomial.eval
      start)}
    (equal : first = second) {prepared : PreparedPath path first}
    (cover : PrimitiveCover (PreparedPathTrace.PreparedPath.castOwner equal prepared)) :
    PrimitiveCover prepared := by
  cases equal
  exact cover

end

set_option genInjectivity false in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- An ordered decomposition of the exact original prepared path into retained covered traced segments.

Every step preserves the original segment, cached finish owner and precise owner transport used to index the retained
tail. -/
inductive CoveredSegments {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} → {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} →
      {owner : Owner (polynomial.eval start)} → PreparedPath path owner → Type
  /-- The empty original prepared path retains its point and owner. -/ | nil (point : Gaussian) (owner : Owner
    (polynomial.eval point)) : CoveredSegments (.nil point owner)
  /-- Retain the original covered head and tail with the exact cached-owner transport. -/ | cons {start middle finish :
    Gaussian} {head : Geometry.ClearPath.ClearSegment polynomial ambient start middle}
      {tail : Polynomial.Geometry.ClearPath polynomial ambient middle finish} {owner : Owner (polynomial.eval start)}
      (first : CoveredSegment head owner) {rest : PreparedPath tail first.traced.finishOwner}
      (remaining : CoveredSegments rest) :
      CoveredSegments (.cons head tail owner first.within first.traced.prepared
        (PreparedPathTrace.PreparedPath.castOwner first.traced.finishOwner_eq rest))

constructive_injectivity CoveredSegments

namespace CoveredSegments

variable {polynomial : GaussianPolynomial} {ambient : Box}

section
open Purelib.Polynomial
/-- Read the original first covered segment from a nonempty retained decomposition. -/
def head {start middle finish : Gaussian} {first : Geometry.ClearPath.ClearSegment polynomial ambient start middle}
    {tail : Polynomial.Geometry.ClearPath polynomial ambient middle finish} {owner : Owner (polynomial.eval start)} :
    {prepared : PreparedPath (.cons first tail) owner} → CoveredSegments prepared → CoveredSegment first owner
  | _, .cons first _ => first

section
open Purelib.Riemann.Branches
open Purelib.Riemann.Paths
/-- The moving vertex list has the retained covering mesh's edge count.

Mapping the original subdivision requests preserves their finite length. The
retained mesh-edge equation identifies that length with the actual edge count. -/
private theorem movingVertices_length {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)} (first : CompleteSegment segment within owner)
    {bounds : Bounds segment} (mesh : Mesh bounds) (meshEq : first.subdivision.parameterEdges = mesh.edges) :
    (PreparedPathTrace.CompleteSegment.movingVertices first).length = mesh.edgeCount := by
  rw [PreparedPathTrace.CompleteSegment.movingVertices, Map.length_map,
    PreparedSheetContinuation.Subdivision.requests_length,
    ← PreparedSheetContinuation.Subdivision.parameterEdges_length,
    meshEq, mesh.edges_length]

/-- The moving vertex list has the retained covering mesh's edge count.

Mapping the original subdivision requests preserves their finite length. The
retained mesh-edge equation identifies that length with the actual edge count. -/
theorem movingVertices_mesh_length {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)} (first : CompleteSegment segment within owner)
    {bounds : Bounds segment} (mesh : Mesh bounds) (meshEq : first.subdivision.parameterEdges = mesh.edges) :
    (PreparedPathTrace.CompleteSegment.movingVertices first).length = mesh.edgeCount := by
  rw [PreparedPathTrace.CompleteSegment.movingVertices, Map.length_map,
    PreparedSheetContinuation.Subdivision.requests_length,
    ← PreparedSheetContinuation.Subdivision.parameterEdges_length,
    meshEq, mesh.edges_length]

end

open Purelib.Riemann.Paths in
/-- Decompose original trace lineage and primitive covers while consuming their retained moving-vertex cache.

Each exact mesh edge count splits the existing cache with take and drop; the original terminal-owner equality transports
the remaining cover before recursion. -/
def build : ∀ {start finish : Gaussian} {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)} {prepared : PreparedPath path owner},
    TraceLineage prepared → PrimitiveCover prepared → (vertices : List Gaussian) →
      vertices = PreparedPathTrace.PreparedPath.movingVertices prepared → CoveredSegments prepared
  | _, _, _, _, _, .nil point owner, .nil _ _, _, _ => .nil point owner
  | _, _, _, _, _, @TraceLineage.cons _ _ _ _ _ head tail owner within first finishOwner rest budget fits finishEq
    remaining, cover, vertices, verticesEq =>
    by
      cases cover with
      | cons bounds mesh meshEq restCover =>
          have cacheEq : vertices =
              PreparedPathTrace.CompleteSegment.movingVertices first ++
              PreparedPathTrace.PreparedPath.movingVertices rest := by
            rw [verticesEq, PreparedPathTrace.PreparedPath.movingVertices,
              PreparedPathTrace.PreparedPath.castOwner_movingVertices]
          have firstEq : vertices.take mesh.edgeCount =
              PreparedPathTrace.CompleteSegment.movingVertices first := by
            rw [cacheEq, ← movingVertices_mesh_length first mesh meshEq, List.take_left]
          have restEq : vertices.drop mesh.edgeCount =
              PreparedPathTrace.PreparedPath.movingVertices rest := by
            rw [cacheEq, ← movingVertices_mesh_length first mesh meshEq, List.drop_left]
          let traced := TracedSegment.ofMovingVertices budget first fits finishOwner finishEq
            (vertices.take mesh.edgeCount) firstEq
          exact .cons ⟨within, traced, bounds, mesh, meshEq⟩
            (build remaining (PrimitiveCover.uncastOwnerForBuild finishEq restCover) (vertices.drop mesh.edgeCount)
              restEq)

/-- Count the original covered segments in the retained ordered decomposition. -/
def count : ∀ {start finish : Gaussian} {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)} {prepared : PreparedPath path owner}, CoveredSegments prepared → Nat
  | _, _, _, _, _, .nil _ _ => 0
  | _, _, _, _, _, .cons _ tail => 1 + tail.count

/-- The retained decomposition has exactly the original cleared path's segment count. -/
theorem count_eq : ∀ {start finish : Gaussian} {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)} {prepared : PreparedPath path owner} (pieces : CoveredSegments prepared),
    pieces.count = path.segmentCount
  | _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, .cons _ tail => by
      change 1 + tail.count = _ + 1
      rw [tail.count_eq, Nat.add_comm]

/-- Concatenate the retained original moving-vertex caches in covered-segment order. -/
def movingVertices : ∀ {start finish : Gaussian} {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)} {prepared : PreparedPath path owner}, CoveredSegments prepared → List
      Gaussian
  | _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, .cons first tail => first.traced.movingVertices ++ tail.movingVertices

open Purelib.Riemann.Paths in
/-- The retained decomposition's moving vertices equal the original prepared path's exact vertex list. -/
theorem movingVertices_eq : ∀ {start finish : Gaussian} {path : Polynomial.Geometry.ClearPath polynomial ambient start
  finish}
    {owner : Owner (polynomial.eval start)} {prepared : PreparedPath path owner} (pieces : CoveredSegments prepared),
    pieces.movingVertices = PreparedPathTrace.PreparedPath.movingVertices prepared
  | _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, .cons first tail => by
      rw [movingVertices, first.traced.movingVertices_eq, tail.movingVertices_eq]
      change _ = PreparedPathTrace.CompleteSegment.movingVertices first.traced.prepared ++ _
      rw [PreparedPathTrace.PreparedPath.castOwner_movingVertices]

/-- Read the original final cached owner from the retained covered-segment decomposition. -/
def finishOwner : ∀ {start finish : Gaussian} {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)} {prepared : PreparedPath path owner},
    CoveredSegments prepared → Owner (polynomial.eval finish)
  | _, _, _, _, _, .nil _ owner => owner
  | _, _, _, _, _, .cons _ tail => tail.finishOwner

open Purelib.Riemann.Paths in
/-- The decomposition's retained terminal owner equals the original prepared path's finish owner. -/
theorem finishOwner_eq : ∀ {start finish : Gaussian} {path : Polynomial.Geometry.ClearPath polynomial ambient start
  finish}
    {owner : Owner (polynomial.eval start)} {prepared : PreparedPath path owner} (pieces : CoveredSegments prepared),
    pieces.finishOwner = PreparedPathGluing.finishOwner prepared
  | _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, .cons _ tail => by
      rw [finishOwner, tail.finishOwner_eq]
      exact (PreparedPathTrace.PreparedPath.castOwner_finishOwner _ _).symm

end

end CoveredSegments

end PreparedPath

namespace CoveredTracedPath

open Purelib.Polynomial
/-- Decompose the original covered traced path using its retained lineage, primitive cover and exact moving cache. -/
def segments {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} {owner : Owner (polynomial.eval start)}
    (prepared : CoveredTracedPath path owner) : PreparedPath.CoveredSegments prepared.traced.prepared :=
  PreparedPath.CoveredSegments.build prepared.traced.lineage prepared.cover prepared.traced.movingVertices
    prepared.traced.movingVertices_eq

/-- The decomposition preserves the original covered traced path's exact moving-vertex cache. -/
theorem segments_movingVertices {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} {owner : Owner (polynomial.eval start)}
    (prepared : CoveredTracedPath path owner) :
    (segments prepared).movingVertices = prepared.traced.movingVertices :=
  (segments prepared).movingVertices_eq.trans prepared.traced.movingVertices_eq.symm

/-- The decomposition preserves the original covered traced path's exact cached finish owner. -/
theorem segments_finishOwner {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} {owner : Owner (polynomial.eval start)}
    (prepared : CoveredTracedPath path owner) :
    (segments prepared).finishOwner = prepared.traced.finishOwner :=
  (segments prepared).finishOwner_eq.trans prepared.traced.finishOwner_eq.symm

end CoveredTracedPath

namespace CoveredSegment

open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- Construct the original covered segment through its exact one-segment covered traced path.

The retained decomposition returns the original first segment with its mesh, cache and owner identities preserved. -/
def build {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start)) : CoveredSegment segment owner :=
  (PreparedPathDecomposition.CoveredTracedPath.segments
    (CoveredTracedPath.build (.cons segment (.nil finish)) (.cons within (.nil finish)) owner)).head

end CoveredSegment

end Purelib.Riemann.Paths.PreparedPathDecomposition
