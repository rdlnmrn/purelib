module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.Riemann.Integration.PreparedCoveredParentLists

import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
public import Purelib.Riemann.Paths.PreparedSegmentParentBanks
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

public section

/-!
# Cached parents and primitive covers of retained path segments

Split the original materialized parent list and its materialized cover at
the retained segment counts. The canonical centered extraction is a proof
specification only. In particular the endpoint-chain witness is erased and
cannot replay a dependent owner transition while consuming a cache.
-/

namespace Purelib.Riemann.Paths.PreparedPathParentCaches.CoveredParents
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}

open Purelib.Curves.Hyperelliptic.Integration
/-- Restrict the original parent-cover evidence to an exact list prefix. -/
@[expose] def take : (steps : Nat) → ∀ {parents : List (CenteredEdge curve differential)},
    Observation.UniformPreparedMesh.CoveredParents count parents → Observation.UniformPreparedMesh.CoveredParents count
      (parents.take steps)
  | 0, _, _ => .nil
  | _ + 1, _, .nil => .nil
  | count + 1, _, .cons patch inside tail => .cons patch inside
    (take count tail)

/-- Restrict the original parent-cover evidence to an exact list suffix. -/
@[expose] def drop : (steps : Nat) → ∀ {parents : List (CenteredEdge curve differential)},
    Observation.UniformPreparedMesh.CoveredParents count parents → Observation.UniformPreparedMesh.CoveredParents count
      (parents.drop steps)
  | 0, _, covered => covered
  | _ + 1, _, .nil => .nil
  | count + 1, _, .cons _ _ tail => drop count tail

end Purelib.Riemann.Paths.PreparedPathParentCaches.CoveredParents

namespace Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Paths.PreparedSegmentParentBanks.PreparedPath.CoveredSegments (parents)

variable {genus : Nat} {curve : HyperellipticCurve genus} {ambient :
  Purelib.Geometry.Rational.Box}
  {start finish : Purelib.Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath
    curve.polynomial ambient start finish}
  {owner : Owner (curve.polynomial.eval start)}

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
set_option genInjectivity false in
/-- A retained covered parent list with its original prepared-path identity.

The cache fixes the differential and sheet, retains the actual centered parents, and identifies them with the original
traced path's parent chain. -/
structure ParentCache (prepared : CoveredTracedPath path owner) (differential : Differentials.Basic.Differential genus)
  (sheet : Fin 2) where
  /-- The retained list of original centered parent edges. -/ parents : List (CenteredEdge curve differential)
  /-- Exact equality with the original prepared path's centered parent chain. -/ parents_eq : parents =
    (CenteredPathChain.ofPreparedPath curve differential sheet prepared.traced.prepared).parents
  /-- Primitive-neighborhood coverage of those same retained parents. -/ covered :
    Observation.UniformPreparedMesh.CoveredParents genus parents

constructive_injectivity ParentCache

namespace ParentCache

variable {prepared : CoveredTracedPath path owner} {differential :
  Differential genus} {sheet : Fin 2}

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
/-- Retain the original prepared-path parent list with its primitive-cover evidence. -/
@[expose] def build (prepared : CoveredTracedPath path owner) (differential : Differentials.Basic.Differential genus)
  (sheet : Fin 2) :
    ParentCache prepared differential sheet :=
  ⟨(CenteredPathChain.ofPreparedPath curve differential sheet prepared.traced.prepared).parents, rfl,
    PreparedCoveredParentLists.PrimitiveCover.coveredParents curve differential sheet genus prepared.cover⟩

/-- Every cached parent retains the proper-edge condition of the original covered path. -/
theorem proper (cache : ParentCache prepared differential sheet) :
    AllParentsProper cache.parents := by
  rw [cache.parents_eq]
  exact CenteredPathChain.ofPreparedPath_allParentsProper_of_allEdgesProper curve differential sheet
    prepared.traced.prepared prepared.cover.proper

/-- The cached parents retain a centered path chain with the original geometric endpoints and sheet. -/
theorem chain (cache : ParentCache prepared differential sheet) :
    Nonempty (CenteredPathChain cache.parents (start := ⟨start, sheet⟩) (finish := ⟨finish, sheet⟩)) := by
  rw [cache.parents_eq]
  exact ⟨(CenteredPathChain.ofPreparedPath curve differential sheet prepared.traced.prepared).chain⟩

end ParentCache

namespace PreparedPath.CoveredSegments

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- A segment-indexed family of retained parent caches for the original covered path.

Each nonempty segment keeps its own cache and the exact remaining path family; the empty family contains no parent data.
-/
@[expose] def ParentCaches (differential : Differentials.Basic.Differential genus) (sheet : Fin 2) :
    ∀ {start finish : Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)} {prepared : PreparedPath path owner}, CoveredSegments prepared →
        Type 2
  | _, _, _, _, _, .nil _ _ => PUnit
  | _, _, _, _, _, .cons first tail => ParentCache first.path differential sheet × ParentCaches differential sheet tail

namespace ParentCaches

variable {differential : Differential genus} {sheet : Fin 2}

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- Split a supplied covered parent cache along the original segment edge counts.

Each segment retains the exact prefix list and its coverage; the recursive tail uses the matching suffix and original
parent-list identity, preserving the supplied cached data. -/
@[expose] def build (differential : Differentials.Basic.Differential genus) (sheet : Fin 2) :
    ∀ {start finish : Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)} {prepared : PreparedPath path owner} (pieces : CoveredSegments
        prepared)
      (cached : List (CenteredEdge curve differential)),
      cached = parents differential sheet pieces → Observation.UniformPreparedMesh.CoveredParents genus cached →
        ParentCaches differential sheet pieces
  | _, _, _, _, _, .nil _ _, _, _, _ => ⟨⟩
  | _, _, _, _, _, .cons first tail, cached, equal, covered => by
      have split : cached = (CenteredPathChain.ofPreparedPath curve differential sheet
        first.path.traced.prepared).parents ++
          parents differential sheet tail := equal
      have firstEq : cached.take first.mesh.edgeCount =
          (CenteredPathChain.ofPreparedPath curve differential sheet first.path.traced.prepared).parents := by
        rw [split, ← PreparedSegmentParentBanks.CoveredSegment.path_parentCount first differential sheet,
          List.take_left]
      have tailEq : cached.drop first.mesh.edgeCount = parents differential sheet tail := by
        rw [split, ← PreparedSegmentParentBanks.CoveredSegment.path_parentCount first differential sheet,
          List.drop_left]
      exact ⟨⟨cached.take first.mesh.edgeCount, firstEq, PreparedPathParentCaches.CoveredParents.take
        first.mesh.edgeCount covered⟩,
        build differential sheet tail (cached.drop first.mesh.edgeCount) tailEq
          (PreparedPathParentCaches.CoveredParents.drop first.mesh.edgeCount covered)⟩

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- Concatenate the original segment caches in their retained path order. -/
@[expose] def parents : ∀ {start finish : Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial
  ambient
  start finish}
    {owner : Owner (curve.polynomial.eval start)} {prepared : PreparedPath path owner} {pieces : CoveredSegments
      prepared},
    ParentCaches differential sheet pieces → List (CenteredEdge curve differential)
  | _, _, _, _, _, .nil _ _, _ => []
  | _, _, _, _, _, .cons _ _, cache => cache.1.parents ++ parents cache.2

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- The concatenated cached parents equal the original covered-segment parent list. -/
theorem parents_eq : ∀ {start finish : Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
  start finish}
    {owner : Owner (curve.polynomial.eval start)} {prepared : PreparedPath path owner} {pieces : CoveredSegments
      prepared}
    (cache : ParentCaches differential sheet pieces), parents cache =
      PreparedSegmentParentBanks.PreparedPath.CoveredSegments.parents differential sheet pieces
  | _, _, _, _, _, .nil _ _, _ => rfl
  | _, _, _, _, _, .cons _ _, cache => congrArg₂ List.append cache.1.parents_eq (parents_eq cache.2)

open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Riemann.Paths in
/-- Splitting and reassembling the segment caches reads back the exact supplied parent list. -/
theorem build_parents (pieces : CoveredSegments prepared) (cached : List (CenteredEdge curve differential))
    (equal : cached = PreparedSegmentParentBanks.PreparedPath.CoveredSegments.parents differential sheet pieces)
      (covered : Observation.UniformPreparedMesh.CoveredParents genus cached) :
    parents (build differential sheet pieces cached equal covered) = cached :=
  (parents_eq (build differential sheet pieces cached equal covered)).trans equal.symm

end ParentCaches
end PreparedPath.CoveredSegments
end Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels
