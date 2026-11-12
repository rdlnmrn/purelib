module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
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
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Blocks
public import Purelib.Riemann.Readings.UniformPreparedRequests

import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
public import Purelib.Riemann.Paths.PreparedSegmentParentBanks
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.List.Map
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

open Purelib.Riemann.Integration

/-- Attach an actual original covered parent list without re-evaluating its centered numerical producer.

The stored coverage supplies the actual list. Its exact index law and the
supplied original prepared-path identity retain every numerical parent,
patch, source owner and dependent tail in the unchanged ParentCache record.
-/
@[expose] def ofCovered (prepared : CoveredTracedPath path owner) (differential : Differential genus) (sheet : Fin 2)
    (parents : List (CenteredEdge curve differential))
    (provenance : parents =
      (CenteredPathChain.ofPreparedPath curve differential sheet prepared.traced.prepared).parents)
    (covered : CoveredParents genus parents) : ParentCache prepared differential sheet :=
  { parents := covered.parentList
    parents_eq := covered.parentList_eq.trans provenance
    covered := Eq.mp (congrArg (CoveredParents genus) covered.parentList_eq.symm) covered }

/-- Attaching the retained coverage preserves the complete original parent-cache value and all of its fields. -/
theorem ofCovered_eq (prepared : CoveredTracedPath path owner) (differential : Differential genus) (sheet : Fin 2)
    (parents : List (CenteredEdge curve differential))
    (provenance : parents =
      (CenteredPathChain.ofPreparedPath curve differential sheet prepared.traced.prepared).parents)
    (covered : CoveredParents genus parents) :
    ofCovered prepared differential sheet parents provenance covered = ⟨parents, provenance, covered⟩ := by
  cases covered <;> rfl

/-- Build the original covered parent list once and retain its actual list without repeating centered acquisition. -/
@[expose] def build (prepared : CoveredTracedPath path owner) (differential : Differential genus)
    (sheet : Fin 2) : ParentCache prepared differential sheet :=
  let covered := PreparedCoveredParentLists.PrimitiveCover.coveredParents curve differential sheet genus prepared.cover
  ofCovered prepared differential sheet _ rfl covered

/-- The retained builder has the complete original parent list, covering spine and prepared-path equality. -/
theorem build_eq (prepared : CoveredTracedPath path owner) (differential : Differential genus) (sheet : Fin 2) :
    build prepared differential sheet =
      ⟨(CenteredPathChain.ofPreparedPath curve differential sheet prepared.traced.prepared).parents, rfl,
        PreparedCoveredParentLists.PrimitiveCover.coveredParents curve differential sheet genus prepared.cover⟩ :=
  ofCovered_eq prepared differential sheet _ rfl _

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

/-- Read a centered chain from the actual retained parent cache without replaying its prepared-path producer.

The existing erased chain witness determines only the original endpoint
indices. The construction traverses the stored parent list once, retaining
each complete original parent, source, request and sheet.
-/
def centeredChain (cache : ParentCache prepared differential sheet) :
    CenteredPathChain cache.parents (start := ⟨start, sheet⟩) (finish := ⟨finish, sheet⟩) :=
  CenteredPathChain.ofNonempty cache.parents cache.chain

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

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.Blocks

open Purelib.Riemann.Integration

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Readings.UniformPreparedRequests (PrimitiveSumRequest)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)

variable {genus : Nat} {curve : HyperellipticCurve genus}

/-- The original per-block parent caches indexed by the exact supplied covered-block spine.

Every moving cons retains an entire existing ParentCache on its unchanged
CoveredTracedPath. A stationary handoff forwards the identical tail family;
it contributes no integration edge and retains its actual join in Blocks.
-/
@[expose] def ParentCaches (differential : Differential genus) (sheet : Fin 2) :
    ∀ {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
      {target : Owner (curve.polynomial.eval finish)}, Blocks curve.polynomial start source finish target → Type 2
  | _, _, _, _, .nil _ _ => PUnit
  | _, _, _, _, .cons covered tail => ParentCache covered differential sheet × ParentCaches differential sheet tail
  | _, _, _, _, .handoff _ tail => ParentCaches differential sheet tail

namespace ParentCaches

variable {differential : Differential genus} {sheet : Fin 2}

/-- Build each original whole parent cache once on the actual retained covered block, preserving every handoff tail. -/
@[expose] def build (differential : Differential genus) (sheet : Fin 2) :
    ∀ {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
      {target : Owner (curve.polynomial.eval finish)} (blocks : Blocks curve.polynomial start source finish target),
      ParentCaches differential sheet blocks
  | _, _, _, _, .nil _ _ => ⟨⟩
  | _, _, _, _, .cons covered tail => ⟨ParentCache.build covered differential sheet, build differential sheet tail⟩
  | _, _, _, _, .handoff _ tail => build differential sheet tail

/-- Read the retained original parent lists in their actual covered-block order. -/
@[expose] def parents : ∀ {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
    {target : Owner (curve.polynomial.eval finish)} {blocks : Blocks curve.polynomial start source finish target},
    ParentCaches differential sheet blocks → List (CenteredEdge curve differential)
  | _, _, _, _, .nil _ _, _ => []
  | _, _, _, _, .cons _ tail, caches => caches.1.parents ++ parents (blocks := tail) caches.2
  | _, _, _, _, .handoff _ tail, caches => parents (blocks := tail) caches
termination_by structural _ _ _ _ blocks _ => blocks

/-- Concatenate the same original per-parent patch and endpoint-containment caches without reacquiring any patch. -/
@[expose] def covered : ∀ {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
    {target : Owner (curve.polynomial.eval finish)} {blocks : Blocks curve.polynomial start source finish target}
    (caches : ParentCaches differential sheet blocks), CoveredParents genus caches.parents
  | _, _, _, _, .nil _ _, _ => .nil
  | _, _, _, _, .cons _ tail, caches =>
      PreparedCoveredParentLists.CoveredParents.append caches.1.covered (covered (blocks := tail) caches.2)
  | _, _, _, _, .handoff _ tail, caches => covered (blocks := tail) caches
termination_by structural _ _ _ _ blocks _ => blocks

/-- Every original retained parent is proper by its own actual covered preparation, including across handoffs. -/
theorem proper : ∀ {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
    {target : Owner (curve.polynomial.eval finish)} {blocks : Blocks curve.polynomial start source finish target}
    (caches : ParentCaches differential sheet blocks), AllParentsProper caches.parents
  | _, _, _, _, .nil _ _, _ => trivial
  | _, _, _, _, .cons _ tail, caches =>
      Integration.PreparedDirectDyadicRefinements.allParentsProper_append caches.1.proper
        (proper (blocks := tail) caches.2)
  | _, _, _, _, .handoff _ tail, caches => proper (blocks := tail) caches
termination_by structural _ _ _ _ blocks _ => blocks

section CenteredChains

open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)

/-- The same cached block parents retain a centered chain at their original physical endpoints and sheet.

Each moving block contributes only its original erased ParentCache chain
witness. Appending those witnesses preserves the literal cached head and
tail lists. A stationary handoff keeps the same spatial coordinate and
forwards the unchanged tail; no numerical parent or owner is reconstructed.
-/
theorem chain : ∀ {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
    {target : Owner (curve.polynomial.eval finish)} {blocks : Blocks curve.polynomial start source finish target}
    (caches : ParentCaches differential sheet blocks),
    Nonempty (CenteredPathChain caches.parents (start := ⟨start, sheet⟩) (finish := ⟨finish, sheet⟩))
  | _, _, _, _, .nil _ _, _ => ⟨.nil _⟩
  | _, _, _, _, .cons _ tail, caches => by
      rcases caches.1.chain with ⟨head⟩
      rcases chain (blocks := tail) caches.2 with ⟨remaining⟩
      exact ⟨head.append remaining⟩
  | _, _, _, _, .handoff _ tail, caches => chain (blocks := tail) caches
termination_by structural _ _ _ _ blocks _ => blocks

/-- Read the global centered chain constructively from those same stored original parent occurrences.

The original list is read once, then the original ofNonempty operation
traverses that list. Coverage and endpoint provenance are erased proofs;
no prepared-path extraction, source attachment, model or observation runs.
The operation does allocate the original chain's finite constructor spine.
-/
def centeredChain {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
    {target : Owner (curve.polynomial.eval finish)} {blocks : Blocks curve.polynomial start source finish target}
    (caches : ParentCaches differential sheet blocks) :
    CenteredPathChain caches.parents (start := ⟨start, sheet⟩) (finish := ⟨finish, sheet⟩) :=
  let parents := caches.parents
  CenteredPathChain.ofNonempty parents caches.chain

end CenteredChains

section RequestRows

open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum gaussianSum_append)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Data.List

variable {count : Nat} {allowance : Fraction.Rational}

/-- Read one ordered bank through the retained original covered-block boundaries.

The supplied split operation consumes the actual whole bank and returns
its exact prefix and suffix at the cached parent boundary. A moving block
passes its complete ParentCache to the reader; a stationary handoff passes
the unchanged suffix onward. No parent, patch or numerical request is built.
-/
@[specialize] def mapBanks {Value : Type u}
    (family : (parents : List (CenteredEdge curve differential)) → CoveredParents genus parents → Type v)
    (divide : ∀ {first last : List (CenteredEdge curve differential)}
      (firstCover : CoveredParents genus first) (lastCover : CoveredParents genus last),
      family (first ++ last)
          (PreparedCoveredParentLists.CoveredParents.append firstCover lastCover) →
        family first firstCover × family last lastCover)
    (read : ∀ {start finish : Canonical} {ambient : Geometry.Rational.Box}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {source : Owner (curve.polynomial.eval start)} (covered : CoveredTracedPath path source)
      (cache : ParentCache covered differential sheet), family cache.parents cache.covered → Value) :
    ∀ {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
      {target : Owner (curve.polynomial.eval finish)} {blocks : Blocks curve.polynomial start source finish target}
      (caches : ParentCaches differential sheet blocks), family caches.parents caches.covered → List Value
  | _, _, _, _, .nil _ _, _, _ => []
  | _, _, _, _, .cons covered tail, caches, bank =>
      let rows := divide caches.1.covered (ParentCaches.covered (blocks := tail) caches.2) bank
      read covered caches.1 rows.1 :: mapBanks family divide read (blocks := tail) caches.2 rows.2
  | _, _, _, _, .handoff _ tail, caches, bank => mapBanks family divide read (blocks := tail) caches bank
termination_by structural _ _ _ _ blocks _ _ => blocks

section MapBranches

variable {Value : Type u}
variable (family : (parents : List (CenteredEdge curve differential)) → CoveredParents genus parents → Type v)
variable (divide : ∀ {first last : List (CenteredEdge curve differential)}
  (firstCover : CoveredParents genus first) (lastCover : CoveredParents genus last),
  family (first ++ last) (PreparedCoveredParentLists.CoveredParents.append firstCover lastCover) →
    family first firstCover × family last lastCover)
variable (read : ∀ {start finish : Canonical} {ambient : Geometry.Rational.Box}
  {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
  {source : Owner (curve.polynomial.eval start)} (covered : CoveredTracedPath path source)
  (cache : ParentCache covered differential sheet), family cache.parents cache.covered → Value)

/-- The original empty block bank contributes no row to either retained interpreter. -/
theorem mapBanks_nil (point : Canonical) (source : Owner (curve.polynomial.eval point))
    (caches : ParentCaches differential sheet (.nil point source)) (bank : family caches.parents caches.covered) :
    mapBanks family divide read caches bank = [] := (rfl)

/-- The original moving branch reads the exact split prefix and forwards its literal suffix to the tail. -/
theorem mapBanks_cons {start middle finish : Canonical} {ambient : Geometry.Rational.Box}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start middle}
    {source : Owner (curve.polynomial.eval start)} {target : Owner (curve.polynomial.eval finish)}
    (covered : CoveredTracedPath path source)
    (tail : Blocks curve.polynomial middle covered.traced.finishOwner finish target)
    (caches : ParentCaches differential sheet (.cons covered tail)) (bank : family caches.parents caches.covered) :
    mapBanks family divide read caches bank =
      let rows := divide caches.1.covered (ParentCaches.covered (blocks := tail) caches.2) bank
      read covered caches.1 rows.1 :: mapBanks family divide read (blocks := tail) caches.2 rows.2 := (rfl)

/-- A stationary original owner join forwards the same complete bank and contributes no numerical row. -/
theorem mapBanks_handoff {point finish : Canonical} {source : Owner (curve.polynomial.eval point)}
    {target : Owner (curve.polynomial.eval finish)} (join : Join source)
    (tail : Blocks curve.polynomial point join.1 finish target)
    (caches : ParentCaches differential sheet (.handoff join tail)) (bank : family caches.parents caches.covered) :
    mapBanks family divide read caches bank = mapBanks family divide read (blocks := tail) caches bank := (rfl)

end MapBranches

/-- Exact row projections flatten to the same supplied global ordered bank.

The empty, split and row laws concern the supplied family's actual values.
They retain the original parent and cover indices and imply a whole-list
readback, without any numerical comparison or geometric success premise.
-/
theorem mapBanks_flatten {Value : Type u} {Entry : Type w}
    (family : (parents : List (CenteredEdge curve differential)) → CoveredParents genus parents → Type v)
    (divide : ∀ {first last : List (CenteredEdge curve differential)}
      (firstCover : CoveredParents genus first) (lastCover : CoveredParents genus last),
      family (first ++ last)
          (PreparedCoveredParentLists.CoveredParents.append firstCover lastCover) →
        family first firstCover × family last lastCover)
    (read : ∀ {start finish : Canonical} {ambient : Geometry.Rational.Box}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {source : Owner (curve.polynomial.eval start)} (covered : CoveredTracedPath path source)
      (cache : ParentCache covered differential sheet), family cache.parents cache.covered → Value)
    (select : Value → List Entry)
    (project : ∀ {parents : List (CenteredEdge curve differential)} (covered : CoveredParents genus parents),
      family parents covered → List Entry)
    (empty : ∀ bank : family [] .nil, project .nil bank = [])
    (divided : ∀ {first last : List (CenteredEdge curve differential)}
      (firstCover : CoveredParents genus first) (lastCover : CoveredParents genus last)
      (bank : family (first ++ last)
        (PreparedCoveredParentLists.CoveredParents.append firstCover lastCover)),
      project (PreparedCoveredParentLists.CoveredParents.append firstCover lastCover) bank =
        project firstCover (divide firstCover lastCover bank).1 ++
          project lastCover (divide firstCover lastCover bank).2)
    (row : ∀ {start finish : Canonical} {ambient : Geometry.Rational.Box}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {source : Owner (curve.polynomial.eval start)} (covered : CoveredTracedPath path source)
      (cache : ParentCache covered differential sheet) (bank : family cache.parents cache.covered),
      select (read covered cache bank) = project cache.covered bank) :
    ∀ {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
      {target : Owner (curve.polynomial.eval finish)} {blocks : Blocks curve.polynomial start source finish target}
      (caches : ParentCaches differential sheet blocks) (bank : family caches.parents caches.covered),
      ((mapBanks family divide read caches bank).map select).flatten = project caches.covered bank
  | _, _, _, _, .nil _ _, caches, bank => (empty bank).symm
  | _, _, _, _, .cons covered tail, caches, bank => by
      let rows := divide caches.1.covered (ParentCaches.covered (blocks := tail) caches.2) bank
      change select (read covered caches.1 rows.1) ++
        ((mapBanks family divide read caches.2 rows.2).map select).flatten = _
      exact ((congrArg (fun values => values ++
        ((mapBanks family divide read caches.2 rows.2).map select).flatten)
          (row covered caches.1 rows.1)).trans
            (congrArg (List.append (project caches.1.covered rows.1))
              (mapBanks_flatten family divide read select project empty divided row caches.2 rows.2))).trans
                (divided caches.1.covered caches.2.covered bank).symm
  | _, _, _, _, .handoff _ tail, caches, bank =>
      mapBanks_flatten family divide read select project empty divided row (blocks := tail) caches bank
termination_by structural _ _ _ _ blocks _ _ => blocks

/-- Read actual request rows at the retained original covered-block boundaries.

Each callback receives the same whole ParentCache and an exact prefix of
one supplied global ordered bank. The literal dependent suffix is passed to
the original tail cache; stationary handoffs forward it unchanged. No
aggregate, primitive, model, block, source or observation is constructed.
-/
def mapRequests {Value : Type u}
    (read : ∀ {start finish : Canonical} {ambient : Geometry.Rational.Box}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {source : Owner (curve.polynomial.eval start)} (covered : CoveredTracedPath path source)
      (cache : ParentCache covered differential sheet), RequestedParents count allowance cache.parents → Value) :
    ∀ {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
      {target : Owner (curve.polynomial.eval finish)} {blocks : Blocks curve.polynomial start source finish target}
      (caches : ParentCaches differential sheet blocks), RequestedParents count allowance caches.parents → List Value :=
  mapBanks (fun parents _ => RequestedParents count allowance parents)
    (fun {_ _} _ _ requests => requests.split _ _) read

/-- Reading rows after one global refinement uses the same original row refinements and common floor.

The global ordered bank is refined once. This whole-list equality identifies
each actual retained row operation without executing a second refinement,
and stationary handoffs preserve the identical recursive tail.
-/
theorem mapRequests_refine {Value : Type u}
    (read : ∀ {start finish : Canonical} {ambient : Geometry.Rational.Box}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {source : Owner (curve.polynomial.eval start)} (covered : CoveredTracedPath path source)
      (cache : ParentCache covered differential sheet), RequestedParents count allowance cache.parents → Value) :
    ∀ {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
      {target : Owner (curve.polynomial.eval finish)} {blocks : Blocks curve.polynomial start source finish target}
      (caches : ParentCaches differential sheet blocks) (requests : RequestedParents count allowance caches.parents)
      (positive : 0 < allowance) (minimum : Nat),
    mapRequests read caches (requests.refine positive caches.proper minimum) =
      mapRequests (fun covered cache row => read covered cache (row.refine positive cache.proper minimum))
        caches requests
  | _, _, _, _, .nil _ _, _, _, _, _ => rfl
  | _, _, _, _, .cons covered tail, caches, requests, positive, minimum => by
      change ParentCache covered differential sheet × ParentCaches differential sheet tail at caches
      change RequestedParents count allowance (caches.1.parents ++ parents (blocks := tail) caches.2) at requests
      let rows := requests.split caches.1.parents (parents (blocks := tail) caches.2)
      have refined := requests.split_refine caches.1.parents (parents (blocks := tail) caches.2)
        positive caches.1.proper caches.2.proper minimum
      refine (congrArg (fun divided => read covered caches.1 divided.1 ::
        mapRequests read caches.2 divided.2) refined).trans ?_
      exact congrArg (fun values => read covered caches.1 (rows.1.refine positive caches.1.proper minimum) :: values)
        (mapRequests_refine read caches.2 rows.2 positive minimum)
  | _, _, _, _, .handoff _ tail, caches, requests, positive, minimum =>
      mapRequests_refine read (blocks := tail) caches requests positive minimum
termination_by structural _ _ _ _ blocks _ _ _ _ => blocks

/-- Grouping retained rows preserves the original global primitive-increment sum.

The local expressions refer to the same stored request prefixes and their
unchanged polynomial models. This erased equality does not reevaluate the
original aggregate's cached scalar values.
-/
theorem mapRequests_increments : ∀ {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
    {target : Owner (curve.polynomial.eval finish)} {blocks : Blocks curve.polynomial start source finish target}
    (caches : ParentCaches differential sheet blocks) (requests : RequestedParents count allowance caches.parents),
    gaussianSum (mapRequests (fun _ _ row => gaussianSum row.increments) caches requests) =
      gaussianSum requests.increments
  | _, _, _, _, .nil _ _, caches, requests => by
      change RequestedParents count allowance [] at requests
      cases requests
      rfl
  | _, _, _, _, .cons covered tail, caches, requests => by
      change ParentCache covered differential sheet × ParentCaches differential sheet tail at caches
      change RequestedParents count allowance (caches.1.parents ++ parents (blocks := tail) caches.2) at requests
      let rows := requests.split caches.1.parents (parents (blocks := tail) caches.2)
      change gaussianSum rows.1.increments +
        gaussianSum (mapRequests (fun _ _ row => gaussianSum row.increments) caches.2 rows.2) = _
      have grouped := (congrArg gaussianSum
        (requests.increments_split caches.1.parents (parents (blocks := tail) caches.2))).trans
          (gaussianSum_append rows.1.increments rows.2.increments)
      exact (congrArg (fun value => gaussianSum rows.1.increments + value)
        (mapRequests_increments caches.2 rows.2)).trans grouped.symm
  | _, _, _, _, .handoff _ tail, caches, requests =>
      mapRequests_increments (blocks := tail) caches requests
termination_by structural _ _ _ _ blocks _ _ => blocks

/-- Grouping retained rows preserves the actual original flattened child-block integral.

The same whole original child blocks are split at their retained parent
boundaries. The existing path-integral append law compares their exact
polynomial samples; it does not infer any geometric or sheet agreement.
-/
theorem mapRequests_integralSample : ∀ {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
    {target : Owner (curve.polynomial.eval finish)} {blocks : Blocks curve.polynomial start source finish target}
    (caches : ParentCaches differential sheet blocks) (requests : RequestedParents count allowance caches.parents),
    gaussianSum (mapRequests (fun _ _ row =>
      (PathModel.mk (row.blocks.children.map CenteredEdge.model)).integralSample) caches requests) =
      (PathModel.mk (requests.blocks.children.map CenteredEdge.model)).integralSample
  | _, _, _, _, .nil _ _, caches, requests => by
      change RequestedParents count allowance [] at requests
      cases requests
      rfl
  | _, _, _, _, .cons covered tail, caches, requests => by
      change ParentCache covered differential sheet × ParentCaches differential sheet tail at caches
      change RequestedParents count allowance (caches.1.parents ++ parents (blocks := tail) caches.2) at requests
      let rows := requests.split caches.1.parents (parents (blocks := tail) caches.2)
      change (PathModel.mk (rows.1.blocks.children.map CenteredEdge.model)).integralSample +
        gaussianSum (mapRequests (fun _ _ row =>
          (PathModel.mk (row.blocks.children.map CenteredEdge.model)).integralSample) caches.2 rows.2) = _
      have children := requests.children_split caches.1.parents (parents (blocks := tail) caches.2)
      have mapped := (congrArg (fun values => values.map CenteredEdge.model) children).trans
        (Map.map_append CenteredEdge.model rows.1.blocks.children rows.2.blocks.children)
      have grouped := (congrArg (fun values => (PathModel.mk values).integralSample) mapped).trans
        (PathModel.integralSample_mk_append (rows.1.blocks.children.map CenteredEdge.model)
          (rows.2.blocks.children.map CenteredEdge.model))
      exact (congrArg (fun value =>
        (PathModel.mk (rows.1.blocks.children.map CenteredEdge.model)).integralSample + value)
          (mapRequests_integralSample caches.2 rows.2)).trans grouped.symm
  | _, _, _, _, .handoff _ tail, caches, requests =>
      mapRequests_integralSample (blocks := tail) caches requests
termination_by structural _ _ _ _ blocks _ _ => blocks

end RequestRows

end ParentCaches

/-- The entire supplied covered-block chain with its actual parent caches and original paid primitive-sum request.

This exact Sigma view retains existing owners and request types. Every local
patch, indexed primitive, ordered child block, numerical integral and aggregate
budget belongs to the same original parent bank; no success premise is added.
-/
@[expose] def PrimitiveRequest {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
    {target : Owner (curve.polynomial.eval finish)} (blocks : Blocks curve.polynomial start source finish target)
    (differential : Differential genus) (sheet : Fin 2) (accuracy : Fraction.Rational) : Type 2 :=
  Σ retained : {retained : Blocks curve.polynomial start source finish target // retained = blocks},
  Σ caches : ParentCaches differential sheet retained.val,
    PrimitiveSumRequest caches.parents genus accuracy

/-- Acquire the original finite primitive request from internally derived coverage and properness of these same Blocks.

Each moving block's original ParentCache and the aggregate request are built
once. Stationary joins remain in the whole supplied chain and add no numerical
cells. The original request computes all local refinement and error budgets.
-/
@[expose] def primitiveRequest {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
    {target : Owner (curve.polynomial.eval finish)} (blocks : Blocks curve.polynomial start source finish target)
    (differential : Differential genus) (sheet : Fin 2) (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    PrimitiveRequest blocks differential sheet accuracy :=
  let caches := ParentCaches.build differential sheet blocks
  let request := PrimitiveSumRequest.acquire caches.covered caches.proper accuracy positive
  ⟨⟨blocks, rfl⟩, caches, request⟩

namespace PrimitiveRequest

open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

variable {start finish : Canonical} {source : Owner (curve.polynomial.eval start)}
variable {target : Owner (curve.polynomial.eval finish)} {blocks : Blocks curve.polynomial start source finish target}
variable {differential : Differential genus} {sheet : Fin 2} {accuracy : Fraction.Rational}

/-- The retained global primitive-sum cache equals the ordered sums of its actual original block rows.

Every row uses the same retained local allowance and request prefix. The
whole original aggregate remains the runtime owner of its cached scalar;
this proof does not assemble a per-block aggregate or reevaluate its data.
-/
theorem primitiveSum_eq_rows (request : PrimitiveRequest blocks differential sheet accuracy) :
    request.2.2.primitiveSum = gaussianSum
      (ParentCaches.mapRequests (fun _ _ row => gaussianSum row.increments) request.2.1 request.2.2.requests) :=
  (request.2.2.primitiveSum_eq.trans (congrArg gaussianSum request.2.2.increments_eq)).trans
    (ParentCaches.mapRequests_increments request.2.1 request.2.2.requests).symm

/-- The retained global integral cache equals the ordered integrals of those same stored child-block rows.

The full original aggregate and child blocks remain unchanged. The equality
uses their retained readbacks and the original polynomial path append law,
including empty rows and stationary handoffs.
-/
theorem integralSample_eq_rows (request : PrimitiveRequest blocks differential sheet accuracy) :
    request.2.2.integralSample = gaussianSum
      (ParentCaches.mapRequests (fun _ _ row =>
        (PathModel.mk (row.blocks.children.map CenteredEdge.model)).integralSample) request.2.1 request.2.2.requests) :=
  (request.2.2.integralSample_eq.trans
    (congrArg (fun childBlocks => (PathModel.mk (childBlocks.children.map CenteredEdge.model)).integralSample)
      request.2.2.blocks_eq)).trans
        (ParentCaches.mapRequests_integralSample request.2.1 request.2.2.requests).symm

end PrimitiveRequest

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.Blocks
