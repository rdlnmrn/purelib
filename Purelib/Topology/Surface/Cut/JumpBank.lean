module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Topology.Surface.Cut.JumpPaths
meta import Mathlib.Tactic.Linter.Lint
import Purelib.Data.List.Append
import Purelib.Data.List.Map
open Purelib.Data.List

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.JumpPaths

open Purelib.Topology.Surface.Sewing.SewingProjection

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.ProjectedEdgePairs

@[expose] public section

/-!
# Cached complete banks of cut-jump cycles

Each entry retains its original projected edge pair, both cut words, both
closed surface words, and their exact prefix provenance. The bank covers the
pair list in order. Downstream consumers read these paths instead of doing
another boundary lookup or selecting an unrelated connector.
-/

namespace Purelib.Topology.Surface.Cut.JumpBank

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair ProjectedEdgePairing)
open Purelib.Topology.Surface.Cut.JumpPaths (CutJumpPaths)

variable {source target : Nat} {labels : Fin source → Fin target}

/-- Both edges of a retained pair occur in the complete ordered pair-occurrence list. -/
theorem ProjectedEdgePair.members {pair : ProjectedEdgePairs.ProjectedEdgePair labels} :
    (pairs : List (ProjectedEdgePairs.ProjectedEdgePair labels)) → pair ∈ pairs →
      pair.first ∈ ProjectedEdgePair.occurrences pairs ∧ pair.second ∈ ProjectedEdgePair.occurrences pairs
  | [], member => (List.not_mem_nil member).elim
  | first :: rest, member => by
      rcases Membership.mem_cons.mp member with same | member
      · cases same
        exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
      · have tail := Purelib.Topology.Surface.Cut.JumpBank.ProjectedEdgePair.members rest member
        exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ tail.1),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ tail.2)⟩

set_option genInjectivity false in
/-- One original projected edge pair with its retained endpoint-jump paths. -/
structure CutJumpEntry (labels : Fin source → Fin target) (boundary : List (Stokes.OrientedEdge source)) where
  /-- Original projected edge pair whose two endpoint jumps are represented. -/ pair :
    ProjectedEdgePairs.ProjectedEdgePair labels
  /-- Cached cut paths and their projections for this exact pair. -/ paths : JumpPaths.CutJumpPaths labels boundary pair

constructive_injectivity CutJumpEntry

set_option genInjectivity false in
open Purelib.Topology.Surface.Cut in
/-- Ordered endpoint-jump paths for every original cut pair.

The pair readback preserves the original list, including its order and repeated occurrences. -/
structure CutJumpBank (labels : Fin source → Fin target) (boundary : List (Stokes.OrientedEdge source))
    (pairs : List (ProjectedEdgePairs.ProjectedEdgePair labels)) where
  /-- Ordered bank of paired edges and their cached jump paths. -/ entries : List (JumpBank.CutJumpEntry labels
    boundary)
  /-- Reading the pairs from the bank recovers the original ordered pair list. -/ pairs_eq : entries.map
    Purelib.Topology.Surface.Cut.JumpBank.CutJumpEntry.pair = pairs

constructive_injectivity CutJumpBank

namespace CutJumpBank

variable {boundary : List (Stokes.OrientedEdge source)}

open Purelib.Topology.Surface.Cut
/-- Build and retain both endpoint-jump paths for every supplied pair.

Membership in the closed cut boundary supplies the original edge selections used by each path constructor. -/
def build (labels : Fin source → Fin target) (boundary : List (Stokes.OrientedEdge source))
    {anchor : Fin source} (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish boundary anchor
      anchor) :
    (pairs : List (ProjectedEdgePairs.ProjectedEdgePair labels)) → (∀ pair ∈ pairs, pair.first ∈ boundary ∧ pair.second
      ∈ boundary) →
    JumpBank.CutJumpBank labels boundary pairs
  | [], _ => ⟨[], rfl⟩
  | pair :: pairs, members =>
      let incident := members pair List.mem_cons_self
      let paths := CutJumpPaths.build labels boundary closed pair incident.1 incident.2
      let tail := Purelib.Topology.Surface.Cut.JumpBank.CutJumpBank.build labels boundary closed pairs (fun next member
        => members next (List.mem_cons_of_mem _ member))
      ⟨⟨pair, paths⟩ :: tail.entries, congrArg (List.cons pair) tail.pairs_eq⟩

/-- The jump bank contains exactly one entry for each original pair occurrence. -/
theorem length_eq {pairs : List (ProjectedEdgePairs.ProjectedEdgePair labels)} (bank : JumpBank.CutJumpBank labels
  boundary pairs) :
    bank.entries.length = pairs.length := by
  have equal := congrArg List.length bank.pairs_eq
  simpa only [Map.length_map] using equal

end CutJumpBank

namespace ProjectedEdgePairing

variable {boundary : List (Stokes.OrientedEdge source)}

open Purelib.Topology.Surface.Cut in
open Purelib.Topology.Surface.Cut.JumpBank in
/-- The incidence proof supplies membership of both occurrences. There is no caller-supplied path, successful search, or
homology-identification input. -/
def jumpPaths (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels boundary) {anchor : Fin source}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish boundary anchor anchor) :
    JumpBank.CutJumpBank labels boundary pairing.pairs :=
  CutJumpBank.build labels boundary closed pairing.pairs (by
    intro pair member
    have occurrences := ProjectedEdgePair.members pairing.pairs member
    exact ⟨(EdgeReordering.mem_iff pairing.incidence pair.first).mpr (Membership.mem_append.mpr (Or.inr occurrences.1)),
      (EdgeReordering.mem_iff pairing.incidence pair.second).mpr (Membership.mem_append.mpr (Or.inr occurrences.2))⟩)

end ProjectedEdgePairing

end Purelib.Topology.Surface.Cut.JumpBank
