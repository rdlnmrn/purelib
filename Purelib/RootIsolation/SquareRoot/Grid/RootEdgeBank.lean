module
import Purelib.Data.List.Membership
import Purelib.Data.Prod.Equality
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
public import Purelib.Data.List.Attach
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.RootIsolation.SquareRoot.Grid.RootEdges
import Purelib.Riemann.RootContinuation.RootPathTransport

open Purelib.Polynomial.Geometry.Grid

public section

open Purelib.Data.Gaussian

/-!
# Shared finite banks of actual two-sheet edge transports

The canonical producer materializes every positive horizontal and vertical
edge once.  Reverse traversal reuses the other direction in that same entry.
Lookup checks only exact endpoint coordinates.  Generated banks can replace
the producer by supplying checked rows and finite coverage of the grid edges.
-/

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

open Purelib.Data
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  Geometry.Grid.ClearGrid polynomial ambient}

set_option genInjectivity false in
/-- One cached reversible root transport with its exact Gaussian endpoints and original frame-bank membership.

The connection retains both actual endpoint frames and the prepared transport rows between them. -/
structure RootEdgeEntry (frames : RootFrames grid) where
  /-- The retained starting base coordinate. -/ start : Gaussian.Basic.Canonical
  /-- The retained finishing base coordinate. -/ finish : Gaussian.Basic.Canonical
  /-- The starting coordinate is an actual vertex of the original grid. -/ first :
    FromStates.ContainsVertex grid start
  /-- The finishing coordinate is an actual vertex of the original grid. -/ last :
    FromStates.ContainsVertex grid finish
  /-- The cached reversible transport between these exact endpoint frame occurrences. -/ connection :
    RootEdges.RootEdge (ambient := ambient) (frames.frameAt start first) (frames.frameAt finish last)

constructive_injectivity RootEdgeEntry

namespace RootEdgeEntry

variable {frames : RootFrames grid}

/-- Read the ordered pair of retained endpoint coordinates. -/
@[expose] def key (entry : RootEdgeEntry frames) : Gaussian.Basic.Canonical ×
  Gaussian.Basic.Canonical := (entry.start, entry.finish)

/-- Prepare one original grid edge using the already retained endpoint frame bank. -/
@[expose] def build (frames : RootFrames grid) {start finish : Gaussian.Basic.Canonical}
  (edge : Walks.Edge grid start finish) : RootEdgeEntry frames :=
  ⟨start, finish, edge.vertices.1, edge.vertices.2, RootEdges.RootFrames.edge frames edge⟩

/-- Reindex a cached edge only along equality of its ordered endpoint key. -/
@[expose] def atEndpoints (entry : RootEdgeEntry frames) (start finish :
  Gaussian.Basic.Canonical)
    (first : FromStates.ContainsVertex grid start) (last :
      FromStates.ContainsVertex grid finish) (equal : entry.key = (start, finish)) :
    RootEdges.RootEdge (ambient := ambient) (frames.frameAt start first) (frames.frameAt finish last) :=
      by
  have startEq : entry.start = start := congrArg Prod.fst equal
  have finishEq : entry.finish = finish := congrArg Prod.snd equal
  cases startEq
  cases finishEq
  exact entry.connection

/-- Scan the retained edge list for the first exact ordered endpoint key.

The supplied membership proof guarantees a cached occurrence; the returned transport reuses that occurrence without
preparing a new edge. -/
@[expose] def lookup (frames : RootFrames grid) (start finish : Gaussian.Basic.Canonical)
    (first : FromStates.ContainsVertex grid start) (last :
      FromStates.ContainsVertex grid finish) :
    (entries : List (RootEdgeEntry frames)) → (start, finish) ∈ entries.map
      key →
      RootEdges.RootEdge (ambient := ambient) (frames.frameAt start first) (frames.frameAt finish last)
  | [], member => (List.not_mem_nil member).elim
  | head :: tail, member =>
      if equal : (start, finish) = head.key then head.atEndpoints start finish first last equal.symm
      else
        RootEdgeEntry.lookup frames start finish first last tail (by
          rcases List.Membership.mem_cons.mp member with same | remaining
          · exact (equal same).elim
          · exact remaining)

/-- Reindex a complete retained connection only by actual vertex incidence and whole endpoint-frame equations.

The grids have the SAME ambient box. Both original clear segments and
all four prepared rows stay in the exact original connection; only its
frame indices and erased grid-membership fields change.
-/
def reframe {fine : Geometry.Grid.ClearGrid polynomial ambient} (newFrames : RootFrames fine)
    (onFine : ∀ point, FromStates.ContainsVertex grid point → FromStates.ContainsVertex fine point)
    (same : ∀ point member, newFrames.frameAt point (onFine point member) = frames.frameAt point member)
    (entry : RootEdgeEntry frames) : RootEdgeEntry newFrames :=
  ⟨entry.start, entry.finish, onFine entry.start entry.first, onFine entry.finish entry.last,
    Eq.mpr (congrArg₂ (fun first last => RootEdges.RootEdge (polynomial := polynomial) (ambient := ambient)
      (start := entry.start) (finish := entry.finish) first last)
      (same entry.start entry.first) (same entry.finish entry.last)) entry.connection⟩

/-- Whole-frame reindexing retains the exact original ordered endpoint key. -/
theorem reframe_key {fine : Geometry.Grid.ClearGrid polynomial ambient} (newFrames : RootFrames fine)
    (onFine : ∀ point, FromStates.ContainsVertex grid point → FromStates.ContainsVertex fine point)
    (same : ∀ point member, newFrames.frameAt point (onFine point member) = frames.frameAt point member)
    (entry : RootEdgeEntry frames) : (reframe newFrames onFine same entry).key = entry.key := by rfl

/-- Exact type transport preserves its complete original value. -/
private theorem mpr_heq {first last : Type} (same : first = last) (value : last) :
    HEq (Eq.mpr same value) value := by
  cases same
  rfl

/-- The whole reindexed connection retains both original directions, actual traces, selections and row caches. -/
theorem reframe_connection_heq {fine : Geometry.Grid.ClearGrid polynomial ambient} (newFrames : RootFrames fine)
    (onFine : ∀ point, FromStates.ContainsVertex grid point → FromStates.ContainsVertex fine point)
    (same : ∀ point member, newFrames.frameAt point (onFine point member) = frames.frameAt point member)
    (entry : RootEdgeEntry frames) : HEq (reframe newFrames onFine same entry).connection entry.connection := by
  unfold reframe
  exact mpr_heq
    (congrArg₂ (fun first last => RootEdges.RootEdge (polynomial := polynomial) (ambient := ambient)
      (start := entry.start) (finish := entry.finish) first last)
      (same entry.start entry.first) (same entry.finish entry.last)) entry.connection

end RootEdgeEntry

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

namespace Purelib.RootIsolation.SquareRoot.Grid

open Purelib.Data
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  Geometry.Grid.ClearGrid polynomial ambient}

set_option genInjectivity false in
/-- A root edge bank retains cached connections and exact coverage of the grid's positive edges.

Both coverage witnesses identify ordered endpoint keys in the stored list.
Queries reuse these cached rows, including the stored reverse directions. -/
structure RootEdgeBank (frames : RootFrames grid) where
  /-- The retained finite list of prepared positive grid-edge connections. -/ entries : List
    (RootEdgeBank.RootEdgeEntry frames)
  /-- Every original positive horizontal grid edge has its ordered endpoint key in the retained bank. -/ horizontal : ∀
    interval ∈ grid.xIntervals, ∀ line ∈ grid.horizontal,
    (Components.Basic.point interval.lower.coordinate line.coordinate, Components.Basic.point
      interval.upper.coordinate line.coordinate) ∈
      entries.map RootEdgeBank.RootEdgeEntry.key
  /-- Every original positive vertical grid edge has its ordered endpoint key in the retained bank. -/ vertical : ∀
    interval ∈ grid.yIntervals, ∀ line ∈ grid.vertical,
    (Components.Basic.point line.coordinate interval.lower.coordinate, Components.Basic.point
      line.coordinate interval.upper.coordinate) ∈
      entries.map RootEdgeBank.RootEdgeEntry.key

constructive_injectivity RootEdgeBank

namespace RootEdgeBank

variable {frames : RootFrames grid}

/-- Enumerate positive grid edges and cache their four directed sheet-transport rows.

The horizontal and vertical materializers retain their finite grid order
and endpoint memberships. Both endpoint frames come from the same stored bank. -/
@[expose] def build (frames : RootFrames grid) : RootEdgeBank
  frames := open Purelib in by
  let horizontal := grid.xIntervals.attach.flatMap fun interval =>
    grid.horizontal.attach.map fun line => RootEdgeEntry.build frames (.horizontal
      interval.val interval.property line.val line.property)
  let vertical := grid.yIntervals.attach.flatMap fun interval =>
    grid.vertical.attach.map fun line => RootEdgeEntry.build frames (.vertical interval.val
      interval.property line.val line.property)
  refine ⟨horizontal ++ vertical, ?_, ?_⟩
  · intro interval adjacent line member
    apply Data.List.Map.mem_map.mpr
    refine ⟨RootEdgeEntry.build frames (.horizontal interval adjacent line member), Data.List.Membership.mem_append.mpr
      (Or.inl ?_), rfl⟩
    exact Data.List.Flatten.mem_flatMap.mpr ⟨⟨interval, adjacent⟩, Data.List.Attach.mem_attach _ _,
      Data.List.Map.mem_map.mpr ⟨⟨line, member⟩, Data.List.Attach.mem_attach _ _, rfl⟩⟩
  · intro interval adjacent line member
    apply Data.List.Map.mem_map.mpr
    refine ⟨RootEdgeEntry.build frames (.vertical interval adjacent line member), Data.List.Membership.mem_append.mpr
      (Or.inr ?_), rfl⟩
    exact Data.List.Flatten.mem_flatMap.mpr ⟨⟨interval, adjacent⟩, Data.List.Attach.mem_attach _ _,
      Data.List.Map.mem_map.mpr ⟨⟨line, member⟩, Data.List.Attach.mem_attach _ _, rfl⟩⟩

/-- The actual prepared-frame prefix followed by original missing-frame extension preserves every old frame. -/
private theorem extended_frameAt {fine : Geometry.Grid.ClearGrid polynomial ambient}
    (newFrames : RootFrames fine) (added : List (RootFrames.RootFrameEntry polynomial))
    (factory : newFrames = (frames.appendEntries added).extend fine)
    (onFine : ∀ point, FromStates.ContainsVertex grid point → FromStates.ContainsVertex fine point)
    (point : Gaussian.Basic.Canonical) (member : FromStates.ContainsVertex grid point) :
    newFrames.frameAt point (onFine point member) = frames.frameAt point member :=
  (congrArg (fun value : RootFrames fine => value.frameAt point (onFine point member)) factory).trans
    (((frames.appendEntries added).extend_frameAt fine point (onFine point member) member).trans
      (frames.appendEntries_frameAt added point member))

/-- Reindex the complete original ordered entry prefix to the actual cached extended frame bank. -/
def reframeEntries {fine : Geometry.Grid.ClearGrid polynomial ambient} (bank : RootEdgeBank frames)
    (newFrames : RootFrames fine) (added : List (RootFrames.RootFrameEntry polynomial))
    (factory : newFrames = (frames.appendEntries added).extend fine)
    (onFine : ∀ point, FromStates.ContainsVertex grid point → FromStates.ContainsVertex fine point) :
    List (RootEdgeEntry newFrames) :=
  bank.entries.map (RootEdgeEntry.reframe newFrames onFine (extended_frameAt newFrames added factory onFine))

/-- Whole-frame equality proofs expose the SAME original retained-entry map after frame transport.

The equality witness changes no stored connection. The existing original
map uses the same endpoint frames, and proof irrelevance identifies only
its erased frame-equality arguments, not any numerical data or Owner.
-/
theorem reframeEntries_eq {fine : Geometry.Grid.ClearGrid polynomial ambient} (bank : RootEdgeBank frames)
    (newFrames : RootFrames fine) (added : List (RootFrames.RootFrameEntry polynomial))
    (factory : newFrames = (frames.appendEntries added).extend fine)
    (onFine : ∀ point, FromStates.ContainsVertex grid point → FromStates.ContainsVertex fine point)
    (same : ∀ point member, newFrames.frameAt point (onFine point member) = frames.frameAt point member) :
    bank.reframeEntries newFrames added factory onFine =
      bank.entries.map (RootEdgeEntry.reframe newFrames onFine same) := by
  unfold reframeEntries
  rfl

/-- The complete original ordered key list survives whole-connection frame transport unchanged. -/
theorem reframeEntries_keys {fine : Geometry.Grid.ClearGrid polynomial ambient} (bank : RootEdgeBank frames)
    (newFrames : RootFrames fine) (added : List (RootFrames.RootFrameEntry polynomial))
    (factory : newFrames = (frames.appendEntries added).extend fine)
    (onFine : ∀ point, FromStates.ContainsVertex grid point → FromStates.ContainsVertex fine point) :
    (bank.reframeEntries newFrames added factory onFine).map RootEdgeEntry.key =
      bank.entries.map RootEdgeEntry.key := by
  have mapped : ∀ entries : List (RootEdgeEntry frames),
      (entries.map (RootEdgeEntry.reframe newFrames onFine
        (extended_frameAt newFrames added factory onFine))).map RootEdgeEntry.key =
          entries.map RootEdgeEntry.key := by
    intro entries
    induction entries with
    | nil => rfl
    | cons entry tail retained =>
        change (RootEdgeEntry.reframe newFrames onFine
          (extended_frameAt newFrames added factory onFine) entry).key :: _ = entry.key :: _
        rw [RootEdgeEntry.reframe_key, retained]
  exact mapped bank.entries

/-- Cache only positive fine-edge occurrences whose endpoint keys are absent from the retained original prefix. -/
def missingEntries {fine : Geometry.Grid.ClearGrid polynomial ambient} (newFrames : RootFrames fine)
    (keys : List (Gaussian.Basic.Canonical × Gaussian.Basic.Canonical)) : List (RootEdgeEntry newFrames) :=
  (fine.xIntervals.attach.flatMap fun interval => fine.horizontal.attach.flatMap fun line =>
    let edge := Walks.Edge.horizontal (grid := fine) interval.val interval.property line.val line.property
    if (Components.Basic.point interval.val.lower.coordinate line.val.coordinate,
      Components.Basic.point interval.val.upper.coordinate line.val.coordinate) ∈ keys then []
    else [RootEdgeEntry.build newFrames edge]) ++
  (fine.yIntervals.attach.flatMap fun interval => fine.vertical.attach.flatMap fun line =>
    let edge := Walks.Edge.vertical (grid := fine) interval.val interval.property line.val line.property
    if (Components.Basic.point line.val.coordinate interval.val.lower.coordinate,
      Components.Basic.point line.val.coordinate interval.val.upper.coordinate) ∈ keys then []
    else [RootEdgeEntry.build newFrames edge])

/-- Extend the original same-ambient edge bank, retaining its whole ordered prefix and building only absent keys.

The supplied frame cache is the original seeded missing-frame extension.
Old connections retain both stored directions and all actual rows. Every
absent positive fine-edge occurrence is genuine new RootEdge work; it is
not a replay or relabeling of an old multi-segment Point connection.
-/
def extend {fine : Geometry.Grid.ClearGrid polynomial ambient} (bank : RootEdgeBank frames)
    (newFrames : RootFrames fine) (added : List (RootFrames.RootFrameEntry polynomial))
    (factory : newFrames = (frames.appendEntries added).extend fine)
    (onFine : ∀ point, FromStates.ContainsVertex grid point → FromStates.ContainsVertex fine point) :
    RootEdgeBank newFrames := by
  let original := bank.reframeEntries newFrames added factory onFine
  let keys := original.map RootEdgeEntry.key
  let addedEdges := missingEntries newFrames keys
  refine ⟨original ++ addedEdges, ?_, ?_⟩
  · intro interval adjacent line member
    let key := (Components.Basic.point interval.lower.coordinate line.coordinate,
      Components.Basic.point interval.upper.coordinate line.coordinate)
    by_cases present : key ∈ keys
    · obtain ⟨entry, listed, equal⟩ := Data.List.Map.mem_map.mp present
      exact Data.List.Map.mem_map.mpr ⟨entry, Data.List.Membership.mem_append.mpr (Or.inl listed), equal⟩
    · let edge := Walks.Edge.horizontal (grid := fine) interval adjacent line member
      apply Data.List.Map.mem_map.mpr
      refine ⟨RootEdgeEntry.build newFrames edge, Data.List.Membership.mem_append.mpr (Or.inr ?_), rfl⟩
      apply Data.List.Membership.mem_append.mpr
      apply Or.inl
      apply Data.List.Flatten.mem_flatMap.mpr
      refine ⟨⟨interval, adjacent⟩, Data.List.Attach.mem_attach _ _, ?_⟩
      apply Data.List.Flatten.mem_flatMap.mpr
      refine ⟨⟨line, member⟩, Data.List.Attach.mem_attach _ _, ?_⟩
      change RootEdgeEntry.build newFrames edge ∈ (if key ∈ keys then [] else [RootEdgeEntry.build newFrames edge])
      rewrite [if_neg present]
      exact Data.List.Membership.mem_cons.mpr (Or.inl rfl)
  · intro interval adjacent line member
    let key := (Components.Basic.point line.coordinate interval.lower.coordinate,
      Components.Basic.point line.coordinate interval.upper.coordinate)
    by_cases present : key ∈ keys
    · obtain ⟨entry, listed, equal⟩ := Data.List.Map.mem_map.mp present
      exact Data.List.Map.mem_map.mpr ⟨entry, Data.List.Membership.mem_append.mpr (Or.inl listed), equal⟩
    · let edge := Walks.Edge.vertical (grid := fine) interval adjacent line member
      apply Data.List.Map.mem_map.mpr
      refine ⟨RootEdgeEntry.build newFrames edge, Data.List.Membership.mem_append.mpr (Or.inr ?_), rfl⟩
      apply Data.List.Membership.mem_append.mpr
      apply Or.inr
      apply Data.List.Flatten.mem_flatMap.mpr
      refine ⟨⟨interval, adjacent⟩, Data.List.Attach.mem_attach _ _, ?_⟩
      apply Data.List.Flatten.mem_flatMap.mpr
      refine ⟨⟨line, member⟩, Data.List.Attach.mem_attach _ _, ?_⟩
      change RootEdgeEntry.build newFrames edge ∈ (if key ∈ keys then [] else [RootEdgeEntry.build newFrames edge])
      rewrite [if_neg present]
      exact Data.List.Membership.mem_cons.mpr (Or.inl rfl)

/-- The extended bank stores the SAME complete transported old prefix before all genuinely new positive-edge work. -/
theorem extend_entries {fine : Geometry.Grid.ClearGrid polynomial ambient} (bank : RootEdgeBank frames)
    (newFrames : RootFrames fine) (added : List (RootFrames.RootFrameEntry polynomial))
    (factory : newFrames = (frames.appendEntries added).extend fine)
    (onFine : ∀ point, FromStates.ContainsVertex grid point → FromStates.ContainsVertex fine point) :
    (bank.extend newFrames added factory onFine).entries =
      bank.reframeEntries newFrames added factory onFine ++
        missingEntries newFrames ((bank.reframeEntries newFrames added factory onFine).map RootEdgeEntry.key) := by rfl

open SquareRoot.Grid.RootEdgeBank
/-- Read a cached connection for an original grid edge.

Positive edges use the exact ordered endpoint key and retained coverage
witness. A reverse edge swaps the stored directions of that same connection. -/
@[expose] def edge (bank : RootEdgeBank frames) : {start finish : Gaussian.Basic.Canonical}
  → (edge : Walks.Edge grid start finish) →
    RootEdges.RootEdge (ambient := ambient) (frames.frameAt start edge.vertices.1) (frames.frameAt
      finish edge.vertices.2)
  | _, _, .horizontal interval adjacent line member =>
      RootEdgeEntry.lookup frames _ _ _ _ bank.entries (bank.horizontal interval adjacent
        line member)
  | _, _, .vertical interval adjacent line member =>
      RootEdgeEntry.lookup frames _ _ _ _ bank.entries (bank.vertical interval adjacent
        line member)
  | _, _, .reverse original => (bank.edge original).reverse

/-- A reversed edge query reads the stored backward target of the same cached positive connection. -/
theorem edge_reverse_forward (bank : RootEdgeBank frames) {start finish :
  Gaussian.Basic.Canonical}
    (edge : Walks.Edge grid start finish) (sheet : Fin 2) :
    (bank.edge (.reverse edge)).forward.target sheet = (bank.edge edge).backward.target sheet := rfl

end RootEdgeBank

end Purelib.RootIsolation.SquareRoot.Grid
