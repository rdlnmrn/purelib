module
import Purelib.Data.List.Membership
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

public section

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
  Polynomial.Geometry.Grid.ClearGrid polynomial ambient}

set_option genInjectivity false in
/-- One cached reversible root transport with its exact Gaussian endpoints and original frame-bank membership.

The connection retains both actual endpoint frames and the prepared transport rows between them. -/
structure RootEdgeEntry (frames : RootFrames grid) where
  /-- The retained starting base coordinate. -/ start : Gaussian.Basic.Canonical
  /-- The retained finishing base coordinate. -/ finish : Gaussian.Basic.Canonical
  /-- The starting coordinate is an actual vertex of the original grid. -/ first :
    Polynomial.Geometry.Grid.FromStates.ContainsVertex grid start
  /-- The finishing coordinate is an actual vertex of the original grid. -/ last :
    Polynomial.Geometry.Grid.FromStates.ContainsVertex grid finish
  /-- The cached reversible transport between these exact endpoint frame occurrences. -/ connection :
    SquareRoot.Grid.RootEdges.RootEdge (ambient := ambient) (frames.frameAt start first) (frames.frameAt finish last)

constructive_injectivity RootEdgeEntry

namespace RootEdgeEntry

variable {frames : RootFrames grid}

/-- Read the ordered pair of retained endpoint coordinates. -/
@[expose] def key (entry : SquareRoot.Grid.RootEdgeBank.RootEdgeEntry frames) : Gaussian.Basic.Canonical ×
  Gaussian.Basic.Canonical := (entry.start, entry.finish)

/-- Prepare one original grid edge using the already retained endpoint frame bank. -/
@[expose] def build (frames : RootFrames grid) {start finish : Gaussian.Basic.Canonical}
  (edge : Geometry.Grid.Walks.Edge grid start finish) : SquareRoot.Grid.RootEdgeBank.RootEdgeEntry frames :=
  ⟨start, finish, edge.vertices.1, edge.vertices.2, SquareRoot.Grid.RootEdges.RootFrames.edge frames edge⟩

/-- Reindex a cached edge only along equality of its ordered endpoint key. -/
@[expose] def atEndpoints (entry : SquareRoot.Grid.RootEdgeBank.RootEdgeEntry frames) (start finish :
  Gaussian.Basic.Canonical)
    (first : Polynomial.Geometry.Grid.FromStates.ContainsVertex grid start) (last :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex grid finish) (equal : entry.key = (start, finish)) :
    SquareRoot.Grid.RootEdges.RootEdge (ambient := ambient) (frames.frameAt start first) (frames.frameAt finish last) :=
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
    (first : Polynomial.Geometry.Grid.FromStates.ContainsVertex grid start) (last :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex grid finish) :
    (entries : List (SquareRoot.Grid.RootEdgeBank.RootEdgeEntry frames)) → (start, finish) ∈ entries.map
      SquareRoot.Grid.RootEdgeBank.RootEdgeEntry.key →
      SquareRoot.Grid.RootEdges.RootEdge (ambient := ambient) (frames.frameAt start first) (frames.frameAt finish last)
  | [], member => (List.not_mem_nil member).elim
  | head :: tail, member =>
      if equal : (start, finish) = head.key then head.atEndpoints start finish first last equal.symm
      else
        Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank.RootEdgeEntry.lookup frames start finish first last tail (by
          rcases List.Membership.mem_cons.mp member with same | remaining
          · exact (equal same).elim
          · exact remaining)

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
    (SquareRoot.Grid.RootEdgeBank.RootEdgeEntry frames)
  /-- Every original positive horizontal grid edge has its ordered endpoint key in the retained bank. -/ horizontal : ∀
    interval ∈ grid.xIntervals, ∀ line ∈ grid.horizontal,
    (Gaussian.Components.Basic.point interval.lower.coordinate line.coordinate, Gaussian.Components.Basic.point
      interval.upper.coordinate line.coordinate) ∈
      entries.map SquareRoot.Grid.RootEdgeBank.RootEdgeEntry.key
  /-- Every original positive vertical grid edge has its ordered endpoint key in the retained bank. -/ vertical : ∀
    interval ∈ grid.yIntervals, ∀ line ∈ grid.vertical,
    (Gaussian.Components.Basic.point line.coordinate interval.lower.coordinate, Gaussian.Components.Basic.point
      line.coordinate interval.upper.coordinate) ∈
      entries.map SquareRoot.Grid.RootEdgeBank.RootEdgeEntry.key

constructive_injectivity RootEdgeBank

namespace RootEdgeBank

variable {frames : RootFrames grid}

/-- Enumerate positive grid edges and cache their four directed sheet-transport rows.

The horizontal and vertical materializers retain their finite grid order
and endpoint memberships. Both endpoint frames come from the same stored bank. -/
@[expose] def build (frames : RootFrames grid) : SquareRoot.Grid.RootEdgeBank
  frames := open Purelib in by
  let horizontal := grid.xIntervals.attach.flatMap fun interval =>
    grid.horizontal.attach.map fun line => SquareRoot.Grid.RootEdgeBank.RootEdgeEntry.build frames (.horizontal
      interval.val interval.property line.val line.property)
  let vertical := grid.yIntervals.attach.flatMap fun interval =>
    grid.vertical.attach.map fun line => SquareRoot.Grid.RootEdgeBank.RootEdgeEntry.build frames (.vertical interval.val
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

open SquareRoot.Grid.RootEdgeBank
/-- Read a cached connection for an original grid edge.

Positive edges use the exact ordered endpoint key and retained coverage
witness. A reverse edge swaps the stored directions of that same connection. -/
@[expose] def edge (bank : SquareRoot.Grid.RootEdgeBank frames) : {start finish : Gaussian.Basic.Canonical}
  → (edge : Geometry.Grid.Walks.Edge grid start finish) →
    SquareRoot.Grid.RootEdges.RootEdge (ambient := ambient) (frames.frameAt start edge.vertices.1) (frames.frameAt
      finish edge.vertices.2)
  | _, _, .horizontal interval adjacent line member =>
      SquareRoot.Grid.RootEdgeBank.RootEdgeEntry.lookup frames _ _ _ _ bank.entries (bank.horizontal interval adjacent
        line member)
  | _, _, .vertical interval adjacent line member =>
      SquareRoot.Grid.RootEdgeBank.RootEdgeEntry.lookup frames _ _ _ _ bank.entries (bank.vertical interval adjacent
        line member)
  | _, _, .reverse original => (bank.edge original).reverse

/-- A reversed edge query reads the stored backward target of the same cached positive connection. -/
theorem edge_reverse_forward (bank : SquareRoot.Grid.RootEdgeBank frames) {start finish :
  Gaussian.Basic.Canonical}
    (edge : Geometry.Grid.Walks.Edge grid start finish) (sheet : Fin 2) :
    (bank.edge (.reverse edge)).forward.target sheet = (bank.edge edge).backward.target sheet := rfl

end RootEdgeBank

end Purelib.RootIsolation.SquareRoot.Grid
