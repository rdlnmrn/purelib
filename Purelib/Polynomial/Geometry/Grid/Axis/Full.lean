module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Complete adjacent-axis walks and their exact edge sums

An axis containing both bounds visits every retained adjacent interval once.
Its executable spine is built directly from the ordered list, without four
independent endpoint searches when assembling an enclosing frame.
-/

namespace Purelib.Polynomial.Geometry.Grid.Axis.Full

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Data.List

namespace Interval

universe u
variable {Alpha : Type u} {key : Alpha → Fraction.Rational}

/-- The final payload read from a nonempty axis belongs to that axis. -/
public theorem lastFrom_mem (first : Alpha) (rest : List Alpha) : Geometry.Grid.CellBoundary.Interval.lastFrom first
  rest ∈ first :: rest := by
  induction rest generalizing first with
  | nil => exact List.mem_cons_self
  | cons next rest ih => exact List.mem_cons_of_mem _ (ih next)

/-- The first key bounds every key in a strictly ordered nonempty axis from below.

The selected key is either the retained first payload or a later occurrence. Strict pairwise ordering supplies the
latter bound without changing the selected entry. -/
public theorem first_le_key (first : Alpha) (rest : List Alpha)
    (ordered : (first :: rest).Pairwise (fun left right => key left < key right))
    {coordinate : Fraction.Rational} (member : coordinate ∈ (first :: rest).map key) : key first ≤ coordinate := open
      Purelib in by
  obtain ⟨entry, member, equal⟩ := Map.mem_map.mp member
  rw [← equal]
  rcases Membership.mem_cons.mp member with same | member
  · rewrite [same]
    exact Fraction.Order.Basic.le_refl _
  · exact ((List.pairwise_cons.mp ordered).1 entry member).le

/-- The last key bounds every key in a strictly ordered nonempty axis from above.

Structural induction follows the retained axis tail to its final payload. Strict pairwise ordering bounds earlier
occurrences by that same final key. -/
public theorem key_le_last (first : Alpha) (rest : List Alpha)
    (ordered : (first :: rest).Pairwise (fun left right => key left < key right))
    {coordinate : Fraction.Rational} (member : coordinate ∈ (first :: rest).map key) : coordinate ≤ key
      (Geometry.Grid.CellBoundary.Interval.lastFrom first rest) := by
  induction rest generalizing first coordinate with
  | nil => exact (Membership.mem_singleton.mp member).le
  | cons next rest ih =>
      rcases Membership.mem_cons.mp member with same | member
      · rw [same]
        exact ((List.pairwise_cons.mp ordered).1 next List.mem_cons_self).le.trans
          (ih next (List.pairwise_cons.mp ordered).2 List.mem_cons_self)
      · exact ih next (List.pairwise_cons.mp ordered).2 member

/-- Construct an increasing walk through every adjacent interval of a nonempty ordered axis.

The supplied inclusion places each original interval in the retained ambient interval list. -/
@[expose] public def fullIn (intervals : List (Geometry.Grid.ClearGrid.Interval key)) (first : Alpha) (rest : List
  Alpha)
    (ordered : (first :: rest).Pairwise (fun left right => key left < key right))
    (included : ∀ interval ∈ Geometry.Grid.ClearGrid.Interval.adjacent (first :: rest) ordered, interval ∈ intervals) :
    Geometry.Grid.AxisWalks.IncreasingWalk intervals (key first) (key (Geometry.Grid.CellBoundary.Interval.lastFrom
      first rest)) :=
  match rest with
  | [] => .nil (key first)
  | next :: tail =>
      .cons ⟨first, next, (List.pairwise_cons.mp ordered).1 next List.mem_cons_self⟩ (included _ List.mem_cons_self)
        (Purelib.Polynomial.Geometry.Grid.Axis.Full.Interval.fullIn intervals next tail (List.pairwise_cons.mp
          ordered).2 (fun interval member =>
          included interval (List.mem_cons_of_mem _ member)))

/-- The complete axis walk retains exactly the original adjacent-interval list. -/
private theorem fullIn_edges (intervals : List (Geometry.Grid.ClearGrid.Interval key)) (first : Alpha) (rest : List
  Alpha)
    (ordered : (first :: rest).Pairwise (fun left right => key left < key right))
    (included : ∀ interval ∈ Geometry.Grid.ClearGrid.Interval.adjacent (first :: rest) ordered, interval ∈ intervals) :
    (Geometry.Grid.Axis.Full.Interval.fullIn intervals first rest ordered included).edges =
      Geometry.Grid.ClearGrid.Interval.adjacent (first :: rest) ordered := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih => exact congrArg (List.cons _) (ih next _ _)

set_option genInjectivity false in
/-- Cached first/last payloads are read from the actual ordered axis.

The record retains its exact nonempty list decomposition and the two requested endpoint equalities. Complete axis
traversal consumes those original adjacent intervals. -/
public structure Span (entries : List Alpha) (lower upper : Fraction.Rational) where
  /-- The first payload of the original nonempty axis. -/ first : Alpha
  /-- The remaining payloads of the original axis. -/ rest : List Alpha
  /-- The original axis is exactly the retained first payload followed by the retained tail. -/ entries_eq : entries =
    first :: rest
  /-- The first payload's key is the requested lower endpoint. -/ lower_eq : key first = lower
  /-- The final payload's key is the requested upper endpoint. -/ upper_eq : key
    (Geometry.Grid.CellBoundary.Interval.lastFrom first rest) = upper

constructive_injectivity Span

namespace Span

variable {entries : List Alpha} {lower upper : Fraction.Rational}

/-- Identify the first and last payloads of an ordered axis containing both bounds.

All keys lie between those bounds; the constructor retains the original nonempty list decomposition. -/
@[expose] public def ofBounds (entries : List Alpha) (ordered : entries.Pairwise (fun left right => key left < key
  right))
    (inside : ∀ entry ∈ entries, lower ≤ key entry ∧ key entry ≤ upper)
    (lowerMember : lower ∈ entries.map key) (upperMember : upper ∈ entries.map key) :
      Geometry.Grid.Axis.Full.Interval.Span (key := key) entries lower upper :=
  match entries with
  | [] => (List.not_mem_nil lowerMember).elim
  | first :: rest =>
      ⟨first, rest, rfl,
        le_antisymm (Geometry.Grid.Axis.Full.Interval.first_le_key first rest ordered lowerMember) (inside first
          List.mem_cons_self).1,
        le_antisymm (inside _ (Geometry.Grid.Axis.Full.Interval.lastFrom_mem first rest)).2
          (Geometry.Grid.Axis.Full.Interval.key_le_last first rest ordered upperMember)⟩

/-- Build the complete increasing walk between a span's certified endpoint coordinates. -/
@[expose] public def walk (span : Geometry.Grid.Axis.Full.Interval.Span (key := key) entries lower upper)
    (ordered : entries.Pairwise (fun left right => key left < key right)) : Geometry.Grid.AxisWalks.IncreasingWalk
      (Geometry.Grid.ClearGrid.Interval.adjacent entries ordered) lower upper := by
  rcases span with ⟨first, rest, rfl, lowerEq, upperEq⟩
  exact ((Geometry.Grid.Axis.Full.Interval.fullIn _ first rest ordered (fun _ member => member)).castStart
    lowerEq).castFinish upperEq

/-- The span walk consumes exactly the adjacent intervals of its original ordered axis. -/
public theorem walk_edges (span : Geometry.Grid.Axis.Full.Interval.Span (key := key) entries lower upper)
    (ordered : entries.Pairwise (fun left right => key left < key right)) :
    (span.walk ordered).edges = Geometry.Grid.ClearGrid.Interval.adjacent entries ordered := by
  rcases span with ⟨first, rest, rfl, rfl, rfl⟩
  exact Geometry.Grid.Axis.Full.Interval.fullIn_edges _ first rest ordered (fun _ member => member)

end Span
end Interval

namespace EdgeValues

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}

/-- Endpoint equality transport preserves a walk's edge-value sum. -/
public theorem walk_castEndpoints (values : Geometry.Grid.CellBoundary.EdgeValues) {start finish first last :
  Gaussian.Basic.Canonical}
    (walk : Geometry.Grid.Walks.Walk grid start finish) (startEq : start = first) (finishEq : finish = last) :
    values.walk (walk.castEndpoints startEq finishEq) = values.walk walk := by
  cases startEq
  cases finishEq
  rfl

/-- A horizontal increasing walk sums the readings of its actual retained intervals. -/
public theorem walk_horizontalIncreasing (values : Geometry.Grid.CellBoundary.EdgeValues) (line :
  Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient) (member : line ∈ grid.horizontal) :
    {start finish : Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals start finish) →
    values.walk (Geometry.Grid.Walks.Walk.horizontalIncreasing line member walk) =
      Geometry.Grid.CellBoundary.sumValues (fun interval => values.horizontal interval.lower.coordinate
        interval.upper.coordinate line.coordinate) walk.edges
  | _, _, .nil _ => rfl
  | _, _, .cons _ _ tail => congrArg (fun total => _ + total)
    (Purelib.Polynomial.Geometry.Grid.Axis.Full.EdgeValues.walk_horizontalIncreasing values line member tail)

/-- A vertical increasing walk sums the readings of its actual retained intervals. -/
public theorem walk_verticalIncreasing (values : Geometry.Grid.CellBoundary.EdgeValues) (line :
  Geometry.Grid.ClearGrid.VerticalLine polynomial ambient) (member : line ∈ grid.vertical) :
    {start finish : Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals start finish) →
    values.walk (Geometry.Grid.Walks.Walk.verticalIncreasing line member walk) =
      Geometry.Grid.CellBoundary.sumValues (fun interval => values.vertical line.coordinate interval.lower.coordinate
        interval.upper.coordinate) walk.edges
  | _, _, .nil _ => rfl
  | _, _, .cons _ _ tail => congrArg (fun total => _ + total)
    (Purelib.Polynomial.Geometry.Grid.Axis.Full.EdgeValues.walk_verticalIncreasing values line member tail)

end EdgeValues

end Purelib.Polynomial.Geometry.Grid.Axis.Full
