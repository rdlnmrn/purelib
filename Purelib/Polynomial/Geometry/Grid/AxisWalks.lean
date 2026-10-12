module

import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map

public import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Total walks along adjacent retained grid coordinates

The two endpoint coordinates are located by finite comparisons in the stored
strictly ordered axis.  The increasing walk visits only consecutive entries;
decreasing traversal reverses that same walk, and equal endpoints emit no
edge.  There is no detour via a common origin and no certificate reacquisition.
-/

namespace Purelib.Polynomial.Geometry.Grid.AxisWalks

open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Data.List

universe u

variable {Alpha : Type u} {key : Alpha → Fraction.Rational}

set_option genInjectivity false in
/-- An executable path through actual adjacent intervals.

The endpoints index a finite oriented spine. Every nonempty step retains an original adjacent interval and its
membership in the supplied interval bank. -/
public inductive IncreasingWalk (intervals : List (Geometry.Grid.ClearGrid.Interval key)) : Fraction.Rational →
  Fraction.Rational → Type u
  /-- The empty walk from a coordinate to itself. -/ | nil (point : Fraction.Rational) :
    Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk intervals point point
  /-- Prepend an actual retained adjacent interval to a walk starting at its upper endpoint. -/ | cons (interval :
    Geometry.Grid.ClearGrid.Interval key) (member : interval ∈ intervals)
      {finish : Fraction.Rational} (tail : Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk intervals (key
        interval.upper) finish) :
      Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk intervals (key interval.lower) finish

constructive_injectivity IncreasingWalk

namespace IncreasingWalk

variable {intervals : List (Geometry.Grid.ClearGrid.Interval key)} {start finish : Fraction.Rational}

/-- Transport a retained increasing walk along an equality of start coordinates. -/
@[expose] public def castStart {other : Fraction.Rational} (walk : Geometry.Grid.AxisWalks.IncreasingWalk intervals
  start finish) (equal : start = other) :
    Geometry.Grid.AxisWalks.IncreasingWalk intervals other finish := equal ▸ walk

/-- Transport a retained increasing walk along an equality of finish coordinates. -/
@[expose] public def castFinish {other : Fraction.Rational} (walk : Geometry.Grid.AxisWalks.IncreasingWalk intervals
  start finish) (equal : finish = other) :
    Geometry.Grid.AxisWalks.IncreasingWalk intervals start other := equal ▸ walk

/-- Read the original adjacent intervals traversed by an increasing walk, in traversal order. -/
@[expose] public def edges : {start finish : Fraction.Rational} → Geometry.Grid.AxisWalks.IncreasingWalk intervals start
  finish → List (Geometry.Grid.ClearGrid.Interval key)
  | _, _, .nil _ => []
  | _, _, .cons interval _ tail => interval :: tail.edges

/-- The start coordinate of an increasing walk is at most its finish coordinate. -/
public theorem ordered : {start finish : Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk intervals
  start finish) → start ≤ finish
  | _, _, .nil _ => le_rfl
  | _, _, .cons interval _ tail => interval.ordered.le.trans tail.ordered

/-- Every emitted edge stays inside the original oriented interval. -/
public theorem edge_bounds : {start finish : Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk
  intervals start finish) →
    ∀ interval ∈ walk.edges, start ≤ key interval.lower ∧ key interval.upper ≤ finish
  | _, _, .nil _, _, member => (List.not_mem_nil member).elim
  | _, _, .cons first _ tail, interval, member => by
      rcases Membership.mem_cons.mp member with equal | member
      · subst interval
        exact ⟨le_rfl, tail.ordered⟩
      · have bounds := tail.edge_bounds interval member
        exact ⟨first.ordered.le.trans bounds.1, bounds.2⟩

/-- Every emitted edge belongs to the original interval bank. -/
public theorem edge_mem : {start finish : Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk intervals
  start finish) →
    ∀ interval ∈ walk.edges, interval ∈ intervals
  | _, _, .nil _, _, member => (List.not_mem_nil member).elim
  | _, _, .cons first firstMember tail, interval, member => by
      rcases Membership.mem_cons.mp member with equal | member
      · rw [equal]
        exact firstMember
      · exact tail.edge_mem interval member

end IncreasingWalk

/-- An adjacent interval of an axis tail remains adjacent in the full strictly ordered axis. -/
public theorem adjacent_tail_mem {head : Alpha} {tail : List Alpha}
    (ordered : (head :: tail).Pairwise (fun left right => key left < key right))
    (interval : Geometry.Grid.ClearGrid.Interval key) (member : interval ∈ Geometry.Grid.ClearGrid.Interval.adjacent
      tail (List.pairwise_cons.mp ordered).2) :
    interval ∈ Geometry.Grid.ClearGrid.Interval.adjacent (head :: tail) ordered := by
  cases tail with
  | nil => exact (List.not_mem_nil member).elim
  | cons next rest => exact List.mem_cons_of_mem _ member

/-- A retained coordinate unequal to the head coordinate belongs to the tail coordinate list.

The original membership constructor identifies either the displayed head key or an occurrence in the unchanged tail. The
supplied inequality excludes exactly the head case. -/
public theorem tail_key_member {head : Alpha} {tail : List Alpha} {coordinate : Fraction.Rational}
    (member : coordinate ∈ (head :: tail).map key) (different : coordinate ≠ key head) : coordinate ∈ tail.map key := by
  rcases Membership.mem_cons.mp member with equal | member
  · exact (different equal).elim
  · exact member

/-- Construct the increasing walk from the first axis entry to a retained target coordinate.

Each recursive step consumes one original adjacent interval and transports only its membership into the supplied
interval bank. -/
@[expose] public def fromHead (intervals : List (Geometry.Grid.ClearGrid.Interval key)) (target : Fraction.Rational) :
  (head : Alpha) → (tail : List Alpha) →
    (ordered : (head :: tail).Pairwise (fun left right => key left < key right)) →
    (∀ interval ∈ Geometry.Grid.ClearGrid.Interval.adjacent (head :: tail) ordered, interval ∈ intervals) →
    target ∈ (head :: tail).map key → Geometry.Grid.AxisWalks.IncreasingWalk intervals (key head) target
  | head, [], _, _, member =>
      (Geometry.Grid.AxisWalks.IncreasingWalk.nil (key head)).castFinish (Membership.mem_singleton.mp member).symm
  | head, next :: tail, ordered, included, member =>
      if equal : target = key head then
        (Geometry.Grid.AxisWalks.IncreasingWalk.nil (key head)).castFinish equal.symm
      else
        let interval : Geometry.Grid.ClearGrid.Interval key := ⟨head, next, (List.pairwise_cons.mp ordered).1 next
          List.mem_cons_self⟩
        let remaining := Purelib.Polynomial.Geometry.Grid.AxisWalks.fromHead intervals target next tail
          (List.pairwise_cons.mp ordered).2
          (fun interval member => included interval (Geometry.Grid.AxisWalks.adjacent_tail_mem ordered interval member))
            (Geometry.Grid.AxisWalks.tail_key_member member equal)
        .cons interval (included interval List.mem_cons_self) remaining

/-- If an increasing walk starts in the tail, its retained finish coordinate also belongs to the tail. -/
public theorem target_in_tail {head : Alpha} {tail : List Alpha} {start finish : Fraction.Rational}
    (ordered : (head :: tail).Pairwise (fun left right => key left < key right))
    (startMember : start ∈ tail.map key) (finishMember : finish ∈ (head :: tail).map key) (forward : start ≤ finish) :
    finish ∈ tail.map key := open Purelib in by
  rcases Map.mem_map.mp startMember with ⟨entry, member, equal⟩
  have before : key head < start := by
    rw [← equal]
    exact (List.pairwise_cons.mp ordered).1 entry member
  apply Geometry.Grid.AxisWalks.tail_key_member finishMember
  intro same
  have strict := before.trans_le forward
  rw [same] at strict
  exact (lt_irrefl _) strict

/-- Construct an increasing walk between two retained coordinates in a supplied interval bank.

Skip entries before the start and retain the original adjacent payloads and bank membership witnesses for all subsequent
steps. -/
@[expose] public def increasingIn (intervals : List (Geometry.Grid.ClearGrid.Interval key)) (start finish :
  Fraction.Rational) : (entries : List Alpha) →
    (ordered : entries.Pairwise (fun left right => key left < key right)) →
    (∀ interval ∈ Geometry.Grid.ClearGrid.Interval.adjacent entries ordered, interval ∈ intervals) →
    start ∈ entries.map key → finish ∈ entries.map key → start ≤ finish →
      Geometry.Grid.AxisWalks.IncreasingWalk intervals start finish
  | [], _, _, startMember, _, _ => (List.not_mem_nil startMember).elim
  | head :: tail, ordered, included, startMember, finishMember, forward =>
      if equal : start = key head then
        (Geometry.Grid.AxisWalks.fromHead intervals finish head tail ordered included finishMember).castStart equal.symm
      else
        let startTail := Geometry.Grid.AxisWalks.tail_key_member startMember equal
        let finishTail := Geometry.Grid.AxisWalks.target_in_tail ordered startTail finishMember forward
        Purelib.Polynomial.Geometry.Grid.AxisWalks.increasingIn intervals start finish tail (List.pairwise_cons.mp
          ordered).2
          (fun interval member => included interval (Geometry.Grid.AxisWalks.adjacent_tail_mem ordered interval member))
            startTail finishTail forward

/-- Walk directly between two increasing grid coordinates.  The prefix
before the start is skipped.  All steps target the original interval bank,
so recursive suffixes are not repeatedly copied just to reindex membership. -/
@[expose] public def increasing (start finish : Fraction.Rational) (entries : List Alpha)
    (ordered : entries.Pairwise (fun left right => key left < key right))
    (startMember : start ∈ entries.map key) (finishMember : finish ∈ entries.map key) (forward : start ≤ finish) :
    Geometry.Grid.AxisWalks.IncreasingWalk (Geometry.Grid.ClearGrid.Interval.adjacent entries ordered) start finish :=
  Geometry.Grid.AxisWalks.increasingIn (Geometry.Grid.ClearGrid.Interval.adjacent entries ordered) start finish entries
    ordered (fun _ member => member) startMember finishMember forward

set_option genInjectivity false in
/-- One orientation bit and one monotone retained path.

Forward traversal follows the stored increasing path from start to finish. Backward traversal uses the same retained
increasing spine in the opposite direction. -/
public inductive Walk (intervals : List (Geometry.Grid.ClearGrid.Interval key)) (start finish : Fraction.Rational) :
  Type u
  /-- Traverse a retained increasing path from the requested start to finish. -/ | forward (path :
    Geometry.Grid.AxisWalks.IncreasingWalk intervals start finish)
  /-- Traverse in reverse a retained increasing path from the requested finish to start. -/ | backward (path :
    Geometry.Grid.AxisWalks.IncreasingWalk intervals finish start)

constructive_injectivity Walk

/-- Construct an oriented walk between two retained coordinates of a strictly ordered axis.

Use the increasing walk in the appropriate direction; equal endpoints produce an empty increasing path. -/
@[expose] public def walk (entries : List Alpha) (ordered : entries.Pairwise (fun left right => key left < key right))
    (start finish : Fraction.Rational) (startMember : start ∈ entries.map key) (finishMember : finish ∈ entries.map key)
      :
    Geometry.Grid.AxisWalks.Walk (Geometry.Grid.ClearGrid.Interval.adjacent entries ordered) start finish :=
  if forward : start ≤ finish then .forward (Geometry.Grid.AxisWalks.increasing start finish entries ordered startMember
    finishMember forward)
  else .backward (Geometry.Grid.AxisWalks.increasing finish start entries ordered finishMember startMember (le_of_not_ge
    forward))

set_option genInjectivity false in
/-- A finite coordinate lookup preserving the original cached payload.

The selected entry belongs to the original axis and reads the requested rational coordinate. The finite scan retains
that payload rather than constructing a replacement line certificate. -/
public structure Lookup (entries : List Alpha) (coordinate : Fraction.Rational) where
  /-- The original entry found by the coordinate scan. -/ entry : Alpha
  /-- The found entry belongs to the original axis list. -/ member : entry ∈ entries
  /-- The found entry has the requested coordinate. -/ coordinate_eq : key entry = coordinate

constructive_injectivity Lookup

/-- Find a retained entry with the requested coordinate by a finite scan.

The result keeps the original payload, its membership witness and the exact coordinate equality. -/
@[expose] public def lookup (coordinate : Fraction.Rational) : (entries : List Alpha) → coordinate ∈ entries.map key →
  Geometry.Grid.AxisWalks.Lookup (key := key) entries coordinate
  | [], member => (List.not_mem_nil member).elim
  | head :: tail, member =>
      if equal : coordinate = key head then ⟨head, List.mem_cons_self, equal.symm⟩
      else
        let found := Purelib.Polynomial.Geometry.Grid.AxisWalks.lookup coordinate tail
          (Geometry.Grid.AxisWalks.tail_key_member member equal)
        ⟨found.entry, List.mem_cons_of_mem _ found.member, found.coordinate_eq⟩

end Purelib.Polynomial.Geometry.Grid.AxisWalks
