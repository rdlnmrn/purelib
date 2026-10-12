module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Data.List.Sort.RationalKey.Basic
import Purelib.Data.List.Map
public import Purelib.Data.List.Filter
import Purelib.Polynomial.Geometry.Grid.Incidence
import Purelib.Data.Rat.Fraction

import Purelib.Data.List.Sort.Key
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Polynomial.Geometry.Grid.Axis.Full
public import Purelib.Polynomial.Geometry.Grid.AxisNeighbors
import Init.Data.List.Lemmas
import Init.Prelude
import Init.SimpLemmas
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint

/-!
# Finite interval partitions containing prescribed rational cuts

Sort and deduplicate the in-range cuts together with the two endpoints.
The cached adjacent intervals cover the entire original interval, retain
every requested in-range coordinate as an endpoint, and preserve total
width exactly. Out-of-range cuts are excluded by an exact membership law.
-/

namespace Purelib.Geometry.Rectangle

open Purelib
open Purelib.Algebra.FiniteSum.Rational
open Purelib.Data.List.Sort
open Purelib.Data.Rat
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.Axis.Full.Interval
open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Data.List

namespace Partition.PreparedAxisPartitions

/-- The rational coordinate type of the axis partition. -/
public abbrev Coordinate := Fraction.Rational
/-- A proper coordinate interval with the identity key. -/
public abbrev Interval := ClearGrid.Interval (id : Coordinate →
  Coordinate)

end Partition.PreparedAxisPartitions

open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk)
open Purelib.Polynomial.Geometry.Grid.Axis.Full.Interval (Span)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)

namespace Partition.PreparedAxisPartitions

/-- Sorted insertion adds at most one coordinate.

The original insertion either keeps an equal coordinate, prepends a new one, or
recurses into the unchanged tail. These cases add at most one entry. -/
private theorem insert_length (point : Coordinate) (points : List
  Coordinate) :
    (RationalKey.Basic.insert id point points).length ≤ points.length + 1 := by
  induction points with
  | nil => exact le_rfl
  | cons head tail ih =>
      unfold RationalKey.Basic.insert
      split
      · exact le_rfl
      · split
        · simpa only [List.length_cons] using Nat.succ_le_succ ih
        · exact Nat.le_succ _

/-- Sorting and deduplicating cannot increase the coordinate count.

Each retained tail is sorted before inserting the displayed head. The insertion
bound accounts for at most one entry per original occurrence. -/
public theorem sort_length (points : List Coordinate) : (RationalKey.Basic.sort id points).length
  ≤ points.length := by
  induction points with
  | nil => exact le_rfl
  | cons head tail ih => exact (insert_length head _).trans (Nat.succ_le_succ ih)

/-- A strictly ordered coordinate list has one fewer adjacent intervals.

A nonempty strictly ordered axis contributes one adjacent interval per
following coordinate. Empty and singleton axes retain zero intervals. -/
public theorem adjacent_length (points : List Coordinate) (ordered : points.Pairwise (fun first
  last => first < last)) :
    (Interval.adjacent (key := id) points ordered).length = points.length - 1 := by
  induction points with
  | nil => rfl
  | cons first rest ih =>
      cases rest with
      | nil => rfl
      | cons next tail =>
          change (Interval.adjacent (key := id) (next :: tail) _).length + 1 = _
          rw [ih]
          simp only [List.length_cons]
          omega

end Partition.PreparedAxisPartitions

set_option genInjectivity false in
/-- Both geometry and counts are retained as data. The exact coordinate membership
law also admits independently generated sorted caches. -/
public structure AxisPartition (lower upper : Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate) (cuts :
    List
  Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate) where
  /-- The original lower endpoint is strictly below the upper endpoint. -/ proper : lower < upper
  /-- The cached sorted list of endpoints and in-range cuts. -/ coordinates : List
    Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate
  /-- The cached coordinates are strictly increasing. -/ ordered : coordinates.Pairwise (fun first last => first < last)
  /-- Exactly the endpoints and requested in-range cuts occur in the coordinate
cache. -/ coordinates_spec : ∀ point, point ∈ coordinates ↔
    point = lower ∨ point = upper ∨ (point ∈ cuts ∧ lower ≤ point ∧ point ≤ upper)
  /-- The cached adjacent intervals. -/ intervals : List Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval
  /-- The interval cache is the adjacent-interval construction on the coordinates. -/ intervals_eq : intervals =
    Interval.adjacent coordinates ordered
  /-- The cached number of intervals. -/ count : Nat
  /-- The cached count is the actual interval-list length. -/ count_eq : count = intervals.length
  /-- The number of intervals is at most one more than the number of requested cuts. -/ count_le : count ≤ cuts.length +
    1
  /-- An increasing walk covering the original interval with retained intervals. -/ walk : AxisWalks.IncreasingWalk
    intervals lower upper
  /-- The covering walk traverses exactly the cached interval list. -/ walk_edges : walk.edges = intervals

constructive_injectivity AxisPartition

namespace AxisPartition

variable {lower upper : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate} {cuts : List
  Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate}

/-- Consecutive adjacent intervals share their common endpoint.

The later-index bound selects two consecutive intervals of the original
adjacent construction. Their stored common coordinate is unchanged by the
recursive tail. -/
private theorem adjacent_consecutive (points : List Partition.PreparedAxisPartitions.Coordinate)
    (ordered : points.Pairwise (fun first last => first < last)) :
    ∀ (index : Nat)
      (later : index + 1 < (Interval.adjacent (key := id) points ordered).length),
      ((Interval.adjacent (key := id) points ordered)[index]'(Nat.lt_trans (Nat.lt_succ_self _) later)).upper =
        ((Interval.adjacent (key := id) points ordered)[index + 1]'later).lower := by
  induction points with
  | nil =>
      intro index later
      simp only [Interval.adjacent, List.length_nil] at later
      omega
  | cons first rest ih =>
      cases rest with
      | nil =>
          intro index later
          simp only [Interval.adjacent, List.length_nil] at later
          omega
      | cons second tail =>
          intro index later
          cases index with
          | zero =>
              cases tail with
              | nil =>
                  simp only [Interval.adjacent, List.length_cons, List.length_nil] at later
                  omega
              | cons third remaining => rfl
          | succ index =>
              have previous := ih (List.pairwise_cons.mp ordered).2 index (by
                simp only [Interval.adjacent, List.length_cons] at later
                omega)
              exact previous

/-- Transport consecutive-endpoint equalities across equality of interval lists.

The supplied equality identifies the entire retained interval lists. It
transports both bounded reads and their exact shared endpoint together. -/
private theorem consecutive_transport {first last : List Partition.PreparedAxisPartitions.Interval} (equal : first =
    last)
    (consecutive : ∀ (index : Nat) (later : index + 1 < first.length),
      (first[index]'(Nat.lt_trans (Nat.lt_succ_self _) later)).upper =
        (first[index + 1]'later).lower) :
    ∀ (index : Nat) (later : index + 1 < last.length),
      (last[index]'(Nat.lt_trans (Nat.lt_succ_self _) later)).upper =
        (last[index + 1]'later).lower := by
  cases equal
  exact consecutive

/-- Consecutive retained partition intervals share an endpoint.

The interval cache equals the original adjacent construction on the cached
ordered coordinates. Transporting its two consecutive reads preserves their
common endpoint. -/
public theorem consecutive (partition : AxisPartition lower upper cuts) (index : Nat)
    (later : index + 1 < partition.intervals.length) :
    (partition.intervals[index]'(Nat.lt_trans (Nat.lt_succ_self _) later)).upper =
      (partition.intervals[index + 1]'later).lower := by
  exact consecutive_transport partition.intervals_eq.symm
    (adjacent_consecutive partition.coordinates partition.ordered) index later

/-- Construct a partition containing every in-range requested cut.

Filter the cuts to the closed interval, sort and deduplicate them with both
endpoints, and cache adjacent intervals, their count bound and their increasing
covering walk. -/
@[expose] public def build (lower upper : Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate) (proper :
  lower < upper) (cuts : List Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate) :
  AxisPartition lower upper cuts := by
  let candidates := lower :: upper :: cuts.filter (fun point => decide (lower ≤ point ∧ point ≤ upper))
  let coordinates := RationalKey.Basic.sort id candidates
  have ordered := RationalKey.Basic.pairwise_sort id candidates
  have spec (point : Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate) : point ∈ coordinates ↔
      point = lower ∨ point = upper ∨ (point ∈ cuts ∧ lower ≤ point ∧ point ≤ upper) := by
    have sorted := RationalKey.Basic.keys_sort id candidates point
    rewrite [Map.map_id, Map.map_id] at sorted
    constructor
    · intro member
      rcases Membership.mem_cons.mp (sorted.mp member) with atLower | member
      · exact Or.inl atLower
      · rcases Membership.mem_cons.mp member with atUpper | member
        · exact Or.inr (Or.inl atUpper)
        · obtain ⟨cutMember, accepted⟩ := Filter.mem_filter.mp member
          exact Or.inr (Or.inr ⟨cutMember, of_decide_eq_true accepted⟩)
    · intro member
      apply sorted.mpr
      rcases member with atLower | atUpper | member
      · exact Membership.mem_cons.mpr (Or.inl atLower)
      · exact Membership.mem_cons.mpr (Or.inr (Membership.mem_cons.mpr (Or.inl atUpper)))
      · exact Membership.mem_cons.mpr (Or.inr (Membership.mem_cons.mpr (Or.inr
          (Filter.mem_filter.mpr ⟨member.1, decide_eq_true member.2⟩))))
  have bounded (point : Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate) (member : point ∈ coordinates) :
    lower ≤ point ∧ point ≤ upper := by
    rcases (spec point).mp member with rfl | rfl | member
    · exact ⟨le_rfl, proper.le⟩
    · exact ⟨proper.le, le_rfl⟩
    · exact member.2
  have lowerMember : lower ∈ coordinates.map id := by
    rw [Map.map_id]
    exact (spec lower).mpr (Or.inl rfl)
  have upperMember : upper ∈ coordinates.map id := by
    rw [Map.map_id]
    exact (spec upper).mpr (Or.inr (Or.inl rfl))
  let span := Span.ofBounds coordinates ordered bounded lowerMember upperMember
  let intervals := Interval.adjacent coordinates ordered
  let count := intervals.length
  have countLe : count ≤ cuts.length + 1 := by
    have sorted := Geometry.Rectangle.Partition.PreparedAxisPartitions.sort_length candidates
    have filtered := Filter.length_filter_le (fun point => decide (lower ≤ point ∧ point ≤ upper)) cuts
    change (Interval.adjacent coordinates ordered).length ≤ _
    rw [Geometry.Rectangle.Partition.PreparedAxisPartitions.adjacent_length coordinates ordered]
    dsimp only [coordinates, candidates] at sorted ⊢
    simp only [List.length_cons] at sorted
    omega
  exact ⟨proper, coordinates, ordered, spec, intervals, rfl, count, rfl, countLe, span.walk ordered, span.walk_edges
    ordered⟩

/-- The lower endpoint occurs in the retained coordinates.

The coordinate-cache specification includes the original lower endpoint
explicitly. Its membership refers to the same retained coordinate cache. -/
public theorem lower_mem (partition : AxisPartition lower upper cuts) : lower ∈ partition.coordinates
  :=
  (partition.coordinates_spec lower).mpr (Or.inl rfl)

/-- The upper endpoint occurs in the retained coordinates.

The coordinate-cache specification includes the original upper endpoint
explicitly. Its membership refers to the same retained coordinate cache. -/
public theorem upper_mem (partition : AxisPartition lower upper cuts) : upper ∈ partition.coordinates
  :=
  (partition.coordinates_spec upper).mpr (Or.inr (Or.inl rfl))

/-- Every requested cut inside the closed interval is retained.

The requested coordinate belongs to the original cut bank and lies between its
endpoints. The exact cache specification retains that same occurrence. -/
public theorem cut_mem (partition : AxisPartition lower upper cuts) {point :
  _root_.Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate} (member : point ∈ cuts)
    (inside : lower ≤ point ∧ point ≤ upper) : point ∈ partition.coordinates :=
  (partition.coordinates_spec point).mpr (Or.inr (Or.inr ⟨member, inside⟩))

/-- Every retained coordinate lies between the original endpoints.

The exact cache specification identifies either original endpoint or an in-
range requested coordinate. All three alternatives give the displayed closed
bounds. -/
public theorem coordinate_bounds (partition : AxisPartition lower upper cuts) {point :
  _root_.Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate}
    (member : point ∈ partition.coordinates) : lower ≤ point ∧ point ≤ upper := by
  rcases (partition.coordinates_spec point).mp member with rfl | rfl | member
  · exact ⟨le_rfl, partition.proper.le⟩
  · exact ⟨partition.proper.le, le_rfl⟩
  · exact member.2

/-- Every retained interval lies within the original interval.

The interval cache is exactly the retained covering walk. Its edge bounds
certify the same selected interval against the original frame endpoints. -/
public theorem interval_bounds (partition : AxisPartition lower upper cuts) {interval :
  Partition.PreparedAxisPartitions.Interval} (member : interval ∈ partition.intervals) :
    lower ≤ interval.lower ∧ interval.upper ≤ upper := by
  rw [← partition.walk_edges] at member
  exact partition.walk.edge_bounds interval member

/-- Retained adjacent intervals are pairwise ordered without interior overlap.

The stored intervals are the adjacent construction on strictly ordered cached
coordinates. Their original endpoint order forbids interior overlap. -/
public theorem separated (partition : AxisPartition lower upper cuts) :
    partition.intervals.Pairwise Interval.Before := by
  rw [partition.intervals_eq]
  exact Interval.adjacent_pairwise partition.coordinates partition.ordered

/-- No retained cut lies strictly inside one of the actual adjacent pieces. The
disjunction also handles cuts equal to either endpoint.

The retained coordinate occurs on the original strictly ordered axis. No
original axis occurrence lies inside one of its adjacent intervals, including
endpoint equality. -/
public theorem coordinate_outside (partition : AxisPartition lower upper cuts) {interval :
  _root_.Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}
    (member : interval ∈ partition.intervals) {point : Partition.PreparedAxisPartitions.Coordinate} (present : point ∈
      partition.coordinates) :
    point ≤ interval.lower ∨ interval.upper ≤ point := by
  rw [partition.intervals_eq] at member
  exact Incidence.Interval.entry_side partition.coordinates partition.ordered member present

/-- Every requested cut lies outside the interior of each retained interval.

Cuts below or above the original frame are already outside every retained
interval. In-range cuts occur in the coordinate cache and satisfy its adjacent-
interval separation law. -/
public theorem cut_outside (partition : AxisPartition lower upper cuts) {interval :
  _root_.Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}
    (member : interval ∈ partition.intervals) {point : Partition.PreparedAxisPartitions.Coordinate} (present : point ∈
        cuts) :
    point ≤ interval.lower ∨ interval.upper ≤ point := by
  if below : point < lower then
    exact Or.inl (below.le.trans (partition.interval_bounds member).1)
  else if above : upper < point then
    exact Or.inr ((partition.interval_bounds member).2.trans above.le)
  else
    exact partition.coordinate_outside member (partition.cut_mem present ⟨le_of_not_gt below, le_of_not_gt above⟩)

set_option genInjectivity false in
/-- A containing interval is returned as executable data, including queries at
either outer endpoint.

The record retains the actual selected interval, its membership in the cached
partition, and closed lower and upper bounds for the supplied query. -/
public structure Located (partition : AxisPartition lower upper cuts)
  (point : Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate) where
  /-- An actual interval containing the query. -/ interval :
    Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval
  /-- The selected interval belongs to the retained partition. -/ member : interval ∈ partition.intervals
  /-- The query lies between the selected interval's closed endpoints. -/ inside : interval.lower ≤ point ∧ point ≤
    interval.upper

constructive_injectivity Located

/-- Scan an increasing finite walk for an interval containing the point.

Strictly ordered outer endpoints and closed point bounds ensure the scan
returns an actual interval with its membership and containment proofs. -/
@[expose] public def locateWalk (intervals : List Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval)
  (point : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate) :
    {start finish : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate} →
      Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk intervals start finish → start < finish →
    start ≤ point → point ≤ finish →
      {interval : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval // interval ∈ intervals ∧
        interval.lower ≤ point ∧ point ≤ interval.upper}
  | _, _, .nil _, proper, _, _ => (lt_irrefl _ proper).elim
  | _, _, .cons interval member tail, _, lower, upper =>
      if before : point ≤ interval.upper then ⟨interval, member, lower, before⟩
      else locateWalk intervals point tail
        ((lt_of_not_ge before).trans_le upper) (le_of_not_ge before) upper

/-- Locate a bounded coordinate in an actual retained interval.

The original increasing-walk scan returns an interval from the retained bank.
The query bounds and original proper frame certify containment at either outer
endpoint as well. -/
@[expose] public def locate (partition : AxisPartition lower upper cuts)
  (point : Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate) (inside : lower ≤ point ∧ point ≤ upper) :
    Located partition point :=
  let found := locateWalk partition.intervals point
    partition.walk partition.proper inside.1 inside.2
  ⟨found.val, found.property.1, found.property.2⟩

set_option genInjectivity false in
/-- A retained cut is a literal endpoint of an actual adjacent interval. The bit
says whether it is the upper endpoint.

The record retains an actual interval and a Boolean identifying its requested
lower or upper endpoint. Its exact reading equals the original cached
coordinate. -/
public structure Endpoint (partition : AxisPartition lower upper cuts)
  (point : Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate) where
  /-- An actual interval having the specified endpoint. -/ interval :
    Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval
  /-- The selected interval belongs to the retained partition. -/ member : interval ∈ partition.intervals
  /-- Whether the specified point is the upper endpoint. -/ high : Bool
  /-- The selected endpoint equals the requested coordinate. -/ endpoint_eq : (if high then interval.upper else
    interval.lower) = point

constructive_injectivity Endpoint

/-- Select an actual partition interval having the requested retained endpoint.

The neighbor construction returns the lower endpoint at the first cut and an
upper endpoint when a preceding interval is available. -/
@[expose] public def endpoint (partition : AxisPartition lower upper
  cuts) (point : Geometry.Rectangle.Partition.PreparedAxisPartitions.Coordinate) (member : point ∈
  partition.coordinates) :
    Endpoint partition point := by
  have keyMember : point ∈ partition.coordinates.map id := by simpa only [Map.map_id] using member
  let neighbors := AxisNeighbors.neighbors point partition.coordinates partition.ordered keyMember
  cases neighbors with
  | first after _ =>
    exact ⟨after.interval, by rw [partition.intervals_eq]; exact after.member, false, after.endpoint_eq⟩
  | last before _ =>
    exact ⟨before.interval, by rw [partition.intervals_eq]; exact before.member, true, before.endpoint_eq⟩
  | interior before _ =>
    exact ⟨before.interval, by rw [partition.intervals_eq]; exact before.member, true, before.endpoint_eq⟩
  | singleton only =>
      exact (partition.proper.ne ((only lower partition.lower_mem).trans (only upper partition.upper_mem).symm)).elim

/-- Sum the widths of a finite interval list.

The finite structural coordinate sum accumulates each retained interval width
in list order. The empty interval bank contributes zero. -/
@[expose] public def widthSum (intervals : List Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval) :
  Partition.PreparedAxisPartitions.Coordinate := Squares.coordinateSum (intervals.map fun interval => interval.upper -
      interval.lower)

/-- The widths along an increasing walk telescope to its endpoint difference.

Each walk step retains the interval ending where the remaining walk begins.
Scalar addition telescopes those displayed widths to the original endpoint
difference. -/
private theorem widthSum_walk {intervals : List Partition.PreparedAxisPartitions.Interval} :
    {start finish : Partition.PreparedAxisPartitions.Coordinate} → (walk : AxisWalks.IncreasingWalk intervals start
        finish) →
      widthSum walk.edges = finish - start
  | _, _, .nil _ => by change (0 : Partition.PreparedAxisPartitions.Coordinate) = _ - _; ring1
  | _, _, .cons interval _ tail => by
      change interval.upper - interval.lower + widthSum tail.edges = _
      rw [widthSum_walk tail]
      simp only [id_eq]
      ring1

/-- The retained interval widths sum to the original interval width.

The cached interval list is the exact edge list of the retained covering walk.
Its scalar width sum therefore reaches the original frame endpoints. -/
public theorem widthSum_eq (partition : AxisPartition lower upper cuts) :
  widthSum partition.intervals = upper - lower := by
  rw [← partition.walk_edges]
  exact widthSum_walk partition.walk

end AxisPartition

end Purelib.Geometry.Rectangle
