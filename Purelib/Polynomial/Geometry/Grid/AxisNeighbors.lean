module

import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map

public import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Certified adjacent intervals at a retained grid coordinate

One finite axis scan returns both neighbors, or exact endpoint/singleton
evidence explaining their absence. Retained intervals keep their original
line payloads. Coverage and uniqueness certify membership in the original
adjacent occurrence bank together with the exact requested endpoint.
-/

namespace Purelib.Polynomial.Geometry.Grid.AxisNeighbors

open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Data.List

universe u
variable {Alpha : Type u} {key : Alpha → Fraction.Rational}

/-- Two members of an ordered interval list with the same lower or upper coordinate
are the same retained interval.

Both membership witnesses refer to the same ordered retained interval list.
Proper widths and pairwise endpoint order identify equal lower or upper
endpoints with the same interval. -/
private theorem same_endpoint {intervals : List (Geometry.Grid.ClearGrid.Interval key)}
    (ordered : intervals.Pairwise Geometry.Grid.ClearGrid.Interval.Before) {first second :
      Geometry.Grid.ClearGrid.Interval key}
    (firstMember : first ∈ intervals) (secondMember : second ∈ intervals)
    (same : key first.lower = key second.lower ∨ key first.upper = key second.upper) : first = second := by
  induction intervals with
  | nil => exact (List.not_mem_nil firstMember).elim
  | cons head tail ih =>
      rcases Membership.mem_cons.mp firstMember with firstEq | firstMember
      · subst first
        rcases Membership.mem_cons.mp secondMember with secondEq | secondMember
        · exact secondEq.symm
        · have before := (List.pairwise_cons.mp ordered).1 second secondMember
          rcases same with lowerEq | upperEq
          · exact (not_lt_of_ge before (lowerEq.symm.trans_lt head.ordered)).elim
          · exact (not_lt_of_ge before (second.ordered.trans_eq upperEq.symm)).elim
      · rcases Membership.mem_cons.mp secondMember with secondEq | secondMember
        · subst second
          have before := (List.pairwise_cons.mp ordered).1 first firstMember
          rcases same with lowerEq | upperEq
          · exact (not_lt_of_ge before (lowerEq.trans_lt head.ordered)).elim
          · exact (not_lt_of_ge before (first.ordered.trans_eq upperEq)).elim
        · exact ih (List.pairwise_cons.mp ordered).2 firstMember secondMember

/-- Adjacent intervals of a strictly ordered axis are equal if their lower
coordinates agree.

Both intervals occur in the adjacent list of one strictly ordered axis. Equal
lower readings identify their original retained interval payloads. -/
public theorem eq_of_lower {entries : List Alpha} (ordered : entries.Pairwise (fun first second => key first < key
  second))
    {first second : Geometry.Grid.ClearGrid.Interval key} (firstMember : first ∈
      Geometry.Grid.ClearGrid.Interval.adjacent entries ordered)
    (secondMember : second ∈ Geometry.Grid.ClearGrid.Interval.adjacent entries ordered) (same : key first.lower = key
      second.lower) : first = second :=
  AxisNeighbors.same_endpoint (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise entries ordered) firstMember
    secondMember (Or.inl same)

/-- Adjacent intervals of a strictly ordered axis are equal if their upper
coordinates agree.

Both intervals occur in the adjacent list of one strictly ordered axis. Equal
upper readings identify their original retained interval payloads. -/
public theorem eq_of_upper {entries : List Alpha} (ordered : entries.Pairwise (fun first second => key first < key
  second))
    {first second : Geometry.Grid.ClearGrid.Interval key} (firstMember : first ∈
      Geometry.Grid.ClearGrid.Interval.adjacent entries ordered)
    (secondMember : second ∈ Geometry.Grid.ClearGrid.Interval.adjacent entries ordered) (same : key first.upper = key
      second.upper) : first = second :=
  AxisNeighbors.same_endpoint (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise entries ordered) firstMember
    secondMember (Or.inr same)

set_option genInjectivity false in
/-- An actual retained interval with one specified endpoint coordinate.

The Boolean chooses the upper endpoint when true and the lower endpoint
otherwise; membership belongs to the original interval bank. -/
public structure AtEndpoint (intervals : List (Geometry.Grid.ClearGrid.Interval key)) (coordinate : Fraction.Rational)
  (upper : Bool) where
  /-- The original interval whose chosen endpoint matches the query. -/ interval : Geometry.Grid.ClearGrid.Interval key
  /-- The retained interval belongs to the displayed interval bank. -/ member : interval ∈ intervals
  /-- The selected lower or upper endpoint has the queried coordinate. -/ endpoint_eq : (if upper then key
    interval.upper else key interval.lower) = coordinate

constructive_injectivity AtEndpoint

/-- Transport an endpoint record to a containing interval bank without changing its
interval or endpoint equality.

The inclusion supplies membership in the target bank for every original bank
entry. The selected interval and its exact endpoint reading are unchanged. -/
@[expose] public def AtEndpoint.include {intervals larger : List (Geometry.Grid.ClearGrid.Interval key)} {coordinate :
  Fraction.Rational} {upper : Bool}
    (endpoint : Geometry.Grid.AxisNeighbors.AtEndpoint intervals coordinate upper) (included : ∀ interval ∈ intervals,
      interval ∈ larger) :
    Geometry.Grid.AxisNeighbors.AtEndpoint larger coordinate upper := ⟨endpoint.interval, included _ endpoint.member,
      endpoint.endpoint_eq⟩

set_option genInjectivity false in
/-- The adjacent intervals at a retained axis coordinate.

The alternatives retain a first or last endpoint with its extremality proof,
two interior neighbors, or evidence that every retained entry has the same
coordinate. -/
public inductive Neighbors (entries : List Alpha)
    (ordered : entries.Pairwise (fun first second => key first < key second)) (coordinate : Fraction.Rational) where
  /-- Retain the following interval and evidence that the query is a minimum axis
coordinate. -/ | first (after : Geometry.Grid.AxisNeighbors.AtEndpoint (Geometry.Grid.ClearGrid.Interval.adjacent
  entries ordered) coordinate false)
      (minimum : ∀ entry ∈ entries, coordinate ≤ key entry)
  /-- Retain the preceding interval and evidence that the query is a maximum axis
coordinate. -/ | last (before : Geometry.Grid.AxisNeighbors.AtEndpoint (Geometry.Grid.ClearGrid.Interval.adjacent
  entries ordered) coordinate true)
      (maximum : ∀ entry ∈ entries, key entry ≤ coordinate)
  /-- Retain the preceding and following intervals at an interior coordinate. -/ | interior (before :
    Geometry.Grid.AxisNeighbors.AtEndpoint (Geometry.Grid.ClearGrid.Interval.adjacent entries ordered) coordinate true)
      (after : Geometry.Grid.AxisNeighbors.AtEndpoint (Geometry.Grid.ClearGrid.Interval.adjacent entries ordered)
        coordinate false)
  /-- Retain evidence that all entries have the query coordinate, so no adjacent
interval is present. -/ | singleton (only : ∀ entry ∈ entries, key entry = coordinate)

constructive_injectivity Neighbors

/-- The first coordinate of a strictly ordered nonempty axis is at most every
coordinate retained in that axis.

The displayed member is either the first coordinate or a later retained
occurrence. Strict pairwise order supplies the latter bound on the same
payload. -/
public theorem head_le {head : Alpha} {tail : List Alpha}
    (ordered : (head :: tail).Pairwise (fun first second => key first < key second))
    {coordinate : Fraction.Rational} (member : coordinate ∈ (head :: tail).map key) : key head ≤ coordinate := open
      Purelib in by
  obtain ⟨entry, entryMember, equal⟩ := Data.List.Map.mem_map.mp member
  rcases Membership.mem_cons.mp entryMember with same | entryMember
  · subst entry
    exact equal.le
  · exact ((List.pairwise_cons.mp ordered).1 entry entryMember).le.trans_eq equal

/-- A retained coordinate different from the head coordinate belongs to the tail
coordinate list.

Membership identifies either the displayed head key or an occurrence in the
unchanged tail. The supplied inequality excludes precisely the head case. -/
public theorem tail_member {head : Alpha} {tail : List Alpha} {coordinate : Fraction.Rational}
    (member : coordinate ∈ (head :: tail).map key) (different : coordinate ≠ key head) : coordinate ∈ tail.map key := by
  rcases Membership.mem_cons.mp member with same | member
  · exact (different same).elim
  · exact member

/-- Scan the strictly ordered axis to retain the neighbors of a displayed member
coordinate.

The result preserves original interval payloads and records exact extremality
or singleton evidence when one or both neighbors are absent. -/
@[expose] public def neighbors (coordinate : Fraction.Rational) : (entries : List Alpha) →
    (ordered : entries.Pairwise (fun first second => key first < key second)) →
    coordinate ∈ entries.map key → Geometry.Grid.AxisNeighbors.Neighbors entries ordered coordinate
  | [], _, member => (List.not_mem_nil member).elim
  | [head], _, member => .singleton (fun entry entryMember => by
      rw [Membership.mem_singleton.mp entryMember]
      exact (Membership.mem_singleton.mp member).symm)
  | head :: next :: tail, ordered, member =>
      let headBefore := (List.pairwise_cons.mp ordered).1 next List.mem_cons_self
      let interval : Geometry.Grid.ClearGrid.Interval key := ⟨head, next, headBefore⟩
      if equal : coordinate = key head then
        .first ⟨interval, List.mem_cons_self, equal.symm⟩ (fun entry entryMember => by
          rw [equal]
          rcases Membership.mem_cons.mp entryMember with same | entryMember
          · exact (congrArg key same).symm.le
          · exact ((List.pairwise_cons.mp ordered).1 entry entryMember).le)
      else
        let memberTail := tail_member member equal
        let tailOrdered := (List.pairwise_cons.mp ordered).2
        match Purelib.Polynomial.Geometry.Grid.AxisNeighbors.neighbors coordinate (next :: tail) tailOrdered memberTail
          with
        | .first after minimum =>
            .interior ⟨interval, List.mem_cons_self, le_antisymm (head_le tailOrdered memberTail) (minimum next
              List.mem_cons_self)⟩
              (after.include (fun _ member => List.mem_cons_of_mem _ member))
        | .last before maximum =>
            .last (before.include (fun _ member => List.mem_cons_of_mem _ member)) (fun entry entryMember => by
              rcases Membership.mem_cons.mp entryMember with same | entryMember
              · rw [same]
                exact headBefore.le.trans (maximum next List.mem_cons_self)
              · exact maximum entry entryMember)
        | .interior before after =>
            .interior (before.include (fun _ member => List.mem_cons_of_mem _ member))
              (after.include (fun _ member => List.mem_cons_of_mem _ member))
        | .singleton only =>
            .last ⟨interval, List.mem_cons_self, only next List.mem_cons_self⟩ (fun entry entryMember => by
              rcases Membership.mem_cons.mp entryMember with same | entryMember
              · rw [same]
                exact headBefore.le.trans_eq (only next List.mem_cons_self)
              · exact (only entry entryMember).le)

namespace Neighbors

variable {entries : List Alpha} {ordered : entries.Pairwise (fun first second => key first < key second)}
  {coordinate : Fraction.Rational}

/-- List the retained neighbors in increasing order, omitting absent endpoint
neighbors.

First and last cases retain their single existing interval. The interior case
lists the preceding interval before the following interval, while singleton
evidence contributes no interval. -/
@[expose] public def intervals : Geometry.Grid.AxisNeighbors.Neighbors entries ordered coordinate → List
  (Geometry.Grid.ClearGrid.Interval key)
  | .first after _ => [after.interval]
  | .last before _ => [before.interval]
  | .interior before after => [before.interval, after.interval]
  | .singleton _ => []

/-- A retained coordinate has at most two adjacent intervals.

The first and last alternatives retain one interval and the interior
alternative retains two. The singleton alternative records their absence. -/
public theorem length_le_two (found : AxisNeighbors.Neighbors entries ordered coordinate) : found.intervals.length ≤ 2
  := by
  cases found <;> simp only [intervals, List.length_cons, List.length_nil] <;> decide

/-- On an axis containing both ends of a proper frame, a retained coordinate has
two neighbors, or one neighbor with evidence that it is a frame endpoint.

Both frame endpoints occur in the original coordinate bank. Their strict
inequality excludes a singleton axis and identifies each missing neighbor with
an actual frame endpoint. -/
public theorem framed_size_cases (found : AxisNeighbors.Neighbors entries ordered coordinate)
    {lower upper : Fraction.Rational} (lowerMember : lower ∈ entries.map key)
    (upperMember : upper ∈ entries.map key) (proper : lower < upper)
    (bounds : ∀ entry ∈ entries, lower ≤ key entry ∧ key entry ≤ upper) :
    (found.intervals.length = 1 ∧ (coordinate = lower ∨ coordinate = upper)) ∨
      found.intervals.length = 2 := open Purelib in by
  obtain ⟨first, firstMember, firstEq⟩ := Data.List.Map.mem_map.mp lowerMember
  obtain ⟨last, lastMember, lastEq⟩ := Data.List.Map.mem_map.mp upperMember
  cases found with
  | first after minimum =>
      refine Or.inl ⟨rfl, Or.inl (le_antisymm ((minimum first firstMember).trans_eq firstEq) ?_)⟩
      exact ((bounds after.interval.lower (Geometry.Grid.ClearGrid.Interval.endpoints_mem _ _
        after.member).1).1).trans_eq after.endpoint_eq
  | last before maximum =>
      refine Or.inl ⟨rfl, Or.inr (le_antisymm ?_ (lastEq.symm.trans_le (maximum last lastMember)))⟩
      exact before.endpoint_eq.symm.trans_le (bounds before.interval.upper
        (Geometry.Grid.ClearGrid.Interval.endpoints_mem _ _ before.member).2).2
  | interior _ _ => exact Or.inr rfl
  | singleton only =>
      have equal := firstEq.symm.trans ((only first firstMember).trans ((only last lastMember).symm.trans lastEq))
      exact (ne_of_lt proper equal).elim

/-- The retained neighbor intervals are ordered from left to right.

Interior neighbors meet at the same retained query coordinate. The remaining
alternatives have at most one retained interval and require no cross-pair
comparison. -/
public theorem pairwise (found : AxisNeighbors.Neighbors entries ordered coordinate) : found.intervals.Pairwise
  ClearGrid.Interval.Before := by
  have single (interval : Geometry.Grid.ClearGrid.Interval key) : [interval].Pairwise ClearGrid.Interval.Before :=
    .cons (fun _ member => (List.not_mem_nil member).elim) .nil
  cases found with
  | first after _ => exact single after.interval
  | last before _ => exact single before.interval
  | singleton _ => exact .nil
  | interior before after =>
      refine .cons ?_ (single after.interval)
      intro interval member
      rw [Membership.mem_singleton.mp member]
      exact (before.endpoint_eq.trans after.endpoint_eq.symm).le

/-- Every retained neighbor is an actual adjacent interval of the original axis.

Each nonempty alternative stores membership of its original intervals. The
displayed finite neighbor-list membership selects one of those stored
certificates. -/
public theorem member (found : AxisNeighbors.Neighbors entries ordered coordinate) {interval :
  Geometry.Grid.ClearGrid.Interval key}
    (member : interval ∈ found.intervals) : interval ∈ Geometry.Grid.ClearGrid.Interval.adjacent entries ordered := by
  cases found with
  | first after _ => exact (Membership.mem_singleton.mp member) ▸ after.member
  | last before _ => exact (Membership.mem_singleton.mp member) ▸ before.member
  | interior before after =>
      rcases Membership.mem_cons.mp member with same | member
      · exact same ▸ before.member
      · exact (Membership.mem_singleton.mp member) ▸ after.member
  | singleton _ => exact (List.not_mem_nil member).elim

/-- Every retained neighbor has the queried coordinate as one of its endpoints.

Each nonempty alternative retains the exact lower or upper endpoint equality.
Finite membership determines the corresponding original endpoint certificate. -/
public theorem endpoint (found : AxisNeighbors.Neighbors entries ordered coordinate) {interval :
  Geometry.Grid.ClearGrid.Interval key}
    (member : interval ∈ found.intervals) : key interval.lower = coordinate ∨ key interval.upper = coordinate := by
  cases found with
  | first after _ => rw [Membership.mem_singleton.mp member]; exact Or.inl after.endpoint_eq
  | last before _ => rw [Membership.mem_singleton.mp member]; exact Or.inr before.endpoint_eq
  | interior before after =>
      rcases Membership.mem_cons.mp member with same | member
      · rw [same]; exact Or.inr before.endpoint_eq
      · rw [Membership.mem_singleton.mp member]; exact Or.inl after.endpoint_eq
  | singleton _ => exact (List.not_mem_nil member).elim

/-- Every original adjacent interval incident to the queried coordinate occurs
among its retained neighbors.

The input interval belongs to the original adjacent bank and has the queried
endpoint. Ordered uniqueness or the retained extremality evidence identifies
its matching neighbor. -/
public theorem covers (found : AxisNeighbors.Neighbors entries ordered coordinate) {interval :
  Geometry.Grid.ClearGrid.Interval key}
    (member : interval ∈ Geometry.Grid.ClearGrid.Interval.adjacent entries ordered)
    (endpoint : key interval.lower = coordinate ∨ key interval.upper = coordinate) : interval ∈ found.intervals := by
  have endpoints := Geometry.Grid.ClearGrid.Interval.endpoints_mem entries ordered member
  cases found with
  | first after minimum =>
      rcases endpoint with lowerEq | upperEq
      · exact Membership.mem_singleton.mpr (AxisNeighbors.eq_of_lower ordered member after.member (lowerEq.trans
          after.endpoint_eq.symm))
      · exact (not_lt_of_ge (minimum interval.lower endpoints.1) (interval.ordered.trans_eq upperEq)).elim
  | last before maximum =>
      rcases endpoint with lowerEq | upperEq
      · exact (not_lt_of_ge (maximum interval.upper endpoints.2) (lowerEq.symm.trans_lt interval.ordered)).elim
      · exact Membership.mem_singleton.mpr (AxisNeighbors.eq_of_upper ordered member before.member (upperEq.trans
          before.endpoint_eq.symm))
  | interior before after =>
      rcases endpoint with lowerEq | upperEq
      · exact List.mem_cons_of_mem _ (Membership.mem_singleton.mpr (AxisNeighbors.eq_of_lower ordered member
          after.member (lowerEq.trans after.endpoint_eq.symm)))
      · exact Membership.mem_cons.mpr (Or.inl (AxisNeighbors.eq_of_upper ordered member before.member (upperEq.trans
          before.endpoint_eq.symm)))
  | singleton only =>
      have strict := interval.ordered
      rw [only interval.lower endpoints.1, only interval.upper endpoints.2] at strict
      exact (lt_irrefl _ strict).elim

end Neighbors

end Purelib.Polynomial.Geometry.Grid.AxisNeighbors
