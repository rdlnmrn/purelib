module
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map

public import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.WindowAxes
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Coarsening finite partial walks to the retained adjacent intervals

Strictly moving pieces stay within their retained adjacent intervals. A
connected word between retained axis coordinates can therefore be grouped
into complete intervals in the same order. The proof retains the original
piece list and performs no new grid search.
-/

namespace Purelib.Polynomial.Geometry.Grid.Axis.Partial

open Purelib.Data.Rat
open Purelib.Data.List

open Purelib.Polynomial

universe u v
variable {Alpha : Type u} {Piece : Type v} {key : Alpha → Fraction.Rational}

/-- A retained axis coordinate lies outside the interior of an adjacent gap.

The ordered coordinate list places each retained point before the lower
endpoint or after the upper endpoint of that exact adjacent interval. -/
theorem coordinate_outside {entries : List Alpha}
    (ordered : entries.Pairwise (fun first second => key first < key second))
    {interval : Geometry.Grid.ClearGrid.Interval key} (member : interval ∈ Geometry.Grid.ClearGrid.Interval.adjacent
      entries ordered)
    {point : Fraction.Rational} (present : point ∈ entries.map key) :
    point ≤ key interval.lower ∨ key interval.upper ≤ point := open Purelib in by
  induction entries with
  | nil => exact (List.not_mem_nil member).elim
  | cons lower remaining ih =>
      cases remaining with
      | nil => exact (List.not_mem_nil member).elim
      | cons upper rest =>
          rcases Membership.mem_cons.mp member with rfl | member
          · rcases Membership.mem_cons.mp present with rfl | present
            · exact Or.inl le_rfl
            · obtain ⟨entry, entryMember, equal⟩ := Data.List.Map.mem_map.mp present
              rcases Membership.mem_cons.mp entryMember with rfl | entryMember
              · exact Or.inr equal.le
              · exact Or.inr (((List.pairwise_cons.mp (List.pairwise_cons.mp ordered).2).1 entry
                  entryMember).le.trans_eq equal)
          · rcases Membership.mem_cons.mp present with rfl | present
            · have endpoint := (Geometry.Grid.ClearGrid.Interval.endpoints_mem (upper :: rest) (List.pairwise_cons.mp
                ordered).2 member).1
              exact Or.inl ((List.pairwise_cons.mp ordered).1 interval.lower endpoint).le
            · exact ih (List.pairwise_cons.mp ordered).2 member present

/-- Two separated intervals containing a point below both upper endpoints agree.

Membership in the original ordered interval list rules out distinct intervals
with overlapping half-open interiors. -/
theorem eq_of_right_overlap {intervals : List (Geometry.Grid.ClearGrid.Interval key)} (separated : intervals.Pairwise
  Geometry.Grid.ClearGrid.Interval.Before)
    {first second : Geometry.Grid.ClearGrid.Interval key} (firstMember : first ∈ intervals) (secondMember : second ∈
      intervals)
    {point : Fraction.Rational} (firstInside : key first.lower ≤ point ∧ point < key first.upper)
    (secondInside : key second.lower ≤ point ∧ point < key second.upper) : first = second := by
  induction intervals with
  | nil => exact (List.not_mem_nil firstMember).elim
  | cons head tail ih =>
      rcases Membership.mem_cons.mp firstMember with rfl | firstTail
      · rcases Membership.mem_cons.mp secondMember with rfl | secondTail
        · rfl
        · exact (not_lt_of_ge (((List.pairwise_cons.mp separated).1 second secondTail).trans secondInside.1)
            firstInside.2).elim
      · rcases Membership.mem_cons.mp secondMember with rfl | secondTail
        · exact (not_lt_of_ge (((List.pairwise_cons.mp separated).1 first firstTail).trans firstInside.1)
            secondInside.2).elim
        · exact ih (List.pairwise_cons.mp separated).2 firstTail secondTail

/-- A connected list of actual pieces, with strict movement and a retained
containing interval for each piece. -/
inductive PartialWalk (span : Piece → Geometry.Grid.ClearGrid.Interval key) (first last : Piece → Fraction.Rational)
    (intervals : List (Geometry.Grid.ClearGrid.Interval key)) : List Piece → Fraction.Rational → Fraction.Rational →
      Prop
  /-- The empty interval list gives the stationary partial walk. -/ | nil (point : Fraction.Rational) :
    Purelib.Polynomial.Geometry.Grid.Axis.Partial.PartialWalk span first last intervals [] point point
  /-- Prepend a retained interval span and continue through the remaining interval list. -/ | cons (piece : Piece)
    {pieces : List Piece} {finish : Fraction.Rational}
      (member : span piece ∈ intervals) (moving : first piece < last piece)
      (inside : key (span piece).lower ≤ first piece ∧ last piece ≤ key (span piece).upper)
      (tail : Purelib.Polynomial.Geometry.Grid.Axis.Partial.PartialWalk span first last intervals pieces (last piece)
        finish) :
      Purelib.Polynomial.Geometry.Grid.Axis.Partial.PartialWalk span first last intervals (piece :: pieces) (first
        piece) finish

namespace PartialWalk

variable {span : Piece → Geometry.Grid.ClearGrid.Interval key} {first last : Piece → Fraction.Rational}

/-- Append two consecutive partial walks while retaining their original interval lists. -/
theorem append {intervals : List (Geometry.Grid.ClearGrid.Interval key)} {before after : List Piece} {start middle
  finish : Fraction.Rational}
    (left : Geometry.Grid.Axis.Partial.PartialWalk span first last intervals before start middle)
    (right : Geometry.Grid.Axis.Partial.PartialWalk span first last intervals after middle finish) :
    Geometry.Grid.Axis.Partial.PartialWalk span first last intervals (before ++ after) start finish := by
  induction left with
  | nil => exact right
  | cons piece member moving inside tail ih => exact .cons piece member moving inside (ih right)

/-- The exact piece list for each complete interval, including its endpoint
coverage, is retained alongside the interval order. -/
inductive Groups (span : Piece → Geometry.Grid.ClearGrid.Interval key) (first last : Piece → Fraction.Rational)
    (intervals : List (Geometry.Grid.ClearGrid.Interval key)) : List (Geometry.Grid.ClearGrid.Interval key) → List Piece
      → Prop
  /-- Empty coarse and fine interval lists form the empty grouping. -/ | nil :
    Purelib.Polynomial.Geometry.Grid.Axis.Partial.PartialWalk.Groups span first last intervals [] []
  /-- Retain one complete coarse span and its ordered fine pieces before the remaining groups. -/ | cons {interval :
    Geometry.Grid.ClearGrid.Interval key} {block pieces : List Piece} {rest : List (Geometry.Grid.ClearGrid.Interval
    key)}
      (same : ∀ piece ∈ block, span piece = interval)
      (path : Geometry.Grid.Axis.Partial.PartialWalk span first last intervals block (key interval.lower) (key
        interval.upper))
      (tail : Purelib.Polynomial.Geometry.Grid.Axis.Partial.PartialWalk.Groups span first last intervals rest pieces) :
      Purelib.Polynomial.Geometry.Grid.Axis.Partial.PartialWalk.Groups span first last intervals (interval :: rest)
        (block ++ pieces)

open Purelib.Polynomial.Geometry.Grid.Axis.Partial in
/-- Split a partial walk at the upper endpoint of a containing coarse interval.

The prefix ends at that exact endpoint and stays in the coarse span; the suffix retains the original remaining walk. -/
private theorem take_to_upper {entries : List Alpha}
    (ordered : entries.Pairwise (fun a b => key a < key b))
    {interval : Geometry.Grid.ClearGrid.Interval key} (member : interval ∈ Geometry.Grid.ClearGrid.Interval.adjacent
      entries ordered)
    {pieces : List Piece} {start finish : Fraction.Rational}
    (walk : Geometry.Grid.Axis.Partial.PartialWalk span first last (Geometry.Grid.ClearGrid.Interval.adjacent entries
      ordered) pieces start finish)
    (afterLower : key interval.lower < start) (beforeUpper : start ≤ key interval.upper)
    (finishMember : finish ∈ entries.map key) :
    ∃ before after, pieces = before ++ after ∧
      Geometry.Grid.Axis.Partial.PartialWalk span first last (Geometry.Grid.ClearGrid.Interval.adjacent entries ordered)
        before start (key interval.upper) ∧
      (∀ piece ∈ before, span piece = interval) ∧
      Geometry.Grid.Axis.Partial.PartialWalk span first last (Geometry.Grid.ClearGrid.Interval.adjacent entries ordered)
        after (key interval.upper) finish := by
  by_cases atEnd : start = key interval.upper
  · exact ⟨[], pieces, rfl, atEnd ▸ .nil start, (by intro piece present; exact (List.not_mem_nil present).elim), atEnd ▸
      walk⟩
  · have before : start < key interval.upper := lt_of_le_of_ne beforeUpper atEnd
    cases walk with
    | nil point =>
        rcases coordinate_outside ordered member finishMember with below | above
        · exact (not_lt_of_ge below afterLower).elim
        · exact (not_lt_of_ge above before).elim
    | cons piece pieceMember moving inside tail =>
        have same : span piece = interval := Geometry.Grid.Axis.Partial.eq_of_right_overlap
          (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise entries ordered) pieceMember member
          ⟨inside.1, moving.trans_le inside.2⟩ ⟨afterLower.le, before⟩
        have bound : last piece ≤ key interval.upper := inside.2.trans_eq (congrArg (fun current :
          Geometry.Grid.ClearGrid.Interval key => key current.upper) same)
        obtain ⟨left, right, equal, leftWalk, leftSame, rightWalk⟩ :=
          Purelib.Polynomial.Geometry.Grid.Axis.Partial.PartialWalk.take_to_upper ordered member tail (afterLower.trans
            moving) bound finishMember
        exact ⟨piece :: left, right, congrArg (List.cons piece) equal, .cons piece pieceMember moving inside leftWalk,
          (by
            intro other present; rcases Membership.mem_cons.mp present with rfl | present; exact same;
            exact leftSame other present), rightWalk⟩
termination_by pieces.length
decreasing_by
  subst_vars
  exact Nat.lt_succ_self _

/-- Transporting a walk's starting coordinate leaves its edge list unchanged. -/
private theorem castStart_edges {intervals : List (Geometry.Grid.ClearGrid.Interval key)} {start finish other :
  Fraction.Rational}
    (walk : Geometry.Grid.AxisWalks.IncreasingWalk intervals start finish) (equal : start = other) :
    (walk.castStart equal).edges = walk.edges := by
  cases equal
  rfl

open Purelib.Polynomial.Geometry.Grid.Axis.Partial in
/-- Coarsening follows the existing finite word. Every complete interval
has exactly its original consecutive group of partial pieces. -/
theorem coarsen {entries : List Alpha} (ordered : entries.Pairwise (fun a b => key a < key b))
    {pieces : List Piece} {start finish : Fraction.Rational}
    (walk : Geometry.Grid.Axis.Partial.PartialWalk span first last (Geometry.Grid.ClearGrid.Interval.adjacent entries
      ordered) pieces start finish)
    (startMember : start ∈ entries.map key) (finishMember : finish ∈ entries.map key) :
    ∃ whole : Geometry.Grid.AxisWalks.IncreasingWalk (Geometry.Grid.ClearGrid.Interval.adjacent entries ordered) start
      finish,
      Geometry.Grid.Axis.Partial.PartialWalk.Groups span first last (Geometry.Grid.ClearGrid.Interval.adjacent entries
        ordered) whole.edges pieces := open Purelib in by
  cases walk with
  | nil => exact ⟨.nil _, .nil⟩
  | @cons piece rest finish member moving inside tail =>
      have startEq : first piece = key (span piece).lower := by
        rcases coordinate_outside ordered member startMember with below | above
        · exact le_antisymm below inside.1
        · exact (not_lt_of_ge (inside.2.trans above) moving).elim
      obtain ⟨before, after, equal, firstWalk, same, lastWalk⟩ :=
        Geometry.Grid.Axis.Partial.PartialWalk.take_to_upper ordered member tail (startEq ▸ moving) inside.2
          finishMember
      have afterShort : after.length < (piece :: rest).length := by
        have lengths := congrArg List.length equal
        simp only [Append.length_append, List.length_cons] at *
        omega
      obtain ⟨remaining, grouped⟩ := Purelib.Polynomial.Geometry.Grid.Axis.Partial.PartialWalk.coarsen ordered lastWalk
        (Data.List.Map.mem_map_of_mem (Geometry.Grid.ClearGrid.Interval.endpoints_mem entries ordered member).2)
          finishMember
      let whole := Geometry.Grid.AxisWalks.IncreasingWalk.cons (span piece) member remaining
      refine ⟨whole.castStart startEq.symm, ?_⟩
      have firstGroup : Geometry.Grid.Axis.Partial.PartialWalk span first last
        (Geometry.Grid.ClearGrid.Interval.adjacent entries ordered) (piece :: before)
          (key (span piece).lower) (key (span piece).upper) :=
        startEq ▸ .cons piece member moving inside firstWalk
      have groups := Geometry.Grid.Axis.Partial.PartialWalk.Groups.cons (by
        intro other present
        rcases Membership.mem_cons.mp present with rfl | present
        · rfl
        · exact same other present) firstGroup grouped
      have wholeEdges : (whole.castStart startEq.symm).edges = (span piece) :: remaining.edges :=
        Geometry.Grid.Axis.Partial.PartialWalk.castStart_edges whole startEq.symm
      rw [wholeEdges, show piece :: _ = (piece :: before) ++ after from congrArg (List.cons piece) equal]
      exact groups
termination_by pieces.length
decreasing_by
  subst_vars
  exact afterShort

/-- Match any already retained complete walk with the same endpoints;
its exact edge order is certified by the separated finite axis. -/
theorem groups_for_walk {entries : List Alpha} (ordered : entries.Pairwise (fun a b => key a < key b))
    {pieces : List Piece} {start finish : Fraction.Rational}
    (walk : Geometry.Grid.Axis.Partial.PartialWalk span first last (Geometry.Grid.ClearGrid.Interval.adjacent entries
      ordered) pieces start finish)
    (startMember : start ∈ entries.map key) (finishMember : finish ∈ entries.map key)
    (whole : Geometry.Grid.AxisWalks.IncreasingWalk (Geometry.Grid.ClearGrid.Interval.adjacent entries ordered) start
      finish) :
    Geometry.Grid.Axis.Partial.PartialWalk.Groups span first last (Geometry.Grid.ClearGrid.Interval.adjacent entries
      ordered) whole.edges pieces := by
  obtain ⟨found, groups⟩ := walk.coarsen ordered startMember finishMember
  have equal := (Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter
      (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise entries ordered) found).trans
    (Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter
      (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise entries ordered) whole).symm
  exact equal ▸ groups

end PartialWalk
end Purelib.Polynomial.Geometry.Grid.Axis.Partial
