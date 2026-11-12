module
public import Purelib.Integration.Cell.Source
public import Purelib.Integration.Cell.Refinement
import Purelib.Data.List.Membership
import Purelib.Tactic.Ring

/-! Source-admitted cell splits with their original ranges and cached readings. -/

public section

namespace Purelib.Integration

open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Integration.Partition

namespace IntegrationCell.Source

/-- Construct the left child of an original cell using the supplied rational tag.

Its endpoints are the original start and the retained cut. The original range
is preserved and its weight is the exact new endpoint difference. -/
@[expose] def leftChild {source : Fraction.Rational → Fraction.Rational}
    (parent : IntegrationCell (SourcePoint source)) (cut tag : Fraction.Rational)
    (inside : parent.item.interval.start ≤ cut ∧ cut ≤ parent.item.interval.finish)
    (tagInside : parent.item.interval.start ≤ tag ∧ tag ≤ cut) : IntegrationCell (SourcePoint source) :=
  { item := parent.item.retag ⟨parent.item.interval.start, cut⟩ tag tagInside.1 tagInside.2
    weight := cut - parent.item.interval.start
    weight_nonnegative := Arithmetic.sub_nonneg_direct inside.1
    lower := parent.lower
    upper := parent.upper
    range_valid := parent.range_valid }

/-- Construct the right child of an original cell using the supplied rational tag.

Its endpoints are the retained cut and the original finish. The original range
is preserved and its weight is the exact new endpoint difference. -/
@[expose] def rightChild {source : Fraction.Rational → Fraction.Rational}
    (parent : IntegrationCell (SourcePoint source)) (cut tag : Fraction.Rational)
    (inside : parent.item.interval.start ≤ cut ∧ cut ≤ parent.item.interval.finish)
    (tagInside : cut ≤ tag ∧ tag ≤ parent.item.interval.finish) : IntegrationCell (SourcePoint source) :=
  { item := parent.item.retag ⟨cut, parent.item.interval.finish⟩ tag tagInside.1 tagInside.2
    weight := parent.item.interval.finish - cut
    weight_nonnegative := Arithmetic.sub_nonneg_direct inside.2
    lower := parent.lower
    upper := parent.upper
    range_valid := parent.range_valid }

/-- Split one original source cell at a rational cut with independently supplied child tags.

The existing split certificate retains the exact parent cell. Its two children
reuse the parent's range and add to the parent's original certified weight. -/
@[expose] def splitAt {source : Fraction.Rational → Fraction.Rational}
    (parent : IntegrationCell (SourcePoint source)) (admitted : Admitted parent)
    (cut leftTag rightTag : Fraction.Rational)
    (inside : parent.item.interval.start ≤ cut ∧ cut ≤ parent.item.interval.finish)
    (leftInside : parent.item.interval.start ≤ leftTag ∧ leftTag ≤ cut)
    (rightInside : cut ≤ rightTag ∧ rightTag ≤ parent.item.interval.finish) : IntegrationSplit parent where
  children := [leftChild parent cut leftTag inside leftInside, rightChild parent cut rightTag inside rightInside]
  weight_conserved := by
    change (cut - parent.item.interval.start) + ((parent.item.interval.finish - cut) + 0) = parent.weight
    rw [admitted.1]
    change (cut - parent.item.interval.start) + ((parent.item.interval.finish - cut) + 0) =
      parent.item.interval.finish - parent.item.interval.start
    ring1
  lower_refines := by
    intro child childMember
    rcases Membership.mem_cons.mp childMember with equal | remaining
    · cases equal
      exact le_rfl
    · have equal := Membership.mem_singleton.mp remaining
      cases equal
      exact le_rfl
  upper_refines := by
    intro child childMember
    rcases Membership.mem_cons.mp childMember with equal | remaining
    · cases equal
      exact le_rfl
    · have equal := Membership.mem_singleton.mp remaining
      cases equal
      exact le_rfl

/-- Each split child's inherited range encloses the original source throughout that child's closed interval. -/
theorem splitAt_source_range {source : Fraction.Rational → Fraction.Rational}
    (parent : IntegrationCell (SourcePoint source)) (admitted : Admitted parent)
    (cut leftTag rightTag : Fraction.Rational)
    (inside : parent.item.interval.start ≤ cut ∧ cut ≤ parent.item.interval.finish)
    (leftInside : parent.item.interval.start ≤ leftTag ∧ leftTag ≤ cut)
    (rightInside : cut ≤ rightTag ∧ rightTag ≤ parent.item.interval.finish)
    (child : IntegrationCell (SourcePoint source))
    (childMember : child ∈ (splitAt parent admitted cut leftTag rightTag inside leftInside rightInside).children)
    (point : Fraction.Rational) (lower : child.item.interval.start ≤ point)
    (upper : point ≤ child.item.interval.finish) :
    child.lower ≤ source point ∧ source point ≤ child.upper := by
  change child ∈ [leftChild parent cut leftTag inside leftInside,
    rightChild parent cut rightTag inside rightInside] at childMember
  rcases Membership.mem_cons.mp childMember with equal | remaining
  · cases equal
    exact admitted.2 point lower (upper.trans inside.2)
  · have equal := Membership.mem_singleton.mp remaining
    cases equal
    exact admitted.2 point (inside.1.trans lower) upper

/-- Each original split child retains the exact length and pointwise source admission needed for another split. -/
theorem splitAt_child_admitted {source : Fraction.Rational → Fraction.Rational}
    (parent : IntegrationCell (SourcePoint source)) (admitted : Admitted parent)
    (cut leftTag rightTag : Fraction.Rational)
    (inside : parent.item.interval.start ≤ cut ∧ cut ≤ parent.item.interval.finish)
    (leftInside : parent.item.interval.start ≤ leftTag ∧ leftTag ≤ cut)
    (rightInside : cut ≤ rightTag ∧ rightTag ≤ parent.item.interval.finish)
    (child : IntegrationCell (SourcePoint source))
    (childMember : child ∈ (splitAt parent admitted cut leftTag rightTag inside leftInside rightInside).children) :
    Admitted child := by
  constructor
  · change child ∈ [leftChild parent cut leftTag inside leftInside,
      rightChild parent cut rightTag inside rightInside] at childMember
    rcases Membership.mem_cons.mp childMember with equal | remaining
    · cases equal
      rfl
    · have equal := Membership.mem_singleton.mp remaining
      cases equal
      rfl
  · intro point lower upper
    exact splitAt_source_range parent admitted cut leftTag rightTag inside leftInside rightInside
      child childMember point lower upper

/-- Every pair of admitted child tags gives a weighted sum inside the original parent enclosure.

The actual child readings use the original source, and the split certificate
conserves the parent's weight before its finite integral bound is compared. -/
theorem splitAt_taggedSum_contains {source : Fraction.Rational → Fraction.Rational}
    (parent : IntegrationCell (SourcePoint source)) (admitted : Admitted parent)
    (cut leftTag rightTag : Fraction.Rational)
    (inside : parent.item.interval.start ≤ cut ∧ cut ≤ parent.item.interval.finish)
    (leftInside : parent.item.interval.start ≤ leftTag ∧ leftTag ≤ cut)
    (rightInside : cut ≤ rightTag ∧ rightTag ≤ parent.item.interval.finish) :
    (integralBound [parent]).Contains
      (weightedEvaluation SourcePoint.reading
        (splitAt parent admitted cut leftTag rightTag inside leftInside rightInside).children) := by
  let split := splitAt parent admitted cut leftTag rightTag inside leftInside rightInside
  have enclosed : (integralBound split.children).Contains (weightedEvaluation SourcePoint.reading split.children) := by
    apply weightedEvaluation_mem_integralBound
    intro child childMember
    have range := splitAt_source_range parent admitted cut leftTag rightTag inside leftInside rightInside
      child childMember child.item.point child.item.start_le child.item.point_le_finish
    rw [child.item.reading_eq]
    exact range
  exact split.integralBound_refines.contains enclosed

end IntegrationCell.Source

namespace SourceFrontier

/-- A source-admitted split history's tagged sum lies inside the original frontier's enclosure.

The retained refinement proves conservation and range narrowing across every
split. Each final cell supplies its own source admission, so its actual cached
tag reading is enclosed before the original frontier bound is recovered. -/
theorem refinedTaggedSum_contains {source : Fraction.Rational → Fraction.Rational}
    (frontier : SourceFrontier source) (cells : List (IntegrationCell (SourcePoint source)))
    (refines : IntegrationFrontierRefines cells frontier.cells)
    (admitted : ∀ cell ∈ cells, IntegrationCell.Source.Admitted cell) :
    (integralBound frontier.cells).Contains (weightedEvaluation SourcePoint.reading cells) := by
  have enclosed : (integralBound cells).Contains (weightedEvaluation SourcePoint.reading cells) := by
    apply weightedEvaluation_mem_integralBound
    intro cell member
    have range := (admitted cell member).2 cell.item.point cell.item.start_le cell.item.point_le_finish
    rw [cell.item.reading_eq]
    exact range
  exact refines.integralBound_refines.contains enclosed

end SourceFrontier

end Purelib.Integration

end
