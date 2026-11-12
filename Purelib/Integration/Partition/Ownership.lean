module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Integration.Partition.Interval
-- The original indexed-owner signatures retain the optional coordinate operation.
public import Purelib.Data.List.GetD
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Indexed rational interval owners

A point owner or child-interval owner retains its exact occurrence index and
parent interval in an original list. Optional readback binds that index to the
same parent, while endpoint inequalities certify half-open or full containment.
-/

namespace Purelib.Integration.Partition.Ownership

open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Partition

public section
set_option genInjectivity false in
/-- A retained interval-list occurrence owning a rational point in its half-open range.

The exact parent interval is certified at the retained index, with the point at or above its start and strictly below
its finish. -/
structure PointOwner (intervals : List Interval) (point : Fraction.Rational) where
  /-- The exact parent occurrence's index in the retained interval list. -/ index : Nat
  /-- The original interval at the retained occurrence index. -/ parent : Interval
  /-- Looking up the retained index returns this exact parent interval. -/ at_index : Purelib.Data.List.getElem?
    intervals index = some parent
  /-- The parent's start is at most the owned point. -/ start_le : parent.start ≤ point
  /-- The owned point lies strictly below the parent's finish. -/ point_lt_finish : point < parent.finish

constructive_injectivity PointOwner

/-- For a fixed interval list and point, the occurrence index determines the owner.

The lookup certificates force the retained parents to agree, and the remaining
fields are proofs. This does not identify equal intervals at different indices.
-/
theorem PointOwner.eq_of_index_eq {intervals : List Interval} {point : Fraction.Rational}
    (first second : PointOwner intervals point) (indices : first.index = second.index) : first = second := by
  have parents : first.parent = second.parent := Option.some.inj
    (first.at_index.symm.trans ((congrArg (Purelib.Data.List.getElem? intervals) indices).trans second.at_index))
  cases first
  cases second
  cases indices
  cases parents
  rfl

/-- Decide equality of two owners of the same point in the same original interval list. -/
@[expose] def PointOwner.compare {intervals : List Interval} {point : Fraction.Rational}
    (first second : PointOwner intervals point) : Decidable (first = second) :=
  if indices : first.index = second.index then
    .isTrue (PointOwner.eq_of_index_eq first second indices)
  else
    .isFalse (fun equal => indices (congrArg PointOwner.index equal))

/-- Find an owning interval by scanning the exact supplied cut chain.

The start and finish bound the point; each comparison either retains the current head occurrence or advances the
original tail owner and its index. -/
@[expose] def pointOwnerBetween (start finish point : Fraction.Rational) :
    (cuts : List Fraction.Rational) → start ≤ point → point < finish →
      PointOwner (Interval.intervalsBetween start finish cuts) point
  | [], lower, upper =>
      { index := 0, parent := ⟨start, finish⟩, at_index := rfl
        start_le := lower, point_lt_finish := upper }
  | cut :: tail, lower, upper =>
      if before : point < cut then
        { index := 0, parent := ⟨start, cut⟩, at_index := rfl
          start_le := lower, point_lt_finish := before }
      else
        let rest := Purelib.Integration.Partition.Ownership.pointOwnerBetween cut finish point tail
          (Purelib.Data.Rat.Fraction.Order.Arithmetic.le_of_not_gt_direct before) upper
        { index := rest.index + 1, parent := rest.parent, at_index := by
            exact rest.at_index
          start_le := rest.start_le, point_lt_finish := rest.point_lt_finish }

/-- Ordered rational points have nondecreasing original interval-owner indices.

The same finite cut list is scanned for both points. If the earlier point
passes a cut, the later point passes it too, so their original tail indices
remain ordered without sorting or replacing the cut list. -/
theorem pointOwnerBetween_index_mono (start finish first second : Fraction.Rational) :
    ∀ (cuts : List Fraction.Rational) (firstLower : start ≤ first) (firstUpper : first < finish)
      (secondLower : start ≤ second) (secondUpper : second < finish), first ≤ second →
      (pointOwnerBetween start finish first cuts firstLower firstUpper).index ≤
        (pointOwnerBetween start finish second cuts secondLower secondUpper).index
  | [], _, _, _, _, _ => Nat.le_refl 0
  | cut :: tail, firstLower, firstUpper, secondLower, secondUpper, ordered => by
      by_cases firstBefore : first < cut
      · rw [pointOwnerBetween, dif_pos firstBefore]
        exact Nat.zero_le _
      · have secondNotBefore : ¬ second < cut := by
          intro secondBefore
          have firstBefore' : first < cut :=
            ⟨Fraction.Order.Basic.le_trans _ _ _ ordered secondBefore.1,
              fun reverse => secondBefore.2 (Fraction.Order.Basic.le_trans _ _ _ reverse ordered)⟩
          exact firstBefore firstBefore'
        rw [pointOwnerBetween, dif_neg firstBefore, pointOwnerBetween, dif_neg secondNotBefore]
        exact Nat.succ_le_succ (pointOwnerBetween_index_mono cut finish first second tail
          (Fraction.Order.Arithmetic.le_of_not_gt_direct firstBefore) firstUpper
          (Fraction.Order.Arithmetic.le_of_not_gt_direct secondNotBefore) secondUpper ordered)

set_option genInjectivity false in
/-- A retained interval-list occurrence containing both endpoints of the exact child interval.

The certificate binds the parent to its actual list index and preserves the original child and enclosing endpoint
inequalities. -/
structure IntervalOwner (intervals : List Interval) (child : Interval) where
  /-- The exact parent occurrence's index in the retained interval list. -/ index : Nat
  /-- The original interval at the retained occurrence index. -/ parent : Interval
  /-- Looking up the retained index returns this exact parent interval. -/ at_index : Purelib.Data.List.getElem?
    intervals index = some parent
  /-- The parent's start is at most the original child's start. -/ start_le : parent.start ≤ child.start
  /-- The child's finish is at most the parent's finish. -/ finish_le : child.finish ≤ parent.finish

constructive_injectivity IntervalOwner

/-- For a fixed interval list and child, the occurrence index determines the owner.

The original lookup certificate determines the parent, and the containment
certificates are proof fields. Different indices remain different occurrences.
-/
theorem IntervalOwner.eq_of_index_eq {intervals : List Interval} {child : Interval}
    (first second : IntervalOwner intervals child) (indices : first.index = second.index) : first = second := by
  have parents : first.parent = second.parent := Option.some.inj
    (first.at_index.symm.trans ((congrArg (Purelib.Data.List.getElem? intervals) indices).trans second.at_index))
  cases first
  cases second
  cases indices
  cases parents
  rfl

end

end Purelib.Integration.Partition.Ownership
