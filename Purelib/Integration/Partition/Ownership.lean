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

end

end Purelib.Integration.Partition.Ownership
