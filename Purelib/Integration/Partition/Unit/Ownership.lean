module
import Purelib.Data.List.GetD
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Partition.Interval
public import Purelib.Integration.Partition.Ownership
public import Purelib.Integration.Partition.Unit.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

/-!
# Indexed owners in retained unit partitions

A cached unit partition locates points and child intervals in its original
interval list. The returned certificates retain the actual parent occurrence
and use cut inclusion to certify the same child's enclosing endpoint bounds.
-/

namespace Purelib.Integration.Partition.Unit.Normalized

open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Partition

public section
/-- Locate the original partition occurrence owning a point in the half-open unit interval.

The result retains the actual interval index, parent and endpoint bounds from the partition's exact cached interval
chain. -/
@[expose] def pointOwner (partition : Normalized) (point : Fraction.Rational)
    (nonnegative : 0 ≤ point) (below : point < 1) : Ownership.PointOwner partition.intervals point :=
  let owner := Ownership.pointOwnerBetween 0 1 point partition.cuts nonnegative below
  { index := owner.index, parent := owner.parent, at_index := by
      rw [partition.intervals_eq]
      exact owner.at_index
    start_le := owner.start_le, point_lt_finish := owner.point_lt_finish }

/-- Locate a fine interval's original coarse owner when every coarse cut occurs in the fine partition.

The retained owner is found from the child's start, and cut inclusion certifies containment of the child's finish in
that same original parent. -/
@[expose] def intervalOwner (coarse fine : Normalized)
    (included : ∀ cut ∈ coarse.cuts, cut ∈ fine.cuts)
    (child : Interval) (member : child ∈ fine.intervals) :
    Ownership.IntervalOwner coarse.intervals child := by
  let bounds := fine.valid child member
  let owner := coarse.pointOwner child.start bounds.1 (bounds.2.1.trans_le bounds.2.2)
  refine { index := owner.index, parent := owner.parent, at_index := owner.at_index
           start_le := owner.start_le, finish_le := ?_ }
  apply Fraction.Order.Arithmetic.le_of_not_gt_direct
  intro below
  rcases coarse.finish_is_cut (Purelib.Data.List.mem_of_getElem? coarse.intervals owner.index owner.parent
    owner.at_index) with last | cut
  · exact (not_lt_of_ge bounds.2.2) (last ▸ below)
  · exact fine.no_cut_inside (included _ cut) member ⟨owner.point_lt_finish, below⟩

end

end Purelib.Integration.Partition.Unit.Normalized
