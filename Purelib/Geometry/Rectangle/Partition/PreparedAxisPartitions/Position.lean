module

public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Data.List.Membership

/-! # The literal position of an already selected retained interval

This cheap metadata reader consumes an existing interval and its original
list membership. It does not locate a geometric point again, select a
root, or inspect a numerical or primitive observation.
-/

public section

namespace Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval

open Purelib.Data.List

/-- Decide equality of two exact rational intervals, retaining their original endpoint payloads and order proofs. -/
private def decideEq (first last : Interval) : Decidable (first = last) :=
  if lower : first.lower = last.lower then
    if upper : first.upper = last.upper then
      isTrue (by cases first; cases last; cases lower; cases upper; rfl)
    else isFalse (fun equal => upper (congrArg (fun interval : Interval => interval.upper) equal))
  else isFalse (fun equal => lower (congrArg (fun interval : Interval => interval.lower) equal))

/-- Read the first literal occurrence of the supplied already selected interval, with its exact bounded readback. -/
def position (target : Interval) : (intervals : List Interval) → target ∈ intervals →
    {index : Fin intervals.length // intervals[index.val]'index.isLt = target}
  | [], present => False.elim (by cases present)
  | first :: remaining, present => by
      letI : Decidable (first = target) := decideEq first target
      if same : first = target then
        exact ⟨⟨0, Nat.zero_lt_succ _⟩, same⟩
      else
        have tailMember : target ∈ remaining := by
          rcases Membership.mem_cons.mp present with head | tail
          · exact False.elim (same head.symm)
          · exact tail
        let found := position target remaining tailMember
        exact ⟨found.val.succ, found.property⟩

end Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval

end
