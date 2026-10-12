module

public import Purelib.Data.Nat.Division

/-!
# Binary operations on retained natural values

The original low-bit recurrence consumes both finite natural arguments. Halving
the first nonzero argument strictly decreases the measure without changing the
retained branch decisions, second argument or bit-combining function.
-/

namespace Purelib.Data.Nat

/-- Combine the corresponding binary digits of two natural values.

The original zero cases return the retained argument or zero according to the
same bit function. Otherwise both arguments are halved, and the combined low bit
is appended to the recursive result. The first argument certifies termination.
-/
@[expose] public def bitwise (combine : Bool → Bool → Bool) (left right : _root_.Nat) : _root_.Nat :=
  if _leftZero : left = 0 then
    if combine false true then right else 0
  else if right = 0 then
    if combine true false then left else 0
  else
    let leftTail := left / 2
    let rightTail := right / 2
    let leftBit := left % 2 = 1
    let rightBit := right % 2 = 1
    let tail := bitwise combine leftTail rightTail
    if combine leftBit rightBit then tail + tail + 1 else tail + tail
termination_by left
decreasing_by
  exact Division.div_lt_self (_root_.Nat.zero_lt_of_ne_zero _leftZero) (by decide)

end Purelib.Data.Nat
