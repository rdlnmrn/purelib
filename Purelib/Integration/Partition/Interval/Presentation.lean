module

public import Purelib.Data.Presentation
public import Purelib.Integration.Partition.Interval
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Integration.Partition.Interval.Presentation

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- The finite display of an unrestricted partition interval. -/
public abbrev Code := Fraction.Rational × Fraction.Rational

/-- Construct the original interval from its two retained endpoints. -/
@[expose] public def read (code : Code) : Interval := ⟨code.1, code.2⟩

/-- Project the endpoints of an original interval without imposing validity. -/
@[expose] public def quote (interval : Interval) : Code := ⟨interval.start, interval.finish⟩

/-- Reading quoted endpoints recovers the original interval. -/
public theorem read_quote (interval : Interval) : read (quote interval) = interval := by
  cases interval
  rfl

/-- Quoting read endpoints recovers the original pair. -/
public theorem quote_read (code : Code) : quote (read code) = code := by
  cases code
  rfl

/-- The original interval equality decides equality of endpoint displays. -/
@[expose] public def compare (left right : Code) : Decidable (left = right) :=
  match (inferInstance : Decidable (read left = read right)) with
  | .isTrue equal => .isTrue ((quote_read left).symm.trans ((congrArg quote equal).trans (quote_read right)))
  | .isFalse unequal => .isFalse (fun equal => unequal (congrArg read equal))

set_option genInjectivity false in
/-- A unit-cell validity check retains the original evidence or the failed bound. -/
public inductive Check (interval : Interval) where
  /-- The interval has the original positive-length unit validity evidence. -/
  | valid (proof : interval.Valid)
  /-- The start lies below zero. -/
  | negativeStart (proof : interval.start < 0)
  /-- The finish is at or before the start. -/
  | nonpositiveLength (proof : interval.finish ≤ interval.start)
  /-- The finish lies above one. -/
  | aboveOne (proof : 1 < interval.finish)

/-- Check the three original unit-cell bounds using rational comparisons. -/
@[expose] public def check (interval : Interval) : Check interval :=
  if start : 0 ≤ interval.start then
    if length : interval.start < interval.finish then
      if finish : interval.finish ≤ 1 then .valid ⟨start, length, finish⟩
      else .aboveOne (lt_of_not_ge finish)
    else .nonpositiveLength (le_of_not_gt length)
  else .negativeStart (lt_of_not_ge start)

/-- Decide the original unit-cell validity predicate using the typed check. -/
@[expose] public def recognize (interval : Interval) : Decidable interval.Valid :=
  match check interval with
  | .valid proof => .isTrue proof
  | .negativeStart proof => .isFalse (fun valid => (not_lt_of_ge valid.1) proof)
  | .nonpositiveLength proof => .isFalse (fun valid => (not_lt_of_ge proof) valid.2.1)
  | .aboveOne proof => .isFalse (fun valid => (not_lt_of_ge valid.2.2) proof)

/-!
## Partition interval endpoints and unit-cell validity

Every pair of canonical rational endpoints presents an original `Interval`,
including reversed endpoints. `read_quote` and `quote_read` recover both
owners, and `compare` uses the original interval equality decision. Separately,
`check` checks the original `Interval.Valid` predicate: nonnegative start,
strictly positive length and finish at most one. Its rejected branches retain
proofs of the failed bounds. All decisions use the original finite rational
comparisons; proof-system and native-execution certification remain separate.
-/
/-- The unrestricted endpoint presentation of original partition intervals. -/
@[expose] public def interval : Purelib.Data.Presentation Code where
  Valid := fun _ => True
  recognize := fun _ => .isTrue True.intro
  Same := fun left right => left.val = right.val
  compare := fun left right => compare left.val right.val
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

end Purelib.Integration.Partition.Interval.Presentation
