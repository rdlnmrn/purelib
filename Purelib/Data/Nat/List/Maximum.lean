module

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Nat.Order
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

open Purelib

open Purelib.Data.Nat

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.CalculationSize

end Purelib.RootIsolation.CalculationSize

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.CalculationSize

end Purelib.RootIsolation.CalculationSize

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.Data.Nat.List.Maximum

/-- Compute the maximum of a finite natural list, with zero for the empty list.

The computation folds max from the initial accumulator zero, retaining no separate
enumeration or choice of a maximizing index. -/
def listMaximum : List Nat → Nat :=
  List.foldl max 0
end Purelib.Data.Nat.List.Maximum

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.CalculationSize

end Purelib.RootIsolation.CalculationSize

end

namespace Purelib.Data.Nat.List.Maximum

open Purelib
open Purelib.Data.Nat

/-- A finite maximum fold never falls below its initial accumulator. -/
private theorem foldl_max_initial_le : ∀ (values :
  List Nat)
    (initial : Nat), initial ≤ values.foldl max initial
  | [], _ => le_refl _
  | _ :: remaining, _ =>
      (Order.le_max_left _ _).trans (foldl_max_initial_le
        remaining _)

/-- Every member of a natural list is bounded by its maximum fold.

The bound holds for any initial natural accumulator, since each visited member is
included by the maximum operation. -/
private theorem member_le_foldl_max : ∀ (values :
  List Nat)
    (initial candidate : Nat), candidate ∈ values →
      candidate ≤ values.foldl max initial
  | [], _, _, member => nomatch member
  | value :: remaining, initial, candidate, member => by
      cases member with
      | head =>
          exact (Order.le_max_right _ _).trans
            (foldl_max_initial_le remaining _)
      | tail _ tail =>
        exact member_le_foldl_max remaining (max initial
          value) candidate tail

/-- Every natural list member is bounded by the list's computed maximum. -/
public theorem member_le_listMaximum (values : List
  Nat)
    (candidate : Nat) (member : candidate ∈ values) :
    candidate ≤ listMaximum values :=
  member_le_foldl_max values 0 candidate member

end Purelib.Data.Nat.List.Maximum
