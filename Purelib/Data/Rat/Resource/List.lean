module
public import Purelib.Data.Rat.Fraction.Resource.Model

import Purelib.Data.Rat.Fraction.Basic

import Mathlib.Order.Basic
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Mathlib.Data.Nat.Basic

/-!
# Maximum resource magnitude over a retained coefficient list
-/

namespace Purelib.Data.Rat.Resource.List

open Purelib.Data.Rat

public section

section
/-- Folding maximum over reduced-fraction magnitudes never decreases its initial natural bound.

Each fold step retains the greater of its previous bound and the next displayed magnitude. The empty list retains the
original initial bound. -/
theorem foldl_max_le_final : ∀ (values : List Fraction.Basic.ReducedFraction)
    (current : Nat), current ≤ values.foldl
      (fun bound value => max bound (Fraction.Resource.Model.rationalModel.magnitude value)) current
  | [], _ => le_refl _
  | _ :: remaining, _ =>
      ((Nat.Order.max_eq_natMax _ _).symm ▸ Nat.Order.le_max_left _ _).trans
        (Purelib.Data.Rat.Resource.List.foldl_max_le_final remaining
        _)
/-- The folded maximum of reduced-fraction magnitudes bounds each member's magnitude.

Membership selects an original coefficient occurrence. Its magnitude is bounded by the same ordered maximum fold from
any supplied initial bound. -/
theorem member_le_foldl_max : ∀ (values : List Fraction.Basic.ReducedFraction)
    (current : Nat) {candidate : Fraction.Basic.ReducedFraction}, candidate ∈ values →
    Fraction.Resource.Model.rationalModel.magnitude candidate ≤
      values.foldl
        (fun bound value => max bound (Fraction.Resource.Model.rationalModel.magnitude value)) current
  | [], _, _, member => by cases member
  | value :: remaining, current, candidate, member => by
      rcases Purelib.Data.List.Membership.mem_cons.mp member with head | tail
      · rw [head]
        exact ((Nat.Order.max_eq_natMax _ _).symm ▸ Nat.Order.le_max_right _ _).trans
          (Purelib.Data.Rat.Resource.List.foldl_max_le_final
          remaining _)
      · exact Purelib.Data.Rat.Resource.List.member_le_foldl_max remaining
          (max current (Fraction.Resource.Model.rationalModel.magnitude value)) tail
end

end

end Purelib.Data.Rat.Resource.List
