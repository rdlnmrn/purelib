module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.List.Sort.RationalKey.Basic

import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

open Purelib.Data.List.Sort.RationalKey

public section

/-! Finite size control for retained-payload sorting with duplicate removal. -/

namespace Purelib.Data.List.Sort.RationalKey.Size

universe u
variable {Alpha : Type u} (key : Alpha → Purelib.Data.Rat.Fraction.Rational)

/-- Insertion with equal-key removal increases a finite payload list's length by at most
one. -/
theorem insert_length_le (entry : Alpha) (entries : List Alpha) :
    (Basic.insert key entry entries).length ≤ entries.length + 1 := by
  induction entries with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
      unfold Basic.insert
      split
      · exact Nat.le_refl _
      · split
        · exact Nat.succ_le_succ ih
        · exact Nat.le_succ _

/-- Sorting with equal-key removal never increases the number of retained payloads. -/
theorem sort_length_le (entries : List Alpha) : (Basic.sort key entries).length ≤ entries.length := by
  induction entries with
  | nil => exact Nat.le_refl _
  | cons head tail ih => exact (Size.insert_length_le key head (Basic.sort key tail)).trans (Nat.succ_le_succ ih)

end Purelib.Data.List.Sort.RationalKey.Size

end
