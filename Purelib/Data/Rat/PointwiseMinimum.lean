module
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Order
public import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Data.List.Membership

/-!
# Pointwise minima of nonempty rational families
-/

namespace Purelib.Data.Rat

open Purelib.Data.Rat

public section

/-- Compute the pointwise minimum of a nonempty finite family of rational-valued functions.

Retain the first function separately so the family is nonempty. At each input, recursively compare its value with the
pointwise minimum of the remaining family, preserving the original domain and function members. -/
@[expose] def pointwiseMinimum {α : Type} (first : α → Fraction.Rational) :
    List (α → Fraction.Rational) → α → Fraction.Rational
  | [], item => first item
  | next :: remaining, item =>
      min (first item) (pointwiseMinimum next remaining item)

/-- The pointwise finite minimum is at most every retained member at each input.

The supplied membership identifies an original function of the nonempty family. The bound holds at the displayed input
without comparing functions or changing their domain. -/
theorem pointwiseMinimum_le_of_mem {α : Type}
    (first : α → Fraction.Rational) (remaining : List (α → Fraction.Rational))
    {candidate : α → Fraction.Rational}
    (member : candidate ∈ first :: remaining) (item : α) :
    pointwiseMinimum first remaining item ≤ candidate item := by
  induction remaining generalizing first candidate with
  | nil =>
      have same : candidate = first := Purelib.Data.List.Membership.mem_singleton.mp member
      subst candidate
      exact le_rfl
  | cons next remaining inductionHypothesis =>
      rcases Purelib.Data.List.Membership.mem_cons.mp member with same | tail
      · subst candidate
        exact Fraction.Order.Basic.min_le_left _ _
      · exact (Fraction.Order.Basic.min_le_right _ _).trans
          (inductionHypothesis next tail)

end

end Purelib.Data.Rat
