module
import Purelib.Data.Rat.Fraction

public import Purelib.Data.Rat.Distance.Basic

import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.MinMax

section
public section

/-!
# Lp quantities of explicit empirical distributions

A nonempty displayed sample produces exact finite sample averages for every
natural-powered magnitude and distance.  Its executable essential maximum is
the recursively computed maximum over the displayed sample rows.
-/

namespace Purelib.Measure

open Purelib.Data.Rat
/-- Compute the largest displayed magnitude in a finite sample list.

The recursion takes rational separation from zero at each occurrence and retains zero for the empty list. Thus all
returned values are nonnegative. -/
@[expose] def sampleEssentialMaximumMagnitude {α : Type}
    (value : α → Fraction.Rational) : List α → Fraction.Rational
  | [] => 0
  | item :: remaining =>
      max (Distance.rationalSeparation (value item) 0)
        (sampleEssentialMaximumMagnitude value remaining)

/-- The recursive maximum magnitude is nonnegative for every finite sample list. -/
theorem sampleEssentialMaximumMagnitude_nonnegative {α : Type}
    (value : α → Fraction.Rational) : ∀ samples : List α,
    0 ≤ sampleEssentialMaximumMagnitude value samples
  | [] => le_rfl
  | _ :: remaining =>
      (sampleEssentialMaximumMagnitude_nonnegative value remaining).trans
        (Fraction.Order.Basic.le_max_right _ _)

/-- Compute the largest displayed separation of two readings over a finite sample list.

At each occurrence the reading is their rational difference. The computation returns zero on the empty list. -/
@[expose] def sampleEssentialMaximumDistance {α : Type}
    (left right : α → Fraction.Rational) (samples : List α) : Fraction.Rational :=
  sampleEssentialMaximumMagnitude
    (fun item => left item - right item) samples

/-- The recursive maximum distance is nonnegative for every finite sample list. -/
theorem sampleEssentialMaximumDistance_nonnegative {α : Type}
    (left right : α → Fraction.Rational) (samples : List α) :
    0 ≤ sampleEssentialMaximumDistance left right samples :=
  sampleEssentialMaximumMagnitude_nonnegative
    (fun item => left item - right item) samples
end Purelib.Measure

end
