module

public import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Group.Negation
import Purelib.Tactic.Ring

/-!
# Centered coordinates of a split monic quadratic

The original ordered roots determine a midpoint and signed half-gap.
Explicit division by the retained nonzero two identifies their product
with the centered square minus the squared half-gap.
-/

public section

namespace Purelib.Polynomial.Quadratic.Split

open Purelib.Algebra.Field
open Purelib.Algebra.Group

attribute [local instance high] Negation.subNegZeroMonoid

variable {K : Type*} [ExplicitField K]

/-- The midpoint of the original ordered pair of roots. -/
@[expose] def center (first last : K) : K := (first + last) / 2

/-- The signed half-gap from the original first root to the original last root. -/
@[expose] def halfGap (first last : K) : K := (last - first) / 2

/-- Multiplying the original half-gap by the retained nonzero two recovers the full root displacement. -/
theorem halfGap_mul_two (first last : K) (twoNonzero : (2 : K) ≠ 0) :
    halfGap first last * 2 = last - first := ExplicitField.div_mul_cancel _ twoNonzero

/-- The midpoint minus the signed half-gap is the original first root. -/
theorem center_sub_halfGap (first last : K) (twoNonzero : (2 : K) ≠ 0) :
    center first last - halfGap first last = first := by
  apply ExplicitField.eq_of_mul_eq_mul_right twoNonzero
  calc
    (center first last - halfGap first last) * 2 =
        (first + last) / 2 * 2 - (last - first) / 2 * 2 := by
      unfold center halfGap
      ring1
    _ = (first + last) - (last - first) := by
      rewrite [ExplicitField.div_mul_cancel _ twoNonzero, ExplicitField.div_mul_cancel _ twoNonzero]
      rfl
    _ = first * 2 := by ring1

/-- The midpoint plus the signed half-gap is the original last root. -/
theorem center_add_halfGap (first last : K) (twoNonzero : (2 : K) ≠ 0) :
    center first last + halfGap first last = last := by
  apply ExplicitField.eq_of_mul_eq_mul_right twoNonzero
  calc
    (center first last + halfGap first last) * 2 =
        (first + last) / 2 * 2 + (last - first) / 2 * 2 := by
      unfold center halfGap
      ring1
    _ = (first + last) + (last - first) := by
      rewrite [ExplicitField.div_mul_cancel _ twoNonzero, ExplicitField.div_mul_cancel _ twoNonzero]
      rfl
    _ = last * 2 := by ring1

/-- The original split monic quadratic is its centered square minus the squared root half-gap.

The retained ordered roots are recovered from the same midpoint and half-gap.
Only the displayed nonzero-two certificate is required to cancel division;
the roots may coincide.
-/
theorem product_eq (first last point : K) (twoNonzero : (2 : K) ≠ 0) :
    (point - first) * (point - last) = (point - center first last) ^ 2 - halfGap first last ^ 2 := by
  have firstFactor : point - first = (point - center first last) + halfGap first last := by
    calc
      point - first = point - (center first last - halfGap first last) :=
        congrArg (fun root => point - root) (center_sub_halfGap first last twoNonzero).symm
      _ = (point - center first last) + halfGap first last := by ring1
  have lastFactor : point - last = (point - center first last) - halfGap first last := by
    calc
      point - last = point - (center first last + halfGap first last) :=
        congrArg (fun root => point - root) (center_add_halfGap first last twoNonzero).symm
      _ = (point - center first last) - halfGap first last := by ring1
  rewrite [firstFactor, lastFactor]
  ring1

/-- Distinct original roots have a nonzero signed half-gap when two is nonzero. -/
theorem halfGap_ne_zero {first last : K} (twoNonzero : (2 : K) ≠ 0) (different : first ≠ last) :
    halfGap first last ≠ 0 := by
  intro zero
  have displacement := halfGap_mul_two first last twoNonzero
  rewrite [zero] at displacement
  have equal : last = first := eq_of_sub_eq_zero (displacement.symm.trans (by ring1))
  exact different equal.symm

end Purelib.Polynomial.Quadratic.Split
