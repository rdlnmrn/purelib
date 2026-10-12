module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Finite cached polynomial-clearance covers

Only unresolved intervals are bisected.  Each retained leaf certifies both a
squared-norm floor and an unsquared coordinate floor; internal nodes combine
the local floors, not a hull of component ranges.  The supplied finite depth
is an operational proposal budget, not a premise of soundness or evidence
that an unresolved polynomial has a zero.
-/

namespace Purelib.Data.Rat.Interval.Bisection

open Purelib.Data.Rat
/-- Compute the rational midpoint as half the sum of the retained endpoints. -/
def midpoint (parameters : Data.Rat.Interval.Bounds) : Fraction.Rational :=
  (parameters.lower + parameters.upper) / 2

/-- The retained lower endpoint is at most the rational midpoint. -/
theorem lower_le_midpoint (parameters : Data.Rat.Interval.Bounds) :
  parameters.lower ≤ midpoint parameters := by
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2) _ (by decide)
  rw [midpoint, Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
  calc
    parameters.lower * 2 = parameters.lower + parameters.lower := by ring1
    _ ≤ parameters.lower + parameters.upper := add_le_add le_rfl parameters.valid

/-- The rational midpoint is at most the retained upper endpoint. -/
theorem midpoint_le_upper (parameters : Data.Rat.Interval.Bounds) :
  midpoint parameters ≤ parameters.upper := by
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2) _ (by decide)
  rw [midpoint, Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
  calc
    parameters.lower + parameters.upper ≤ parameters.upper + parameters.upper := add_le_add parameters.valid le_rfl
    _ = parameters.upper * 2 := by ring1

/-- Construct the closed interval from the retained lower endpoint to the midpoint. -/
def leftHalf (parameters : Data.Rat.Interval.Bounds) :
    Data.Rat.Interval.Bounds :=
  ⟨parameters.lower, midpoint parameters, lower_le_midpoint parameters⟩

/-- Construct the closed interval from the midpoint to the retained upper endpoint. -/
def rightHalf (parameters : Data.Rat.Interval.Bounds) :
  Data.Rat.Interval.Bounds :=
  ⟨midpoint parameters, parameters.upper, midpoint_le_upper parameters⟩

/-- Every contained rational belongs to at least one of the two midpoint halves. -/
theorem inside_half {parameters : Data.Rat.Interval.Bounds} {parameter :
  Fraction.Rational} (inside : parameters.Contains parameter) :
    (leftHalf parameters).Contains parameter ∨ (rightHalf parameters).Contains
      parameter := by
  if before : parameter ≤ midpoint parameters then exact Or.inl ⟨inside.1, before⟩
  else exact Or.inr ⟨le_of_not_ge before, inside.2⟩

/-- Every rational contained in the left half lies in the original interval. -/
theorem leftHalf_subset {parameters : Data.Rat.Interval.Bounds} {parameter :
  Fraction.Rational}
    (inside : (leftHalf parameters).Contains parameter) : parameters.Contains parameter :=
  ⟨inside.1, inside.2.trans (midpoint_le_upper parameters)⟩

/-- Every rational contained in the right half lies in the original interval. -/
theorem rightHalf_subset {parameters : Data.Rat.Interval.Bounds} {parameter :
  Fraction.Rational}
    (inside : (rightHalf parameters).Contains parameter) : parameters.Contains parameter :=
  ⟨(lower_le_midpoint parameters).trans inside.1, inside.2⟩

end Purelib.Data.Rat.Interval.Bisection

end
