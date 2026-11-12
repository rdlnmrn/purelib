module
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Interval.Basic
public import Purelib.Data.Rat.Interval.Width
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Exact rational interval bisection

The retained endpoints determine a midpoint and two closed halves. Scalar
half-width identities also apply to the ordinary rational interval owner.
-/

namespace Purelib.Data.Rat.Interval.Bisection

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
/-- Compute the rational midpoint as half the sum of the retained endpoints. -/
def midpoint (parameters : Data.Rat.Interval.Bounds) : Fraction.Rational :=
  (parameters.lower + parameters.upper) / 2

/-- The retained lower endpoint is at most the rational midpoint. -/
theorem lower_le_midpoint (parameters : Data.Rat.Interval.Bounds) :
  parameters.lower ≤ midpoint parameters := by
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := 2) _ (by decide)
  rw [midpoint, Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
  calc
    parameters.lower * 2 = parameters.lower + parameters.lower := by ring1
    _ ≤ parameters.lower + parameters.upper := Arithmetic.add_le_add_direct le_rfl parameters.valid

/-- The rational midpoint is at most the retained upper endpoint. -/
theorem midpoint_le_upper (parameters : Data.Rat.Interval.Bounds) :
  midpoint parameters ≤ parameters.upper := by
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := 2) _ (by decide)
  rw [midpoint, Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
  calc
    parameters.lower + parameters.upper ≤ parameters.upper + parameters.upper :=
      Arithmetic.add_le_add_direct parameters.valid le_rfl
    _ = parameters.upper * 2 := by ring1

/-- Division by two is multiplication by one half. -/
private theorem div_two_eq_mul_half (value : Fraction.Rational) :
    value / 2 = value * (1 / 2) := by
  change value * (2 : Fraction.Rational)⁻¹ =
    value * ((1 : Fraction.Rational) * (2 : Fraction.Rational)⁻¹)
  rw [Fraction.Field.one_mul]

/-- The upper endpoint minus the midpoint is half the original width. -/
theorem upper_sub_midpoint_eq_half_width
    (lower upper : Fraction.Rational) :
    upper - (lower + upper) / 2 = (upper - lower) * (1 / 2) := by
  have numerator :
      upper * 2 - (lower + upper) * 1 = upper - lower := by
    ring1
  calc
    upper - (lower + upper) / 2 =
        upper / 1 - (lower + upper) / 2 := by
      change upper - (lower + upper) / 2 =
        upper * (1 : Fraction.Rational)⁻¹ - (lower + upper) / 2
      rw [show (1 : Fraction.Rational)⁻¹ = 1 by decide,
        Fraction.Field.mul_one_direct]
    _ = (upper * 2 - (lower + upper) * 1) / (1 * 2) :=
      Fraction.Field.div_sub_div_direct upper 1
        (lower + upper) 2 (by decide) (by decide)
    _ = (upper - lower) / 2 := by
      rw [numerator, Fraction.Field.one_mul]
    _ = (upper - lower) * (1 / 2) := div_two_eq_mul_half _

/-- The midpoint minus the lower endpoint is half the original width. -/
theorem midpoint_sub_lower_eq_half_width
    (lower upper : Fraction.Rational) :
    (lower + upper) / 2 - lower = (upper - lower) * (1 / 2) := by
  have numerator :
      (lower + upper) * 1 - lower * 2 = upper - lower := by
    ring1
  calc
    (lower + upper) / 2 - lower =
        (lower + upper) / 2 - lower / 1 := by
      change (lower + upper) / 2 - lower =
        (lower + upper) / 2 - lower * (1 : Fraction.Rational)⁻¹
      rw [show (1 : Fraction.Rational)⁻¹ = 1 by decide,
        Fraction.Field.mul_one_direct]
    _ = ((lower + upper) * 1 - lower * 2) / (2 * 1) :=
      Fraction.Field.div_sub_div_direct (lower + upper) 2
        lower 1 (by decide) (by decide)
    _ = (upper - lower) / 2 := by
      rw [numerator, Fraction.Field.mul_one_direct]
    _ = (upper - lower) * (1 / 2) := div_two_eq_mul_half _

/-- Construct the closed interval from the retained lower endpoint to the midpoint. -/
def leftHalf (parameters : Data.Rat.Interval.Bounds) :
    Data.Rat.Interval.Bounds :=
  ⟨parameters.lower, midpoint parameters, lower_le_midpoint parameters⟩

/-- Construct the closed interval from the midpoint to the retained upper endpoint. -/
def rightHalf (parameters : Data.Rat.Interval.Bounds) :
  Data.Rat.Interval.Bounds :=
  ⟨midpoint parameters, parameters.upper, midpoint_le_upper parameters⟩

/-- The retained left half has exactly half the original interval width. -/
theorem leftHalf_width (parameters : Data.Rat.Interval.Bounds) :
    (leftHalf parameters).width = parameters.width / 2 := by
  change (parameters.lower + parameters.upper) / 2 - parameters.lower = (parameters.upper - parameters.lower) / 2
  apply Fraction.Field.mul_right_cancel_of_ne (by decide +kernel : (2 : Fraction.Rational) ≠ 0)
  calc
    _ = (parameters.lower + parameters.upper) / 2 * 2 - parameters.lower * 2 := by ring1
    _ = parameters.lower + parameters.upper - parameters.lower * 2 := by
      rewrite [Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide +kernel)]
      rfl
    _ = parameters.upper - parameters.lower := by ring1
    _ = _ := (Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide +kernel)).symm

/-- The retained right half has exactly the same half width. -/
theorem rightHalf_width (parameters : Data.Rat.Interval.Bounds) :
    (rightHalf parameters).width = parameters.width / 2 := by
  change parameters.upper - (parameters.lower + parameters.upper) / 2 = (parameters.upper - parameters.lower) / 2
  apply Fraction.Field.mul_right_cancel_of_ne (by decide +kernel : (2 : Fraction.Rational) ≠ 0)
  calc
    _ = parameters.upper * 2 - (parameters.lower + parameters.upper) / 2 * 2 := by ring1
    _ = parameters.upper * 2 - (parameters.lower + parameters.upper) := by
      rewrite [Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide +kernel)]
      rfl
    _ = parameters.upper - parameters.lower := by ring1
    _ = _ := (Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide +kernel)).symm

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

namespace Purelib.Data.Rat.Interval

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- Compute the midpoint of the original rational interval's exact endpoints. -/
def midpoint (bound : Interval) : Fraction.Rational :=
  Bisection.midpoint ⟨bound.lower, bound.upper, bound.valid⟩

/-- The computed midpoint lies in the original closed rational interval. -/
theorem midpoint_contains (bound : Interval) : bound.Contains bound.midpoint :=
  ⟨Bisection.lower_le_midpoint ⟨bound.lower, bound.upper, bound.valid⟩,
    Bisection.midpoint_le_upper ⟨bound.lower, bound.upper, bound.valid⟩⟩

/-- Negating the original interval negates its rational midpoint. -/
theorem midpoint_neg (bound : Interval) : bound.neg.midpoint = -bound.midpoint := by
  change ((-bound.upper + -bound.lower) / 2) = -((bound.lower + bound.upper) / 2)
  change (-bound.upper + -bound.lower) * (2 : Fraction.Rational)⁻¹ =
    -((bound.lower + bound.upper) * (2 : Fraction.Rational)⁻¹)
  ring1

/-- Scaling an interval by a nonnegative factor scales its rational midpoint. -/
theorem midpoint_scale (bound : Interval) (factor : Fraction.Rational) (nonnegative : 0 ≤ factor) :
    (bound.scale factor nonnegative).midpoint = factor * bound.midpoint := by
  change (factor * bound.lower + factor * bound.upper) / 2 = factor * ((bound.lower + bound.upper) / 2)
  change (factor * bound.lower + factor * bound.upper) * (2 : Fraction.Rational)⁻¹ =
    factor * ((bound.lower + bound.upper) * (2 : Fraction.Rational)⁻¹)
  ring1

/-- Every rational in the original interval is within half its width of the midpoint.

The absolute difference is bounded using both original endpoints and their
exact scalar half-width identities. No completed value is involved. -/
theorem abs_sub_midpoint_le {bound : Interval} {value : Fraction.Rational} (inside : bound.Contains value) :
    Fraction.abs (value - bound.midpoint) ≤ bound.width * (1 / 2) := by
  have upper : value - bound.midpoint ≤ bound.upper - bound.midpoint :=
    Arithmetic.sub_le_sub_direct inside.2 (Fraction.Order.Basic.le_refl _)
  have lower : bound.midpoint - value ≤ bound.midpoint - bound.lower :=
    Arithmetic.sub_le_sub_direct (Fraction.Order.Basic.le_refl _) inside.1
  have upperHalf : bound.upper - bound.midpoint = bound.width * (1 / 2) :=
    Bisection.upper_sub_midpoint_eq_half_width bound.lower bound.upper
  have lowerHalf : bound.midpoint - bound.lower = bound.width * (1 / 2) :=
    Bisection.midpoint_sub_lower_eq_half_width bound.lower bound.upper
  rw [upperHalf] at upper
  rw [lowerHalf] at lower
  change max (value - bound.midpoint) (-(value - bound.midpoint)) ≤ bound.width * (1 / 2)
  apply Fraction.Order.Basic.max_le upper
  have reverse : -(value - bound.midpoint) = bound.midpoint - value := by ring1
  rw [reverse]
  exact lower

end Purelib.Data.Rat.Interval

end

public section

namespace Purelib.Data.Rat.Interval.Bisection

open Purelib.Data.Rat
open Purelib.Data.List

/-- Bisect each retained interval once, keeping both closed halves in their original left-to-right order. -/
@[expose] def refine : List Bounds → List Bounds
  | [] => []
  | span :: spans => leftHalf span :: rightHalf span :: refine spans

/-- Original ordered concatenation is preserved by interval bisection. -/
theorem refine_append (left right : List Bounds) : refine (left ++ right) = refine left ++ refine right := by
  induction left with
  | nil => rfl
  | cons span spans inductionHypothesis =>
      exact congrArg (fun tail => leftHalf span :: rightHalf span :: tail) inductionHypothesis

/-- Retain the ordered dyadic midpoint parts of the original closed rational interval.

Each stage bisects its same preceding ordered interval list. These are only
original Bounds objects and their validity proofs; no numerical observations
or independent partition certificate are constructed.
-/
@[expose] def parts : Nat → Bounds → List Bounds
  | 0, span => [span]
  | depth + 1, span => refine (parts depth span)

/-- The actual dyadic parts split into the original left and right half traces with their shared midpoint. -/
theorem parts_split (depth : Nat) (span : Bounds) :
    parts (depth + 1) span = parts depth (leftHalf span) ++ parts depth (rightHalf span) := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change refine (parts (depth + 1) span) =
        refine (parts depth (leftHalf span)) ++ refine (parts depth (rightHalf span))
      rewrite [inductionHypothesis, refine_append]
      rfl

/-- Every actual dyadic part remains inside the same original retained interval. -/
theorem parts_subset (depth : Nat) (span : Bounds) {part : Bounds} (member : part ∈ parts depth span)
    {time : Fraction.Rational} (contained : part.Contains time) : span.Contains time := by
  induction depth generalizing span with
  | zero =>
      have equal : part = span := Membership.mem_singleton.mp member
      exact Eq.mp (congrArg (fun bounds : Bounds => bounds.Contains time) equal) contained
  | succ depth inductionHypothesis =>
      rewrite [parts_split] at member
      rcases Membership.mem_append.mp member with left | right
      · exact leftHalf_subset (inductionHypothesis (leftHalf span) left)
      · exact rightHalf_subset (inductionHypothesis (rightHalf span) right)

/-- Successive dyadic refinements retain the original ordered coarse parts and each same ordered descendant row. -/
theorem parts_add (coarse extra : Nat) (span : Bounds) :
    parts (coarse + extra) span = (parts coarse span).flatMap (parts extra) := by
  induction coarse generalizing span with
  | zero =>
      rewrite [Nat.zero_add]
      exact (Append.append_nil _).symm
  | succ coarse inductionHypothesis =>
      rewrite [Nat.succ_add, parts_split, parts_split, Flatten.flatMap_append,
        inductionHypothesis (leftHalf span), inductionHypothesis (rightHalf span)]
      rfl

/-- Every actual later dyadic part belongs to an original coarse part's same ordered descendant row. -/
theorem parts_ancestor (coarse extra : Nat) (span : Bounds) {part : Bounds}
    (member : part ∈ parts (coarse + extra) span) :
    ∃ parent ∈ parts coarse span, part ∈ parts extra parent := by
  rewrite [parts_add] at member
  exact Flatten.mem_flatMap.mp member

/-- Each actual dyadic part has exactly the original width times the finite half power. -/
theorem parts_width (depth : Nat) (span : Bounds) {part : Bounds} (member : part ∈ parts depth span) :
    part.width = span.width * (1 / 2 : Fraction.Rational) ^ depth := by
  induction depth generalizing span with
  | zero =>
      have equal : part = span := Membership.mem_singleton.mp member
      rewrite [equal, pow_zero, Fraction.Field.mul_one_direct]
      rfl
  | succ depth inductionHypothesis =>
      rewrite [parts_split] at member
      have child : ∃ half : Bounds, part ∈ parts depth half ∧ half.width = span.width / 2 := by
        rcases Membership.mem_append.mp member with left | right
        · exact ⟨leftHalf span, left, leftHalf_width span⟩
        · exact ⟨rightHalf span, right, rightHalf_width span⟩
      rcases child with ⟨half, member, width⟩
      have retained := inductionHypothesis half member
      rewrite [width] at retained
      exact retained.trans (by
        rewrite [pow_succ]
        simp only [Fraction.Field.div_eq_mul_inv_direct]
        ring1)

/-- Strict original endpoints give strictly ordered endpoints in every actual retained dyadic part. -/
theorem parts_proper (depth : Nat) (span : Bounds) (proper : span.lower < span.upper)
    {part : Bounds} (member : part ∈ parts depth span) : part.lower < part.upper := by
  have positive := Fraction.Order.Arithmetic.mul_pos_direct (Bounds.width_pos proper)
    (Fraction.Order.Arithmetic.pow_pos_direct (by decide +kernel : (0 : Fraction.Rational) < 1 / 2) depth)
  exact Fraction.Order.Arithmetic.lt_of_sub_pos_direct
    (positive.trans_eq (parts_width depth span member).symm)

end Purelib.Data.Rat.Interval.Bisection
