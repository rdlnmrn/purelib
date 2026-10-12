module

import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section
public section

/-!
# Certified rational bounds

This module contains the interval arithmetic used by the finite measure
development.  A bound is displayed rational data with an order certificate.
It is not an interval in a completed line and does not denote a supremum,
infimum, or limit.
-/

namespace Purelib.Data.Rat

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- Retain the lower and upper endpoints of a closed rational interval with their order witness.

The validity field retains the proof that the lower endpoint is at most the upper endpoint. Closed containment includes
both endpoints; all constructions preserve this exact nominal carrier and its stored endpoint evidence. -/
structure Interval where
  /-- The retained lower rational endpoint. -/ lower : Fraction.Rational
  /-- The retained upper rational endpoint. -/ upper : Fraction.Rational
  /-- Evidence that the lower endpoint is at most the upper endpoint. -/ valid : lower ≤ upper

constructive_injectivity Interval

namespace Interval

end Interval
namespace Interval
open Purelib.Data.Rat.Interval

open Purelib.Data in
/-- Two retained rational intervals with equal endpoints are equal records. -/
@[ext] theorem ext {left right : Rat.Interval}
    (lower : left.lower = right.lower)
    (upper : left.upper = right.upper) : left = right := by
  cases left with
  | mk leftLower leftUpper leftValid =>
    cases right with
    | mk rightLower rightUpper rightValid =>
      cases lower
      cases upper
      rfl

section
open Purelib.Data
open Purelib.Data.Rat
/-- Construct the singleton rational interval at the supplied value. -/
@[expose] def exact (value : Fraction.Rational) : Rat.Interval :=
  ⟨value, value, le_rfl⟩

/-- Read the interval width as its upper endpoint minus its lower endpoint. -/
@[expose] def width (bound : Rat.Interval) : Fraction.Rational :=
  bound.upper - bound.lower

end

open Purelib.Data in
/-- Every retained rational interval has nonnegative width. -/
theorem width_nonneg (bound : Rat.Interval) : 0 ≤ bound.width :=
  Purelib.Data.Rat.Fraction.Order.Arithmetic.sub_nonneg_direct bound.valid

open Purelib.Data.Rat in
/-- A singleton rational interval has zero width. -/
@[simp] theorem exact_width (value : Fraction.Rational) :
    (exact value).width = 0 := by
  dsimp only [Interval.width, exact]
  ring1

section
open Purelib.Data
open Purelib.Data.Rat
/-- Require a rational value to lie between the retained lower and upper endpoints. -/
@[expose] def Contains (bound : Rat.Interval) (value : Fraction.Rational) : Prop :=
  bound.lower ≤ value ∧ value ≤ bound.upper

/-- Decide containment using the two concrete rational endpoint comparisons. -/
instance containsDecidable (bound : Rat.Interval) (value : Fraction.Rational) :
    Decidable (bound.Contains value) := by
  unfold Interval.Contains
  infer_instance

/-- Two values contained in a zero-width rational interval are equal. -/
theorem eq_of_contains_of_contains_of_width_eq_zero
    {bound : Rat.Interval} {left right : Fraction.Rational}
    (leftInside : bound.Contains left)
    (rightInside : bound.Contains right)
    (widthZero : bound.width = 0) : left = right := by
  have upperLeLower : bound.upper ≤ bound.lower := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    change bound.upper - bound.lower = 0 at widthZero
    calc
      0 ≤ -(bound.upper - bound.lower) := by
        rw [widthZero, neg_zero]
      _ = bound.lower - bound.upper := by ring1
  apply le_antisymm
  · exact leftInside.2.trans (upperLeLower.trans rightInside.1)
  · exact rightInside.2.trans (upperLeLower.trans leftInside.1)

end

open Purelib.Data.Rat in
/-- A singleton interval contains a candidate exactly when it equals the retained value. -/
theorem exact_contains_iff (value candidate : Fraction.Rational) :
    (exact value).Contains candidate ↔ candidate = value := by
  constructor
  · intro inside
    exact le_antisymm inside.2 inside.1
  · intro equal
    rw [equal]
    exact ⟨le_rfl, le_rfl⟩

section
open Purelib.Data
/-- Construct the sum interval by adding corresponding endpoints and retaining their order proof.

The constructor uses the exact sums of the two lower and two upper endpoints. The retained validity witnesses prove the
new endpoint order, and containment transports the sum of any two input values. -/
@[expose] def add (left right : Rat.Interval) : Rat.Interval where
  lower := left.lower + right.lower
  upper := left.upper + right.upper
  valid := add_le_add left.valid right.valid

section
open Purelib.Data.Rat
/-- The sum interval's lower endpoint is the sum of the two lower endpoints. -/
@[simp] theorem add_lower (left right : Rat.Interval) :
    (Interval.add left right).lower = left.lower + right.lower := rfl

/-- The sum interval's upper endpoint is the sum of the two upper endpoints. -/
@[simp] theorem add_upper (left right : Rat.Interval) :
    (Interval.add left right).upper = left.upper + right.upper := rfl

/-- The width of the sum interval is the sum of the input widths. -/
theorem add_width (left right : Rat.Interval) :
    (Interval.add left right).width = left.width + right.width := by
  dsimp only [Interval.width, Interval.add]
  ring1

/-- The sum interval contains the sum of any two values contained in its inputs. -/
theorem add_contains {left right : Rat.Interval} {x y : Fraction.Rational}
    (leftInside : left.Contains x) (rightInside : right.Contains y) :
    (Interval.add left right).Contains (x + y) :=
  ⟨add_le_add leftInside.1 rightInside.1,
    add_le_add leftInside.2 rightInside.2⟩

/-- Negate a rational interval by exchanging and negating its endpoints.

The upper endpoint becomes the negation of the original lower endpoint, and the lower endpoint becomes the negation of
the original upper endpoint. The reversed order proof is retained in the new interval. -/
@[expose] def neg (bound : Rat.Interval) : Rat.Interval where
  lower := -bound.upper
  upper := -bound.lower
  valid := Fraction.Order.Arithmetic.neg_le_neg_direct bound.valid

end

/-- The negated interval's lower endpoint is the negation of the original upper endpoint. -/
@[simp] theorem neg_lower (bound : Rat.Interval) :
    bound.neg.lower = -bound.upper := rfl

/-- The negated interval's upper endpoint is the negation of the original lower endpoint. -/
@[simp] theorem neg_upper (bound : Rat.Interval) :
    bound.neg.upper = -bound.lower := rfl

section
open Purelib.Data.Rat
/-- Negating an interval preserves its width. -/
theorem neg_width (bound : Rat.Interval) : bound.neg.width = bound.width := by
  dsimp only [Interval.neg, Interval.width]
  ring1

/-- Negating an interval retains containment of the negated value. -/
theorem neg_contains {bound : Rat.Interval} {value : Fraction.Rational}
    (inside : bound.Contains value) : bound.neg.Contains (-value) :=
  ⟨Fraction.Order.Arithmetic.neg_le_neg_direct inside.2,
    Fraction.Order.Arithmetic.neg_le_neg_direct inside.1⟩

/-- Negating a rational interval twice recovers the original record. -/
@[simp] theorem neg_neg_bound (bound : Rat.Interval) : bound.neg.neg = bound := by
  apply Interval.ext <;> dsimp only [Interval.neg] <;> ring1

/-- The negated interval contains a value exactly when the original contains its negation. -/
theorem neg_contains_iff {bound : Rat.Interval} {value : Fraction.Rational} :
    bound.neg.Contains value ↔ bound.Contains (-value) := by
  constructor
  · intro inside
    have transported := Interval.neg_contains inside
    simpa only [Interval.neg_neg_bound] using transported
  · intro inside
    have transported := Interval.neg_contains inside
    have doubleNegation : -(-value) = value := by ring1
    rw [doubleNegation] at transported
    exact transported

end

/-- Construct a difference interval by adding the left interval to the negation of the right. -/
@[expose] def sub (left right : Rat.Interval) : Rat.Interval :=
  left.add right.neg

section
open Purelib.Data.Rat
/-- The width of a difference interval is the sum of its input widths. -/
theorem sub_width (left right : Rat.Interval) :
    (left.sub right).width = left.width + right.width := by
  rw [Interval.sub, Interval.add_width, Interval.neg_width]

/-- The difference interval contains the difference of any two values contained in its inputs. -/
theorem sub_contains {left right : Rat.Interval} {x y : Fraction.Rational}
    (leftInside : left.Contains x) (rightInside : right.Contains y) :
    (left.sub right).Contains (x - y) := by
  change (left.add right.neg).Contains (x + -y)
  exact Interval.add_contains leftInside (Interval.neg_contains rightInside)

/-- Multiply both interval endpoints by a supplied nonnegative rational factor.

The explicit nonnegativity witness preserves endpoint order under multiplication. The original endpoints are scaled
directly, without selecting a sign branch or changing the nominal interval carrier. -/
@[expose] def scale (factor : Fraction.Rational) (nonnegative : 0 ≤ factor)
    (bound : Rat.Interval) : Rat.Interval where
  lower := factor * bound.lower
  upper := factor * bound.upper
  valid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    bound.valid nonnegative

/-- Scaling by a nonnegative rational multiplies interval width by that same factor. -/
theorem scale_width (factor : Fraction.Rational) (nonnegative : 0 ≤ factor)
    (bound : Rat.Interval) :
    (Interval.scale factor nonnegative bound).width = factor * bound.width := by
  dsimp only [Interval.width, Interval.scale]
  ring1

/-- Nonnegative interval scaling retains containment of the correspondingly scaled value. -/
theorem scale_contains {factor : Fraction.Rational} (nonnegative : 0 ≤ factor)
    {bound : Rat.Interval} {value : Fraction.Rational} (inside : bound.Contains value) :
    (Interval.scale factor nonnegative bound).Contains (factor * value) :=
  ⟨Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      inside.1 nonnegative,
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      inside.2 nonnegative⟩

end

/-- Retain evidence that the inner interval's endpoints lie within the outer endpoints.

The lower field compares the outer lower endpoint to the inner lower endpoint, and the upper field compares the inner
upper endpoint to the outer upper endpoint. These witnesses transport containment and bound the inner width. -/
structure Refines (inner outer : Rat.Interval) : Prop where
  /-- The outer lower endpoint is at most the inner lower endpoint. -/ lower : outer.lower ≤ inner.lower
  /-- The inner upper endpoint is at most the outer upper endpoint. -/ upper : inner.upper ≤ outer.upper

end

namespace Refines

section
open Purelib.Data
open Purelib.Data.Rat
/-- Every rational interval refines itself. -/
theorem refl (bound : Rat.Interval) : Interval.Refines bound bound :=
  ⟨le_rfl, le_rfl⟩

/-- Compose rational interval refinement through the same retained middle interval. -/
theorem trans {inner middle outer : Rat.Interval}
    (innerMiddle : Interval.Refines inner middle)
    (middleOuter : Interval.Refines middle outer) : Interval.Refines inner outer :=
  ⟨middleOuter.lower.trans innerMiddle.lower,
    innerMiddle.upper.trans middleOuter.upper⟩

/-- An outer interval contains every value contained in an interval refining it. -/
theorem contains {inner outer : Rat.Interval} (refines : Interval.Refines inner outer)
    {value : Fraction.Rational} (inside : inner.Contains value) :
    outer.Contains value :=
  ⟨refines.lower.trans inside.1, inside.2.trans refines.upper⟩

/-- Refining a rational interval cannot increase its width. -/
theorem width_le {inner outer : Rat.Interval} (refines : Interval.Refines inner outer) :
    inner.width ≤ outer.width :=
  Fraction.Order.Arithmetic.sub_le_sub_direct refines.upper refines.lower

/-- Adding two interval refinements preserves endpoint refinement. -/
theorem add {innerLeft outerLeft innerRight outerRight : Rat.Interval}
    (left : Interval.Refines innerLeft outerLeft)
    (right : Interval.Refines innerRight outerRight) :
    Interval.Refines (innerLeft.add innerRight) (outerLeft.add outerRight) :=
  ⟨add_le_add left.lower right.lower,
    add_le_add left.upper right.upper⟩

/-- Negation preserves rational interval refinement. -/
theorem neg {inner outer : Rat.Interval} (refines : Interval.Refines inner outer) :
    Interval.Refines inner.neg outer.neg :=
  ⟨Fraction.Order.Arithmetic.neg_le_neg_direct refines.upper,
    Fraction.Order.Arithmetic.neg_le_neg_direct refines.lower⟩

/-- Subtracting two interval refinements preserves endpoint refinement. -/
theorem sub {innerLeft outerLeft innerRight outerRight : Rat.Interval}
    (left : Interval.Refines innerLeft outerLeft)
    (right : Interval.Refines innerRight outerRight) :
    Interval.Refines (innerLeft.sub innerRight) (outerLeft.sub outerRight) :=
  left.add right.neg

/-- Scaling both intervals by the same nonnegative rational preserves refinement. -/
theorem scale (factor : Fraction.Rational) (nonnegative : 0 ≤ factor)
    {inner outer : Rat.Interval} (refines : Interval.Refines inner outer) :
    Interval.Refines (inner.scale factor nonnegative) (outer.scale factor nonnegative) :=
  ⟨Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      refines.lower nonnegative,
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      refines.upper nonnegative⟩

end

end Refines

section
open Purelib.Data
/-- Require each interval's lower endpoint to be at most the other interval's upper endpoint. -/
@[expose] def Overlaps (left right : Rat.Interval) : Prop :=
  left.lower ≤ right.upper ∧ right.lower ≤ left.upper

open Purelib.Data.Rat in
/-- Decide overlap using the two retained endpoint comparisons. -/
instance overlapsDecidable (left right : Rat.Interval) :
    Decidable (left.Overlaps right) := by
  unfold Interval.Overlaps
  infer_instance

section
open Purelib.Data.Rat
/-- Two rational intervals containing a common value overlap. -/
theorem overlaps_of_common {left right : Rat.Interval} {value : Fraction.Rational}
    (leftInside : left.Contains value) (rightInside : right.Contains value) :
    left.Overlaps right :=
  ⟨leftInside.1.trans rightInside.2,
    rightInside.1.trans leftInside.2⟩

/-- Choose the larger lower endpoint as an explicit overlap candidate.

Take the maximum of the two lower endpoints, a total executable rational operation. The overlap hypothesis is required
only for the theorem that this candidate belongs to both original intervals. -/
@[expose] def overlapWitness (left right : Rat.Interval) : Fraction.Rational :=
  max left.lower right.lower

/-- When two intervals overlap, their chosen overlap witness lies in both. -/
theorem overlapWitness_inside {left right : Rat.Interval}
    (overlaps : left.Overlaps right) :
    left.Contains (Interval.overlapWitness left right) ∧
      right.Contains (Interval.overlapWitness left right) :=
  ⟨⟨Fraction.Order.Basic.le_max_left _ _, Fraction.Order.Basic.max_le left.valid overlaps.2⟩,
    ⟨Fraction.Order.Basic.le_max_right _ _, Fraction.Order.Basic.max_le overlaps.1 right.valid⟩⟩

/-- Both directed differences between contained values are bounded by the interval width. -/
theorem pairwise_difference_le {bound : Rat.Interval} {left right : Fraction.Rational}
    (leftInside : bound.Contains left)
    (rightInside : bound.Contains right) :
    left - right ≤ bound.width ∧ right - left ≤ bound.width :=
  ⟨Fraction.Order.Arithmetic.sub_le_sub_direct leftInside.2 rightInside.1,
    Fraction.Order.Arithmetic.sub_le_sub_direct rightInside.2 leftInside.1⟩

/-- Choose the retained lower endpoint as an explicit interval sample. -/
@[expose] def sample (bound : Rat.Interval) : Fraction.Rational :=
  bound.lower

end

/-- The chosen lower-endpoint sample lies in its original interval. -/
theorem sample_contains (bound : Rat.Interval) : bound.Contains bound.sample :=
  ⟨le_rfl, bound.valid⟩

open Purelib.Data.Rat
/-- Both directed differences between a contained value and the chosen sample are bounded by interval width. -/
theorem sample_difference_le {bound : Rat.Interval} {value : Fraction.Rational}
    (inside : bound.Contains value) :
    value - bound.sample ≤ bound.width ∧
      bound.sample - value ≤ bound.width :=
  Interval.pairwise_difference_le inside bound.sample_contains

/-! ## Exact finite interval cuts -/

/-- Keep the original lower endpoint and use the supplied contained cut as the new upper endpoint. -/
@[expose] def cutLeft (bound : Rat.Interval) (cut : Fraction.Rational)
    (inside : bound.Contains cut) : Rat.Interval :=
  ⟨bound.lower, cut, inside.1⟩

/-- Use the supplied contained cut as lower endpoint and keep the original upper endpoint. -/
@[expose] def cutRight (bound : Rat.Interval) (cut : Fraction.Rational)
    (inside : bound.Contains cut) : Rat.Interval :=
  ⟨cut, bound.upper, inside.2⟩

/-- A left cut at a contained rational refines the original interval. -/
theorem cutLeft_refines (bound : Rat.Interval) (cut : Fraction.Rational)
    (inside : bound.Contains cut) :
    Interval.Refines (bound.cutLeft cut inside) bound :=
  ⟨le_rfl, inside.2⟩

/-- A right cut at a contained rational refines the original interval. -/
theorem cutRight_refines (bound : Rat.Interval) (cut : Fraction.Rational)
    (inside : bound.Contains cut) :
    Interval.Refines (bound.cutRight cut inside) bound :=
  ⟨inside.1, le_rfl⟩

/-- The widths of the two intervals cut at one contained rational sum to the original width. -/
theorem cut_width_add (bound : Rat.Interval) (cut : Fraction.Rational)
    (inside : bound.Contains cut) :
    (bound.cutLeft cut inside).width +
      (bound.cutRight cut inside).width = bound.width := by
  dsimp only [Interval.cutLeft, Interval.cutRight, Interval.width]
  ring1

end

end Interval

end Purelib.Data.Rat

end

end

section
/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

public section

namespace Purelib.Data.Rat.Interval

open Purelib.Data in
open Purelib.Data.Rat in
/-- Construct the original rational interval from its supplied ordered endpoints. -/
@[expose] def quantileCutBound (lower upper : Fraction.Rational) (order : lower ≤ upper) :
    Rat.Interval :=
  ⟨lower, upper, order⟩
end Purelib.Data.Rat.Interval

end

section
public section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

namespace Purelib.Data.Rat.Interval

@[expose] public section

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- Retain the lower and upper endpoints of a closed rational interval with their order witness.

The validity field retains the proof that the lower endpoint is at most the upper endpoint. Closed containment includes
both endpoints; all constructions preserve this exact nominal carrier and its stored endpoint evidence. -/
structure Bounds where
  /-- The retained lower rational endpoint. -/ lower : Fraction.Rational
  /-- The retained upper rational endpoint. -/ upper : Fraction.Rational
  /-- Evidence that the lower endpoint is at most the upper endpoint. -/ valid : lower ≤ upper
deriving DecidableEq

constructive_injectivity Bounds

namespace Bounds

end Bounds
end

namespace Bounds

section
open Purelib.Data.Rat
/-- Require a rational value to lie between the retained lower and upper endpoints. -/
@[expose] def Contains (interval : Bounds) (x : Fraction.Rational) : Prop :=
  interval.lower ≤ x ∧ x ≤ interval.upper

/-- Require both endpoints of the inner nominal basic interval to lie within the outer endpoint bounds. -/
@[expose] def Refines (interval root : Bounds) : Prop :=
  root.lower ≤ interval.lower ∧ interval.upper ≤ root.upper

end

open Purelib.Data.Rat
/-- Decide containment using the two concrete rational endpoint comparisons. -/
instance containsDecidable (interval : Bounds) (x : Fraction.Rational) :
    Decidable (interval.Contains x) := by
  unfold Contains
  infer_instance

/-- Decide endpoint refinement using the concrete rational comparisons. -/
instance refinesDecidable (interval root : Bounds) :
    Decidable (interval.Refines root) := by
  unfold Refines
  infer_instance
end Bounds
end Purelib.Data.Rat.Interval

end

section

section
public section

/-!
# Whole-segment comparison of finite polynomial primitives

A uniform bound on the difference of two polynomial coefficients controls
their primitive increments.  Finite midpoint refinement eliminates the
Taylor remainder, so the final bound has no polynomial-degree-dependent
error floor.  Constant terms of either primitive are irrelevant.
-/

end

end
