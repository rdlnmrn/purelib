import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ConstructiveFraction

/-!
# Certified rational bounds

This module contains the interval arithmetic used by the finite measure
development.  A bound is displayed rational data with an order certificate.
It is not an interval in a completed line and does not denote a supremum,
infimum, or limit.
-/

namespace FiniteMeasure

abbrev Coordinate := RFAP.ConstructiveFraction.Rational

/-- A certified closed rational enclosure. -/
structure Bound where
  lower : Coordinate
  upper : Coordinate
  valid : lower ≤ upper

namespace Bound

@[ext] theorem ext {left right : Bound}
    (lower : left.lower = right.lower)
    (upper : left.upper = right.upper) : left = right := by
  cases left
  cases right
  simp_all

/-- Exact displayed rational data as a zero-width enclosure. -/
def exact (value : Coordinate) : Bound :=
  ⟨value, value, le_rfl⟩

/-- Width of a rational enclosure. -/
def width (bound : Bound) : Coordinate :=
  bound.upper - bound.lower

theorem width_nonneg (bound : Bound) : 0 ≤ bound.width :=
  sub_nonneg.mpr bound.valid

@[simp] theorem exact_width (value : Coordinate) :
    (exact value).width = 0 := by
  dsimp only [width, exact]
  ring1

/-- A displayed rational value is admitted by the enclosure. -/
def Contains (bound : Bound) (value : Coordinate) : Prop :=
  bound.lower ≤ value ∧ value ≤ bound.upper

instance containsDecidable (bound : Bound) (value : Coordinate) :
    Decidable (bound.Contains value) := by
  unfold Contains
  infer_instance

/-- A zero-width rational enclosure admits at most one displayed rational
value. -/
theorem eq_of_contains_of_contains_of_width_eq_zero
    {bound : Bound} {left right : Coordinate}
    (leftInside : bound.Contains left)
    (rightInside : bound.Contains right)
    (widthZero : bound.width = 0) : left = right := by
  have upperLeLower : bound.upper ≤ bound.lower := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    change bound.upper - bound.lower = 0 at widthZero
    calc
      0 ≤ -(bound.upper - bound.lower) := by
        rw [widthZero, neg_zero]
      _ = bound.lower - bound.upper := by ring1
  apply le_antisymm
  · exact leftInside.2.trans (upperLeLower.trans rightInside.1)
  · exact rightInside.2.trans (upperLeLower.trans leftInside.1)

@[simp] theorem exact_contains_iff (value candidate : Coordinate) :
    (exact value).Contains candidate ↔ candidate = value := by
  constructor
  · intro inside
    exact le_antisymm inside.2 inside.1
  · intro equal
    rw [equal]
    exact ⟨le_rfl, le_rfl⟩

/-- Addition of independently certified rational enclosures. -/
def add (left right : Bound) : Bound where
  lower := left.lower + right.lower
  upper := left.upper + right.upper
  valid := add_le_add left.valid right.valid

@[simp] theorem add_lower (left right : Bound) :
    (add left right).lower = left.lower + right.lower := rfl

@[simp] theorem add_upper (left right : Bound) :
    (add left right).upper = left.upper + right.upper := rfl

theorem add_width (left right : Bound) :
    (add left right).width = left.width + right.width := by
  dsimp only [width, add]
  ring1

theorem add_contains {left right : Bound} {x y : Coordinate}
    (leftInside : left.Contains x) (rightInside : right.Contains y) :
    (add left right).Contains (x + y) :=
  ⟨add_le_add leftInside.1 rightInside.1,
    add_le_add leftInside.2 rightInside.2⟩

/-- Additive inverse of a certified rational enclosure. -/
def neg (bound : Bound) : Bound where
  lower := -bound.upper
  upper := -bound.lower
  valid := RFAP.ConstructiveFraction.neg_le_neg_direct bound.valid

@[simp] theorem neg_lower (bound : Bound) :
    bound.neg.lower = -bound.upper := rfl

@[simp] theorem neg_upper (bound : Bound) :
    bound.neg.upper = -bound.lower := rfl

theorem neg_width (bound : Bound) : bound.neg.width = bound.width := by
  dsimp only [neg, width]
  ring1

theorem neg_contains {bound : Bound} {value : Coordinate}
    (inside : bound.Contains value) : bound.neg.Contains (-value) :=
  ⟨RFAP.ConstructiveFraction.neg_le_neg_direct inside.2,
    RFAP.ConstructiveFraction.neg_le_neg_direct inside.1⟩

@[simp] theorem neg_neg_bound (bound : Bound) : bound.neg.neg = bound := by
  apply Bound.ext <;> dsimp only [neg] <;> ring1

theorem neg_contains_iff {bound : Bound} {value : Coordinate} :
    bound.neg.Contains value ↔ bound.Contains (-value) := by
  constructor
  · intro inside
    have transported := neg_contains inside
    simpa only [neg_neg_bound] using transported
  · intro inside
    have transported := neg_contains inside
    have doubleNegation : -(-value) = value := by ring1
    rw [doubleNegation] at transported
    exact transported

/-- Difference of two independently certified rational enclosures. -/
def sub (left right : Bound) : Bound :=
  left.add right.neg

theorem sub_width (left right : Bound) :
    (left.sub right).width = left.width + right.width := by
  rw [sub, add_width, neg_width]

theorem sub_contains {left right : Bound} {x y : Coordinate}
    (leftInside : left.Contains x) (rightInside : right.Contains y) :
    (left.sub right).Contains (x - y) := by
  change (left.add right.neg).Contains (x + -y)
  exact add_contains leftInside (neg_contains rightInside)

/-- Multiplication of a bound by an explicitly nonnegative rational. -/
def scale (factor : Coordinate) (nonnegative : 0 ≤ factor)
    (bound : Bound) : Bound where
  lower := factor * bound.lower
  upper := factor * bound.upper
  valid := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    bound.valid nonnegative

theorem scale_width (factor : Coordinate) (nonnegative : 0 ≤ factor)
    (bound : Bound) :
    (scale factor nonnegative bound).width = factor * bound.width := by
  dsimp only [width, scale]
  ring1

theorem scale_contains {factor : Coordinate} (nonnegative : 0 ≤ factor)
    {bound : Bound} {value : Coordinate} (inside : bound.Contains value) :
    (scale factor nonnegative bound).Contains (factor * value) :=
  ⟨RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      inside.1 nonnegative,
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      inside.2 nonnegative⟩

/-- Refinement narrows both rational endpoints. -/
structure Refines (inner outer : Bound) : Prop where
  lower : outer.lower ≤ inner.lower
  upper : inner.upper ≤ outer.upper

namespace Refines

theorem refl (bound : Bound) : Refines bound bound :=
  ⟨le_rfl, le_rfl⟩

theorem trans {inner middle outer : Bound}
    (innerMiddle : Refines inner middle)
    (middleOuter : Refines middle outer) : Refines inner outer :=
  ⟨middleOuter.lower.trans innerMiddle.lower,
    innerMiddle.upper.trans middleOuter.upper⟩

theorem contains {inner outer : Bound} (refines : Refines inner outer)
    {value : Coordinate} (inside : inner.Contains value) :
    outer.Contains value :=
  ⟨refines.lower.trans inside.1, inside.2.trans refines.upper⟩

theorem width_le {inner outer : Bound} (refines : Refines inner outer) :
    inner.width ≤ outer.width :=
  RFAP.ConstructiveFraction.sub_le_sub_direct refines.upper refines.lower

theorem add {innerLeft outerLeft innerRight outerRight : Bound}
    (left : Refines innerLeft outerLeft)
    (right : Refines innerRight outerRight) :
    Refines (innerLeft.add innerRight) (outerLeft.add outerRight) :=
  ⟨add_le_add left.lower right.lower,
    add_le_add left.upper right.upper⟩

theorem neg {inner outer : Bound} (refines : Refines inner outer) :
    Refines inner.neg outer.neg :=
  ⟨RFAP.ConstructiveFraction.neg_le_neg_direct refines.upper,
    RFAP.ConstructiveFraction.neg_le_neg_direct refines.lower⟩

theorem sub {innerLeft outerLeft innerRight outerRight : Bound}
    (left : Refines innerLeft outerLeft)
    (right : Refines innerRight outerRight) :
    Refines (innerLeft.sub innerRight) (outerLeft.sub outerRight) :=
  left.add right.neg

theorem scale (factor : Coordinate) (nonnegative : 0 ≤ factor)
    {inner outer : Bound} (refines : Refines inner outer) :
    Refines (inner.scale factor nonnegative) (outer.scale factor nonnegative) :=
  ⟨RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      refines.lower nonnegative,
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      refines.upper nonnegative⟩

end Refines

/-- Two finite enclosures overlap arithmetically.  No intersection object is
formed. -/
def Overlaps (left right : Bound) : Prop :=
  left.lower ≤ right.upper ∧ right.lower ≤ left.upper

instance overlapsDecidable (left right : Bound) :
    Decidable (left.Overlaps right) := by
  unfold Overlaps
  infer_instance

theorem overlaps_of_common {left right : Bound} {value : Coordinate}
    (leftInside : left.Contains value) (rightInside : right.Contains value) :
    left.Overlaps right :=
  ⟨leftInside.1.trans rightInside.2,
    rightInside.1.trans leftInside.2⟩

/-- Explicit rational witness in the overlap of two rational enclosures. -/
def overlapWitness (left right : Bound) : Coordinate :=
  max left.lower right.lower

theorem overlapWitness_inside {left right : Bound}
    (overlaps : left.Overlaps right) :
    left.Contains (overlapWitness left right) ∧
      right.Contains (overlapWitness left right) :=
  ⟨⟨le_max_left _ _, max_le left.valid overlaps.2⟩,
    ⟨le_max_right _ _, max_le overlaps.1 right.valid⟩⟩

/-- Pairwise finite indistinguishability inside one enclosure, expressed
without absolute values. -/
theorem pairwise_difference_le {bound : Bound} {left right : Coordinate}
    (leftInside : bound.Contains left)
    (rightInside : bound.Contains right) :
    left - right ≤ bound.width ∧ right - left ≤ bound.width :=
  ⟨RFAP.ConstructiveFraction.sub_le_sub_direct leftInside.2 rightInside.1,
    RFAP.ConstructiveFraction.sub_le_sub_direct rightInside.2 leftInside.1⟩

/-- Canonical rational representative of one finite enclosure.  Choosing the
displayed lower endpoint requires no selection principle. -/
def sample (bound : Bound) : Coordinate :=
  bound.lower

theorem sample_contains (bound : Bound) : bound.Contains bound.sample :=
  ⟨le_rfl, bound.valid⟩

/-- Every explicitly admitted rational is within the displayed width of the
canonical rational representative, in both directed differences. -/
theorem sample_difference_le {bound : Bound} {value : Coordinate}
    (inside : bound.Contains value) :
    value - bound.sample ≤ bound.width ∧
      bound.sample - value ≤ bound.width :=
  pairwise_difference_le inside bound.sample_contains

/-! ## Exact finite interval cuts -/

/-- Left child of a displayed rational interval cut. -/
def cutLeft (bound : Bound) (cut : Coordinate)
    (inside : bound.Contains cut) : Bound :=
  ⟨bound.lower, cut, inside.1⟩

/-- Right child of a displayed rational interval cut. -/
def cutRight (bound : Bound) (cut : Coordinate)
    (inside : bound.Contains cut) : Bound :=
  ⟨cut, bound.upper, inside.2⟩

theorem cutLeft_refines (bound : Bound) (cut : Coordinate)
    (inside : bound.Contains cut) :
    Refines (bound.cutLeft cut inside) bound :=
  ⟨le_rfl, inside.2⟩

theorem cutRight_refines (bound : Bound) (cut : Coordinate)
    (inside : bound.Contains cut) :
    Refines (bound.cutRight cut inside) bound :=
  ⟨inside.1, le_rfl⟩

/-- Exact finite additivity of rational interval length across one displayed
cut. -/
theorem cut_width_add (bound : Bound) (cut : Coordinate)
    (inside : bound.Contains cut) :
    (bound.cutLeft cut inside).width +
      (bound.cutRight cut inside).width = bound.width := by
  dsimp only [cutLeft, cutRight, width]
  ring1

end Bound

end FiniteMeasure
