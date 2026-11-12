module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field

import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section

open Purelib.Data.Rat.Fraction.Order
@[expose] public section

/-! Finite affine segments between two points of a rational rectangle. -/

namespace Purelib.Geometry.Rational.Box

open Purelib.Data.Rat in
/-- A convex combination of two contained rationals remains between the same retained endpoints. -/
public theorem coordinate_between {lower upper first last
  parameter : Fraction.Rational}
    (firstInside : lower ≤ first ∧ first ≤ upper) (lastInside : lower ≤ last ∧ last ≤ upper)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    lower ≤ first + parameter * (last - first) ∧ first + parameter * (last - first) ≤ upper := by
  have complement := Arithmetic.sub_nonneg_direct inside.2
  constructor
  · calc
      _ = (1 - parameter) * lower + parameter * lower := by ring1
      _ ≤ (1 - parameter) * first + parameter * last := add_le_add
        (Arithmetic.mul_le_mul_of_nonneg_left_direct firstInside.1 complement)
        (Arithmetic.mul_le_mul_of_nonneg_left_direct lastInside.1 inside.1)
      _ = _ := by ring1
  · calc
      _ = (1 - parameter) * first + parameter * last := by ring1
      _ ≤ (1 - parameter) * upper + parameter * upper := add_le_add
        (Arithmetic.mul_le_mul_of_nonneg_left_direct firstInside.2 complement)
        (Arithmetic.mul_le_mul_of_nonneg_left_direct lastInside.2 inside.1)
      _ = _ := by ring1

end Purelib.Geometry.Rational.Box

end

public section

namespace Purelib.Data.Rat.Interval.ConvexCombination

open Purelib.Data.Rat

/-- A rational lies between two displayed endpoints exactly when one of their two directed intervals contains it.

The minimum and maximum retain both orientations, including equal
endpoints. Each directed pair gives the same closed containment bounds.
-/
theorem between_endpoints_iff (first last value : Fraction.Rational) :
    (min first last ≤ value ∧ value ≤ max first last) ↔
      (first ≤ value ∧ value ≤ last) ∨ (last ≤ value ∧ value ≤ first) := by
  constructor
  · intro inside
    cases Fraction.Order.Basic.le_total first last with
    | inl forward =>
        exact Or.inl ⟨(Fraction.Order.Basic.min_eq_left forward) ▸ inside.1,
          (Fraction.Order.Basic.max_eq_right forward) ▸ inside.2⟩
    | inr reverse =>
        exact Or.inr ⟨(Fraction.Order.Basic.min_eq_right reverse) ▸ inside.1,
          (Fraction.Order.Basic.max_eq_left reverse) ▸ inside.2⟩
  · intro directed
    cases directed with
    | inl forward =>
        exact ⟨(Fraction.Order.Basic.min_le_left _ _).trans forward.1,
          forward.2.trans (Fraction.Order.Basic.le_max_right _ _)⟩
    | inr reverse =>
        exact ⟨(Fraction.Order.Basic.min_le_right _ _).trans reverse.1,
          reverse.2.trans (Fraction.Order.Basic.le_max_left _ _)⟩

/-- Compute the affine parameter of a rational between two displayed endpoints.

The orientation branch makes the denominator nonnegative. A stationary pair
uses the rational carrier's total zero division and yields parameter zero. -/
@[expose] def segmentParameter (first last value : Fraction.Rational) : Fraction.Rational :=
  if first ≤ last then (value - first) / (last - first)
  else (first - value) / (first - last)

/-- Segment normalization preserves every rational affine combination in either orientation.

The denominator is fixed by the original endpoints. Rewriting its total
division as multiplication by the same reciprocal proves the identity even
when those endpoints coincide, without any interval or nonzero assumption.
-/
theorem segmentParameter_affine (first last lower upper input : Fraction.Rational) :
    segmentParameter first last lower +
        input * (segmentParameter first last upper - segmentParameter first last lower) =
      segmentParameter first last (lower + input * (upper - lower)) := by
  by_cases forward : first ≤ last
  · simp only [segmentParameter, if_pos forward, Fraction.Field.div_eq_mul_inv_direct]
    ring1
  · simp only [segmentParameter, if_neg forward, Fraction.Field.div_eq_mul_inv_direct]
    ring1

/-- The computed affine parameter lies in the unit interval for every value between the endpoints.

Both orientations use a positive denominator unless the endpoints coincide;
in that stationary case the contained value is the same endpoint. -/
theorem segmentParameter_bounds (first last value : Fraction.Rational)
    (inside : min first last ≤ value ∧ value ≤ max first last) :
    0 ≤ segmentParameter first last value ∧ segmentParameter first last value ≤ 1 := by
  unfold segmentParameter
  by_cases forward : first ≤ last
  · rw [if_pos forward]
    have lower : first ≤ value := (Fraction.Order.Basic.min_eq_left forward) ▸ inside.1
    have upper : value ≤ last := (Fraction.Order.Basic.max_eq_right forward) ▸ inside.2
    by_cases stationary : first = last
    · have valueEqual : value = first :=
        Fraction.Order.Basic.le_antisymm _ _ (upper.trans_eq stationary.symm) lower
      rw [valueEqual, stationary]
      rw [show last - last = (0 : Fraction.Rational) by ring1, Fraction.Field.div_zero_direct]
      change 0 ≤ (0 : Fraction.Rational) ∧ (0 : Fraction.Rational) ≤ 1
      exact ⟨le_rfl, by decide⟩
    · have strict : first < last :=
        ⟨forward, fun reverse => stationary (Fraction.Order.Basic.le_antisymm _ _ forward reverse)⟩
      have positive := Arithmetic.sub_pos_direct strict
      constructor
      · exact Fraction.Order.Field.div_nonneg_direct
          (Arithmetic.sub_nonneg_direct lower) positive.le
      · apply (Fraction.Order.Field.div_le_iff_pos positive).mpr
        rw [Fraction.Field.one_mul]
        exact Arithmetic.sub_le_sub_direct upper le_rfl
  · rw [if_neg forward]
    have strict : last < first := Arithmetic.lt_of_not_ge_direct forward
    have lower : last ≤ value := (Fraction.Order.Basic.min_eq_right strict.le) ▸ inside.1
    have upper : value ≤ first := (Fraction.Order.Basic.max_eq_left strict.le) ▸ inside.2
    have positive := Arithmetic.sub_pos_direct strict
    constructor
    · exact Fraction.Order.Field.div_nonneg_direct
        (Arithmetic.sub_nonneg_direct upper) positive.le
    · apply (Fraction.Order.Field.div_le_iff_pos positive).mpr
      rw [Fraction.Field.one_mul]
      exact Arithmetic.sub_le_sub_direct le_rfl lower

/-- Interpolation at the computed unit parameter recovers the original contained rational.

The cancellation uses the original endpoint difference in either orientation.
Equal endpoints are handled directly, without dividing by a nonzero witness. -/
theorem segmentParameter_interpolates (first last value : Fraction.Rational)
    (inside : min first last ≤ value ∧ value ≤ max first last) :
    first + segmentParameter first last value * (last - first) = value := by
  unfold segmentParameter
  by_cases forward : first ≤ last
  · rw [if_pos forward]
    by_cases stationary : first = last
    · have lower : first ≤ value := (Fraction.Order.Basic.min_eq_left forward) ▸ inside.1
      have upper : value ≤ first :=
        ((Fraction.Order.Basic.max_eq_right forward) ▸ inside.2).trans_eq stationary.symm
      have valueEqual := Fraction.Order.Basic.le_antisymm _ _ upper lower
      rw [valueEqual, stationary]
      ring1
    · have strict : first < last :=
        ⟨forward, fun reverse => stationary (Fraction.Order.Basic.le_antisymm _ _ forward reverse)⟩
      rw [Fraction.Field.div_mul_cancel_of_ne _ _
        (Arithmetic.sub_pos_direct strict).ne']
      ring1
  · rw [if_neg forward]
    have strict : last < first := Arithmetic.lt_of_not_ge_direct forward
    have cancelled := Fraction.Field.div_mul_cancel_of_ne (first - value) (first - last)
      (Arithmetic.sub_pos_direct strict).ne'
    calc
      first + (first - value) / (first - last) * (last - first) =
          first - (first - value) / (first - last) * (first - last) := by ring1
      _ = first - (first - value) := by rw [cancelled]
      _ = value := by ring1

/-- Two parameters giving the same affine reading coincide when the original endpoints differ.

Subtracting the original first endpoint identifies their products with the
same nonzero endpoint difference. Direct rational cancellation preserves
the original parameters without any interval or orientation assumptions. -/
theorem parameter_eq_of_interpolation {first last left right : Fraction.Rational}
    (nonstationary : first ≠ last)
    (same : first + left * (last - first) = first + right * (last - first)) : left = right := by
  have differenceNonzero : last - first ≠ 0 := by
    intro zero
    apply nonstationary
    calc
      first = first + 0 := by ring1
      _ = first + (last - first) := congrArg (fun value => first + value) zero.symm
      _ = last := by ring1
  apply Fraction.Field.mul_right_cancel_of_ne differenceNonzero
  calc
    left * (last - first) = (first + left * (last - first)) - first := by ring1
    _ = (first + right * (last - first)) - first := congrArg (fun value => value - first) same
    _ = right * (last - first) := by ring1

/-- Two strictly ordered affine parameters preserve exactly the displayed endpoint direction.

Equal endpoint readings remain stationary. Reverse endpoints give a
strict reverse comparison, so no direction is inferred from coordinates.
-/
theorem interpolation_order (first last lower upper : Fraction.Rational) (ordered : lower < upper) :
    first + lower * (last - first) ≤ first + upper * (last - first) ↔ first ≤ last := by
  constructor
  · intro retained
    by_cases forward : first ≤ last
    · exact forward
    · have reverse : last < first := Arithmetic.lt_of_not_ge_direct forward
      have positive := Arithmetic.mul_pos_of_neg_of_neg_direct
        (Arithmetic.sub_neg_direct ordered) (Arithmetic.sub_neg_direct reverse)
      have actual : 0 < (first + lower * (last - first)) - (first + upper * (last - first)) :=
        (show (lower - upper) * (last - first) =
          (first + lower * (last - first)) - (first + upper * (last - first)) by ring1) ▸ positive
      exact ((Arithmetic.lt_of_sub_pos_direct actual).2 retained).elim
  · intro forward
    have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct ordered.1
      (Arithmetic.sub_nonneg_direct forward)
    have shifted := Arithmetic.add_le_add_right_direct scaled first
    have firstEq : lower * (last - first) + first = first + lower * (last - first) := by ring1
    have lastEq : upper * (last - first) + first = first + upper * (last - first) := by ring1
    rewrite [firstEq, lastEq] at shifted
    exact shifted

end Purelib.Data.Rat.Interval.ConvexCombination
