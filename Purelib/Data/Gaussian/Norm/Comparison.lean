module
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Int.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Data.Rat.Fraction.Square
import Purelib.Data.Rat.Fraction.Order.Basic
public import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Squared norms from retained fraction reducedness

This computes the same exact rational norm as `normSq`.  Squaring the two
coordinates consumes their existing reducedness evidence instead of running
Euclid again on each numerator/denominator pair.  No rounding is involved.
-/

namespace Purelib.Data.Gaussian.Basic.Canonical.Norm.Comparison

open Purelib.Data.Rat.Fraction (RawFraction)

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Compute squared norm from the retained reduced rational coordinates.

Each coordinate square consumes its existing reducedness evidence, and their
exact rational sum retains the canonical scalar representation. -/
@[expose] def normSqFromReduced (source : Basic.Canonical) : Fraction.Rational :=
  Fraction.square source.re + Fraction.square source.im

/-- Reduced-coordinate squaring computes the canonical Gaussian squared norm.

The two exact scalar square identities identify the displayed sum with the
coordinate-product definition, without changing either retained coordinate. -/
@[simp] theorem normSqFromReduced_eq (source : Basic.Canonical) :
    normSqFromReduced source = Norm.Basic.normSq source := by
  unfold normSqFromReduced Norm.Basic.normSq
  rw [pow_two, pow_two, Fraction.square_eq_mul, Fraction.square_eq_mul]

/-- Compute an unreduced fraction for squared norm using two raw coordinate products and their raw sum.

Read both coordinate raw representatives once, multiply each by itself with referenceMulRaw, then combine them with
plainAddRaw. Equivalence relates this unreduced result to the canonical squared norm without changing its denominator
representation. -/
@[expose] def normSqRaw (source : Basic.Canonical) : RawFraction :=
  Fraction.plainAddRaw (Fraction.referenceMulRaw source.re source.re) (Fraction.referenceMulRaw source.im source.im)

/-- The canonical squared norm and the raw coordinate computation represent equivalent fractions. -/
theorem normSqRaw_equivalent (source : Basic.Canonical) :
    Fraction.Equivalent (Norm.Basic.normSq source).toRaw (normSqRaw source) := by
  simp only [Norm.Basic.normSq, pow_two]
  exact Fraction.equivalent_trans (Fraction.add_plain _ _)
    (Fraction.plainAddRaw_respects (Fraction.mul_equivalent source.re source.re) (Fraction.mul_equivalent source.im
      source.im))

end

open Purelib.Data in
open Purelib.Data.Rat in
/-- Positive equivalent representatives compare by the same cross products.

Equivalent numerator-denominator pairs give equal scaled products. Their
positive denominators permit cancellation in both directions of the comparison. -/
private theorem le_iff_raw (left right : Fraction.Rational) (leftRaw rightRaw : Fraction.RawFraction)
    (leftEqual : Fraction.Equivalent left.toRaw leftRaw) (rightEqual : Fraction.Equivalent right.toRaw rightRaw) :
    left ≤ right ↔ leftRaw.num * (rightRaw.den : Int) ≤ rightRaw.num * (leftRaw.den : Int) := by
  change left.num * (right.den : Int) ≤ right.num * (left.den : Int) ↔ _
  change left.num * (leftRaw.den : Int) = leftRaw.num * (left.den : Int) at leftEqual
  change right.num * (rightRaw.den : Int) = rightRaw.num * (right.den : Int) at rightEqual
  have leftProduct :
      (left.num * (right.den : Int)) * ((leftRaw.den : Int) * (rightRaw.den : Int)) =
        (leftRaw.num * (rightRaw.den : Int)) * ((left.den : Int) * (right.den : Int)) := by
    calc
      _ = (left.num * (leftRaw.den : Int)) * ((right.den : Int) * (rightRaw.den : Int)) := by ring1
      _ = _ := by rw [leftEqual]; ring1
  have rightProduct :
      (right.num * (left.den : Int)) * ((leftRaw.den : Int) * (rightRaw.den : Int)) =
        (rightRaw.num * (leftRaw.den : Int)) * ((left.den : Int) * (right.den : Int)) := by
    calc
      _ = (right.num * (rightRaw.den : Int)) * ((left.den : Int) * (leftRaw.den : Int)) := by ring1
      _ = _ := by rw [rightEqual]; ring1
  have canonicalPositive : 0 < (left.den : Int) * (right.den : Int) :=
    Int.Order.mul_pos (Int.Order.natCast_pos left.den_pos) (Int.Order.natCast_pos right.den_pos)
  have rawPositive : 0 < (leftRaw.den : Int) * (rightRaw.den : Int) :=
    Int.Order.mul_pos (Int.Order.natCast_pos leftRaw.den_pos) (Int.Order.natCast_pos rightRaw.den_pos)
  constructor
  · intro order
    apply Int.Order.int_le_of_mul_le_mul_right canonicalPositive
    rw [← leftProduct, ← rightProduct]
    exact Int.Order.mul_le_mul_of_nonneg_right order (Int.Order.le_of_lt rawPositive)
  · intro order
    apply Int.Order.int_le_of_mul_le_mul_right rawPositive
    rw [leftProduct, rightProduct]
    exact Int.Order.mul_le_mul_of_nonneg_right order (Int.Order.le_of_lt canonicalPositive)

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Decide whether Gaussian squared norm is at most a rational by comparing retained raw cross products.

Reuse the raw norm and rational representative to decide the integer cross-product comparison. Transport that decision
through the proved positive-denominator equivalence to the requested canonical rational inequality. -/
@[expose] def decidableNormSqLE (source : Basic.Canonical) (bound : Fraction.Rational) : Decidable
  (Norm.Basic.normSq source ≤ bound) :=
  let raw := normSqRaw source
  decidable_of_iff (raw.num * (bound.den : Int) ≤ bound.num * (raw.den : Int))
    (by exact (le_iff_raw (Norm.Basic.normSq source) bound raw bound.toRaw
      (normSqRaw_equivalent source) (Fraction.equivalent_refl _)).symm)

/-- Decide whether a rational is at most Gaussian squared norm using the retained raw squared-norm computation.

Keep the supplied rational representative and the computed raw norm, decide their integer cross products and transport
the result through the exact comparison equivalence. -/
@[expose] def decidableLENormSq (bound : Fraction.Rational) (source : Basic.Canonical) : Decidable (bound ≤
  Norm.Basic.normSq source) :=
  let raw := normSqRaw source
  decidable_of_iff (bound.num * (raw.den : Int) ≤ raw.num * (bound.den : Int))
    (by exact (le_iff_raw bound (Norm.Basic.normSq source) bound.toRaw raw
      (Fraction.equivalent_refl _) (normSqRaw_equivalent source)).symm)

/-- Decide strict squared-norm comparison from the reversed weak comparison.

The retained raw squared norm supplies the reversed weak decision. The exact
rational strict-order law transports its negation to the requested inequality. -/
@[expose] def decidableNormSqLT (source : Basic.Canonical) (bound : Fraction.Rational) : Decidable
  (Norm.Basic.normSq source < bound) := by
  letI := decidableLENormSq bound source
  exact decidable_of_iff (¬ bound ≤ Norm.Basic.normSq source) _root_.not_le

end

open Purelib.Data.Gaussian in
/-- Check the retained concrete squared-norm equality, weak-order and strict-order examples by kernel computation. -/
theorem comparison_regressions :
    @decide (Norm.Basic.normSq (⟨3, 4⟩ : Basic.Canonical) ≤ 25) (decidableNormSqLE ⟨3, 4⟩ 25) = true ∧
      @decide (25 ≤ Norm.Basic.normSq (⟨3, 4⟩ : Basic.Canonical)) (decidableLENormSq 25 ⟨3, 4⟩) = true ∧
      @decide (Norm.Basic.normSq (⟨3, 4⟩ : Basic.Canonical) < 25) (decidableNormSqLT ⟨3, 4⟩ 25) = false ∧
      @decide (Norm.Basic.normSq (0 : Basic.Canonical) ≤ -1) (decidableNormSqLE 0 (-1)) = false ∧
      @decide (Norm.Basic.normSq (0 : Basic.Canonical) < 1) (decidableNormSqLT 0 1) = true := by
  decide +kernel

end Purelib.Data.Gaussian.Basic.Canonical.Norm.Comparison

end
