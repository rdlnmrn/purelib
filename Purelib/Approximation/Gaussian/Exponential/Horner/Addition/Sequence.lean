module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Approximation.Gaussian.Exponential.Horner.Taylor
import Purelib.Approximation.Gaussian.Exponential.Taylor.Cauchy.Bounds
public import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Multiplication
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
public section

/-! Approximation Gaussian Exponential Horner Addition Sequence and its finite structural certificates. -/

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Addition.Sequence

open Purelib
open Purelib.Approximation.Gaussian.Exponential.Horner
open Purelib.Approximation.Gaussian.Exponential.Taylor
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-! Approximation Gaussian Exponential Horner Addition Sequence and its finite structural certificates. -/

/-- Multiply the two finite exponential Horner samples at the same index. -/
@[expose] public def expProductSample (x y : Data.Gaussian.Basic.Canonical) (index : Nat) :
  Data.Gaussian.Basic.Canonical :=
  Sample.sample x index *
    Sample.sample y index

/-- The rational scale 400 for the geometric squared-error bound of the sampled exponential product. -/
@[expose] public def expProductErrorScale : Fraction.Rational := 40 * 10

/-- The exponential product error scale is nonnegative. -/
theorem expProductErrorScale_nonneg : 0 ≤
  Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductErrorScale :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 40) (by decide)).le
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 10) (by decide)).le

/-- The rational uniform squared-norm bound 100 for products of unit-disk exponential samples. -/
@[expose] public def expProductCenterBound : Fraction.Rational := 10 * 10

/-- The exponential product center bound is nonnegative. -/
theorem expProductCenterBound_nonneg : 0 ≤
  Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductCenterBound :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 10) (by decide)).le
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 10) (by decide)).le

/-- Products of exponential samples at unit-disk inputs satisfy the retained uniform squared-norm bound. -/
theorem expProductSample_bounded {x y : Data.Gaussian.Basic.Canonical}
    (xUnit : Data.Gaussian.Norm.Basic.normSq x ≤ 1) (yUnit : Data.Gaussian.Norm.Basic.normSq y ≤ 1)
      (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      (Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductSample x y index) ≤
      Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductCenterBound := by
  rw [Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductSample, Data.Gaussian.Norm.Basic.normSq_mul]
  have multiplied := Fraction.Order.Arithmetic.mul_le_mul_direct
    (Sample.sample_bounded x xUnit index)
    (Sample.sample_bounded y yUnit index)
    (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide : (0 : Fraction.Rational) ≤ 10)
  calc
    Data.Gaussian.Norm.Basic.normSq (Sample.sample x index) *
        Data.Gaussian.Norm.Basic.normSq (Sample.sample y index) ≤ 10 * 10 :=
      multiplied
    _ = Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductCenterBound := rfl

/-- Later equal-index exponential products remain within the geometric squared-error radius of the earlier index. -/
theorem expProductSample_later_close {x y : Data.Gaussian.Basic.Canonical}
    (xUnit : Data.Gaussian.Norm.Basic.normSq x ≤ 1) (yUnit : Data.Gaussian.Norm.Basic.normSq y ≤ 1)
    {earlier later : Nat} (order : earlier ≤ later) :
    Data.Gaussian.Norm.Basic.normSq
      (Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductSample x y later -
      Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductSample x y earlier) ≤
      Geometric.Basic.quarterRadius
        Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductErrorScale earlier := by
  rw [Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductSample,
    Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductSample,
    Multiplication.product_difference_identity]
  let radius :=
    Geometric.Basic.quarterRadius 10 earlier
  have xClose := Sample.sample_later_close x xUnit order
  have yClose := Sample.sample_later_close y yUnit order
  have yLaterBound := Sample.sample_bounded y yUnit later
  have xEarlierBound := Sample.sample_bounded x xUnit earlier
  have firstBound :
      Data.Gaussian.Norm.Basic.normSq
          ((Sample.sample x later -
              Sample.sample x earlier) *
            Sample.sample y later) ≤ radius * 10 := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct xClose yLaterBound
      (Data.Gaussian.Norm.Basic.normSq_nonneg _) (Geometric.Basic.quarterRadius_nonneg
        (by decide) _)
  have secondBound :
      Data.Gaussian.Norm.Basic.normSq
          (Sample.sample x earlier *
            (Sample.sample y later -
              Sample.sample y earlier)) ≤ 10 * radius := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct xEarlierBound yClose
      (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      (by decide : (0 : Fraction.Rational) ≤ 10)
  calc
    Data.Gaussian.Norm.Basic.normSq
        ((Sample.sample x later -
              Sample.sample x earlier) *
            Sample.sample y later +
          Sample.sample x earlier *
            (Sample.sample y later -
              Sample.sample y earlier)) ≤
      2 * (radius * 10 + 10 * radius) := by
        exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (add_le_add firstBound secondBound) (by decide))
    _ = Geometric.Basic.quarterRadius
        Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductErrorScale earlier := by
      dsimp only [radius]
      rw [Geometric.Basic.quarterRadius_eq_mul_pow,
        Geometric.Basic.quarterRadius_eq_mul_pow]
      dsimp only [Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductErrorScale]
      ring1

/-- The pointwise product of the two finite exponential programs, equipped with an explicit finite tail sidecar. -/
@[expose] public def expProductApproximation (x y : Data.Gaussian.Basic.Canonical)
    (xUnit : Data.Gaussian.Norm.Basic.normSq x ≤ 1) (yUnit : Data.Gaussian.Norm.Basic.normSq y ≤ 1) :
      ApproximationData where
  sample := Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductSample x y
  radiusSq := Geometric.Basic.quarterRadius
    Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductErrorScale
  radiusSq_nonneg :=
    Geometric.Basic.quarterRadius_nonneg
      Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductErrorScale_nonneg
  later_close := Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductSample_later_close xUnit yUnit
  refineIndex current target _ :=
    Search.firstQuarterBelow
      Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductErrorScale current target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge
      Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductErrorScale current target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate
      Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductErrorScale
        Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductErrorScale_nonneg
  centerBound := Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductCenterBound
  centerBound_nonneg := Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductCenterBound_nonneg
  sample_bounded := Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductSample_bounded xUnit yUnit

/-- At an odd sample index, the product and sum-input exponential samples differ by at most the displayed geometric
squared-error bound.

Both original Gaussian inputs must lie in the unit disk; the estimate uses their finite Cauchy-product identity. -/
theorem expProductSample_addition_error_odd {x y : Data.Gaussian.Basic.Canonical}
    (xUnit : Data.Gaussian.Norm.Basic.normSq x ≤ 1) (yUnit : Data.Gaussian.Norm.Basic.normSq y ≤ 1)
      (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        (Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductSample x y (2 * index + 1) -
          Sample.sample (x + y) (2 * index + 1)) ≤
      Geometric.Basic.quarterRadius 16 index := by
  rw [Approximation.Gaussian.Exponential.Horner.Addition.Sequence.expProductSample,
    Taylor.sample_eq_truncatedExp, Taylor.sample_eq_truncatedExp,
    Taylor.sample_eq_truncatedExp]
  simpa only [show 2 * index + 1 + 1 = 2 * index + 2 by rfl] using
    Cauchy.Bounds.truncatedExp_addition_error_even xUnit yUnit index
end Purelib.Approximation.Gaussian.Exponential.Horner.Addition.Sequence

end
