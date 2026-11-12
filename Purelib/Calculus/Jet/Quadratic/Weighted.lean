module

public import Purelib.Calculus.Jet.Quadratic.Basic
public import Purelib.Data.Vector.Basic
public import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Weighted finite Taylor certificates

One retained finite weight vector multiplies the original base, output,
slope and remainder entries at the same increment. The finite quadrance
sum estimate computes a remainder factor from their individual factors.
The constructor needs no conclusion about the weighted sample.
-/

public section

namespace Purelib.Calculus.Jet.Quadratic.Basic.Certificate

open Purelib.Algebra
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

variable {count : Nat} {increment : Canonical}

/-- The computed remainder factor of the original finite weighted certificate entries. -/
@[expose] def weightedFactor (weights : Data.Vector Canonical count)
    (entries : Data.Vector (Certificate increment) count) : Fraction.Rational :=
  (count : Fraction.Rational) *
    FiniteSum.Fin.sumFin (fun index => Norm.Basic.normSq (weights index) * (entries index).factor)

/-- The finite factor is nonnegative, including empty families and zero or signed Gaussian weights. -/
theorem weightedFactor_nonnegative (weights : Data.Vector Canonical count)
    (entries : Data.Vector (Certificate increment) count) : 0 ≤ weightedFactor weights entries :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count))
    (FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun index =>
      Fraction.Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg (weights index))
        (entries index).factor_nonneg))

/-- Weighted finite summation preserves the exact original Taylor expansions at the common increment. -/
theorem weighted_expansion (weights : Data.Vector Canonical count)
    (entries : Data.Vector (Certificate increment) count) :
    FiniteSum.Fin.sumFin (fun index => weights index * (entries index).output) -
        FiniteSum.Fin.sumFin (fun index => weights index * (entries index).base) -
        increment * FiniteSum.Fin.sumFin (fun index => weights index * (entries index).slope) =
      FiniteSum.Fin.sumFin (fun index => weights index * (entries index).remainder) := by
  calc
    _ = FiniteSum.Fin.sumFin (fun index =>
        (weights index * (entries index).output - weights index * (entries index).base) -
          increment * (weights index * (entries index).slope)) := by
      rewrite [FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_mul_left]
      rfl
    _ = _ := FiniteSum.Fin.sumFin_congr (fun index => by
      rewrite [← (entries index).expansion]
      ring1)

/-- The original weighted remainder sum has a quantified fourth-order bound computed from every entry factor.

Finite Cauchy bounds its quadrance by the count times the sum of individual
quadrances. Each original certificate pays its own remainder after the
identical retained Gaussian weight multiplies it.
-/
theorem weighted_remainder_le (weights : Data.Vector Canonical count)
    (entries : Data.Vector (Certificate increment) count) :
    Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun index => weights index * (entries index).remainder)) ≤
      weightedFactor weights entries * Norm.Basic.normSq increment ^ 2 := by
  have entryBound (index : Fin count) :
      Norm.Basic.normSq (weights index * (entries index).remainder) ≤
        (Norm.Basic.normSq (weights index) * (entries index).factor) * Norm.Basic.normSq increment ^ 2 := by
    have bound := (entries index).remainder_le
    rewrite [← Norm.Basic.normSq_eq_canonical, ← Norm.Basic.normSq_eq_canonical] at bound
    rewrite [Norm.Basic.normSq_mul]
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bound
      (Norm.Basic.normSq_nonneg (weights index))).trans_eq (by ring1)
  have estimate := Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin
    (fun index => weights index * (entries index).remainder)
    (fun index => (Norm.Basic.normSq (weights index) * (entries index).factor) *
      Norm.Basic.normSq increment ^ 2) entryBound
  exact estimate.trans_eq (by
    rewrite [FiniteSum.Fin.sumFin_mul_right]
    unfold weightedFactor
    ring1)

/-- Construct the weighted certificate from the identical retained finite weights and original entries.

Every displayed Gaussian field is its original ordered finite weighted sum.
The factor and mathematical expansion and remainder bounds are constructed
internally, with no replacement entry or requested final inequality.
-/
@[expose] def weightedSum (weights : Data.Vector Canonical count)
    (entries : Data.Vector (Certificate increment) count) : Certificate increment where
  base := FiniteSum.Fin.sumFin (fun index => weights index * (entries index).base)
  output := FiniteSum.Fin.sumFin (fun index => weights index * (entries index).output)
  slope := FiniteSum.Fin.sumFin (fun index => weights index * (entries index).slope)
  remainder := FiniteSum.Fin.sumFin (fun index => weights index * (entries index).remainder)
  expansion := weighted_expansion weights entries
  factor := weightedFactor weights entries
  factor_nonneg := weightedFactor_nonnegative weights entries
  remainder_le := by
    rewrite [← Norm.Basic.normSq_eq_canonical, ← Norm.Basic.normSq_eq_canonical]
    exact weighted_remainder_le weights entries

/-- The weighted certificate base is the sum of the same original weighted base entries. -/
theorem weightedSum_base (weights : Data.Vector Canonical count)
    (entries : Data.Vector (Certificate increment) count) :
    (weightedSum weights entries).base = FiniteSum.Fin.sumFin (fun index => weights index * (entries index).base) := rfl

/-- The weighted output is the sum of the identical original weighted outputs. -/
theorem weightedSum_output (weights : Data.Vector Canonical count)
    (entries : Data.Vector (Certificate increment) count) :
    (weightedSum weights entries).output =
      FiniteSum.Fin.sumFin (fun index => weights index * (entries index).output) := rfl

/-- The weighted slope is the sum of the same original weighted derivative entries. -/
theorem weightedSum_slope (weights : Data.Vector Canonical count)
    (entries : Data.Vector (Certificate increment) count) :
    (weightedSum weights entries).slope =
      FiniteSum.Fin.sumFin (fun index => weights index * (entries index).slope) := rfl

/-- The weighted remainder is the sum of the retained original weighted remainders. -/
theorem weightedSum_remainder (weights : Data.Vector Canonical count)
    (entries : Data.Vector (Certificate increment) count) :
    (weightedSum weights entries).remainder =
      FiniteSum.Fin.sumFin (fun index => weights index * (entries index).remainder) := rfl

/-- The constructed weighted certificate retains the computed finite quadrance factor. -/
theorem weightedSum_factor (weights : Data.Vector Canonical count)
    (entries : Data.Vector (Certificate increment) count) :
    (weightedSum weights entries).factor = weightedFactor weights entries := rfl

end Purelib.Calculus.Jet.Quadratic.Basic.Certificate
