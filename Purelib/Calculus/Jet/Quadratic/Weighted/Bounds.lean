module

public import Purelib.Calculus.Jet.Quadratic.Weighted
public import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Uniform remainder ceilings for original finite weighted Taylor banks

The actual finite weights and cached entry factors retain their existing
weighted certificate. Pointwise weight and factor ceilings bound that exact
factor. For dyadic chart weights the original cell count cancels their
quarter-radius quadrance, giving a ceiling independent of refinement depth.
-/

public section

namespace Purelib.Calculus.Jet.Quadratic.Basic.Certificate

open Purelib
open Purelib.Algebra
open Purelib.Approximation.Rational
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

variable {count : Nat} {increment : Canonical}

/-- Pointwise original weight and entry-factor ceilings bound the retained weighted certificate's exact factor. -/
theorem weightedFactor_le (weights : Data.Vector Canonical count)
    (entries : Data.Vector (Certificate increment) count) (weightCeiling factorCeiling : Fraction.Rational)
    (factorNonnegative : 0 ≤ factorCeiling)
    (weightBound : ∀ index, Norm.Basic.normSq (weights index) ≤ weightCeiling)
    (factorBound : ∀ index, (entries index).factor ≤ factorCeiling) :
    weightedFactor weights entries ≤
      (count : Fraction.Rational) * ((count : Fraction.Rational) * (weightCeiling * factorCeiling)) := by
  have entryBound (index : Fin count) :
      Norm.Basic.normSq (weights index) * (entries index).factor ≤ weightCeiling * factorCeiling :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (factorBound index)
      (Norm.Basic.normSq_nonneg _)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (weightBound index) factorNonnegative)
  have total := FiniteSum.Rational.Order.IndexedBudget.sumFin_le entryBound
  rewrite [FiniteSum.Fin.Rational.sum_constant] at total
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct total
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count))

/-- The original dyadic count cancels weight quadrance and gives a depth-independent weighted factor ceiling. -/
theorem dyadic_weightedFactor_le (weights : Data.Vector Canonical count)
    (entries : Data.Vector (Certificate increment) count) (depth : Nat) (count_eq : count = 2 ^ depth)
    (weightScale factorCeiling : Fraction.Rational) (factorNonnegative : 0 ≤ factorCeiling)
    (weightBound : ∀ index, Norm.Basic.normSq (weights index) ≤ Geometric.Basic.quarterRadius weightScale depth)
    (factorBound : ∀ index, (entries index).factor ≤ factorCeiling) :
    weightedFactor weights entries ≤ weightScale * factorCeiling := by
  have bound := weightedFactor_le weights entries (Geometric.Basic.quarterRadius weightScale depth)
    factorCeiling factorNonnegative weightBound factorBound
  apply bound.trans_eq
  calc
    _ = ((count : Fraction.Rational) *
        ((count : Fraction.Rational) * Geometric.Basic.quarterRadius weightScale depth)) * factorCeiling := by ring1
    _ = _ := by
      rewrite [count_eq, Geometric.DyadicCount.dyadic_count_cancel]
      rfl

/-- Original dyadic weighted samples obey a common fourth-order Taylor bound independent of the finite mesh depth. -/
theorem dyadic_weighted_remainder_le (weights : Data.Vector Canonical count)
    (entries : Data.Vector (Certificate increment) count) (depth : Nat) (count_eq : count = 2 ^ depth)
    (weightScale factorCeiling : Fraction.Rational) (factorNonnegative : 0 ≤ factorCeiling)
    (weightBound : ∀ index, Norm.Basic.normSq (weights index) ≤ Geometric.Basic.quarterRadius weightScale depth)
    (factorBound : ∀ index, (entries index).factor ≤ factorCeiling) :
    Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun index => weights index * (entries index).remainder)) ≤
      weightScale * factorCeiling * Norm.Basic.normSq increment ^ 2 :=
  (weighted_remainder_le weights entries).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (dyadic_weightedFactor_le weights entries depth count_eq weightScale factorCeiling factorNonnegative
        weightBound factorBound) (Fraction.Order.Arithmetic.sq_nonneg_direct _))

end Purelib.Calculus.Jet.Quadratic.Basic.Certificate
