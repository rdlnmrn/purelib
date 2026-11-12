module

public import Purelib.Algebra.Ring.GaussianReading
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Weight
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Paid discrepancies for original additive finite readings

The same original ordered finite sum is read additively. A finite table of
source-fixed error coefficients bounds its discrepancy from a displayed
Gaussian sum, without assuming multiplicative preservation.
-/

public section

namespace Purelib.Algebra.Ring.GaussianReading

open Purelib.Algebra.FiniteSum.Fin
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order

variable {K : Type*} [CommRing K] {weight : Weight K} {scalar : Canonical → K}

/-- Pointwise paid errors bound the reading of the same actual formal finite sum.

Each coefficient belongs to its original summand. Exact additivity and the
original finite squared-triangle estimate retain the complete ordered sum;
no equality between a reading of a product and a product of readings is used.
-/
theorem sum_discrepancy_bound (reading : GaussianReading weight scalar) {count : Nat}
    (original : Fin count → K) (model : Fin count → Canonical) (coefficients : Fin count → Rational)
    (bounded : ∀ index, Norm.Basic.normSq (reading.read (original index) - model index) ≤
      reading.error * coefficients index) :
    Norm.Basic.normSq (reading.read (sumFin original) - sumFin model) ≤
      reading.error * ((2 : Rational) ^ count * sumFin coefficients) := by
  rewrite [map_sumFin reading.read reading.mapZero reading.mapAdd, ← sumFin_sub]
  have bound := Norm.normSq_sumFin_le (fun index => reading.read (original index) - model index)
    (fun index => reading.error * coefficients index) bounded
  rewrite [sumFin_mul_left] at bound
  exact bound.trans_eq (by ring1)

end Purelib.Algebra.Ring.GaussianReading

end
