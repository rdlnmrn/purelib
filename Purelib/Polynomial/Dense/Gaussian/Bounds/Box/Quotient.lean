module

public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Norm.Quotient
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Cached finite polynomial quotient bounds on a rational box

The actual numerator and denominator Horner folds are retained together
with their original polynomial and box indices. A supplied positive floor
at two displayed denominator values pays the finite quotient estimate;
no whole-box denominator clearance is asserted.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Box

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-- The actual original Horner value/slope table retained at its polynomial and box indices. -/
public abbrev HornerCache (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (B : Box) :=
  { cache : Bounds.Horner // cache = denseHornerNormBounds p B }

/-- The finite quotient sensitivity read from both actual original Horner caches and a positive denominator floor.

The two supplied tables retain their original polynomial and box parents.
Their value and slope fields are consumed directly; neither coefficient
fold is repeated while comparing contained points.
-/
@[expose] public def quotientLipschitzBound
    (numerator denominator : Basic.CanonicalCoefficients.CoefficientPolynomial) (B : Box)
    (lower : Fraction.Rational)
    (numeratorCache : HornerCache numerator B := ⟨denseHornerNormBounds numerator B, rfl⟩)
    (denominatorCache : HornerCache denominator B := ⟨denseHornerNormBounds denominator B, rfl⟩) :
    Fraction.Rational :=
  (2 * (numeratorCache.val.slope * denominatorCache.val.value +
    numeratorCache.val.value * denominatorCache.val.slope)) / (lower * lower)

/-- Both retained Horner tables and a positive denominator floor give a nonnegative finite quotient sensitivity. -/
public theorem quotientLipschitzBound_nonnegative
    (numerator denominator : Basic.CanonicalCoefficients.CoefficientPolynomial) (B : Box)
    (lower : Fraction.Rational) (positive : 0 < lower)
    (numeratorCache : HornerCache numerator B) (denominatorCache : HornerCache denominator B) :
    0 ≤ quotientLipschitzBound numerator denominator B lower numeratorCache denominatorCache := by
  have first := denseHornerNormBounds_nonneg numerator B
  have second := denseHornerNormBounds_nonneg denominator B
  change 0 ≤ (denseHornerNormBounds numerator B).value ∧
    0 ≤ (denseHornerNormBounds numerator B).slope at first
  change 0 ≤ (denseHornerNormBounds denominator B).value ∧
    0 ≤ (denseHornerNormBounds denominator B).slope at second
  rewrite [← numeratorCache.property] at first
  rewrite [← denominatorCache.property] at second
  have sum := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct first.2 second.1)
    (Fraction.Order.Arithmetic.mul_nonneg_direct first.1 second.2)
  rewrite [Fraction.Field.zero_add] at sum
  exact Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) sum)
    (Fraction.Order.Arithmetic.mul_nonneg_direct positive.le positive.le)

/-- The two actual polynomial quotients have a finite squared-distance bound from their retained common box caches.

Both displayed denominator values must meet the original positive floor.
The original polynomial value and difference estimates feed the exact
finite Gaussian quotient theorem. No nonvanishing assertion is made away
from those two admitted points.
-/
public theorem normSq_eval_div_sub_eval_div_le
    (numerator denominator : Basic.CanonicalCoefficients.CoefficientPolynomial) {B : Box}
    {first last : Basic.Canonical} (firstInside : B.Contains first) (lastInside : B.Contains last)
    (lower : Fraction.Rational) (positive : 0 < lower)
    (firstLower : lower ≤ Norm.Basic.normSq (denominator.eval first))
    (lastLower : lower ≤ Norm.Basic.normSq (denominator.eval last))
    (numeratorCache : HornerCache numerator B) (denominatorCache : HornerCache denominator B) :
    Norm.Basic.normSq (numerator.eval first / denominator.eval first -
      numerator.eval last / denominator.eval last) ≤
      quotientLipschitzBound numerator denominator B lower numeratorCache denominatorCache *
        Norm.Basic.normSq (first - last) := by
  have numeratorDifference := normSq_eval_sub_eval_le numerator firstInside lastInside
  have denominatorDifference := normSq_eval_sub_eval_le denominator lastInside firstInside
  rewrite [Norm.Bounds.normSq_sub_symm last first] at denominatorDifference
  have numeratorBound := normSq_eval_le_denseEvalNormBound numerator lastInside
  have denominatorBound := normSq_eval_le_denseEvalNormBound denominator lastInside
  have estimate := Norm.Quotient.ApproximationQuotientVariation.normSq_div_sub_div_le positive
    numeratorDifference numeratorBound denominatorBound denominatorDifference firstLower lastLower
  have same : Approximation.Rational.Budget.Quotient.quotientBound
      (denseEvalNormLipschitzBound numerator B) (denseEvalNormBound numerator B) (denseEvalNormBound denominator B)
      lower (Norm.Basic.normSq (first - last))
      (denseEvalNormLipschitzBound denominator B * Norm.Basic.normSq (first - last)) =
      quotientLipschitzBound numerator denominator B lower numeratorCache denominatorCache *
        Norm.Basic.normSq (first - last) := by
    unfold Approximation.Rational.Budget.Quotient.quotientBound quotientLipschitzBound
    rewrite [numeratorCache.property, denominatorCache.property]
    simp only [denseEvalNormLipschitzBound, denseEvalNormBound, Fraction.Field.div_eq_mul_inv_direct]
    ring1
  exact estimate.trans_eq same

end Purelib.Polynomial.Dense.Gaussian.Bounds.Box
