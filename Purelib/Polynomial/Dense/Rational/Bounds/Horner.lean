module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Data.Rat.Interval.Bounds
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring
import Purelib.Algebra.Semiring.Normalization

/-!
# Retained rational Horner square bounds

The original finite coefficient folds retain their interval radii and
accumulator data. Value bounds and paired value/difference bounds
certify those same finite evaluations and their scalar readbacks.
-/

namespace Purelib.Polynomial.Dense.Rational.Bounds.Horner

open Purelib
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Bounds.Square (twice_le_twice twice_nonneg add_sq_le_two)
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational
open Purelib.Algebra.Semiring

/-- One Horner step for a squared evaluation majorant.

The original step multiplies the retained squared-value bound by the
supplied squared radius, adds the exact coefficient square, and doubles
that same rational sum. -/
@[expose] public def evalSqBoundStep (radiusSq bound coefficient : Fraction.Rational) : Fraction.Rational :=
  2 * (bound * radiusSq + coefficient ^ 2)

/-- Finite Horner majorant for `p(t)^2` throughout an interval.

The original coefficient list is folded from zero with the interval's
retained square bound. Every coefficient and accumulator is consumed in
the same original order. -/
@[expose] public def evalSqBound (p : Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) :
  Fraction.Rational :=
  p.coeffs.foldl (evalSqBoundStep interval.squareBound) 0

/-- Monotonicity of one squared Horner-majorant step against separately
displayed radius, accumulator, and coefficient-square ceilings.

The radius and ceiling accumulator are nonnegative. The retained
component inequalities bound the original product and coefficient square
inside the same doubled Horner step. -/
public theorem evalSqBoundStep_le
    {radius bound coefficient radiusCeiling boundCeiling
      coefficientSqCeiling : Fraction.Rational}
    (radiusNonnegative : 0 ≤ radius)
    (radiusLe : radius ≤ radiusCeiling)
    (boundLe : bound ≤ boundCeiling)
    (coefficientSqLe : coefficient ^ 2 ≤ coefficientSqCeiling)
    (boundCeilingNonnegative : 0 ≤ boundCeiling) :
    evalSqBoundStep radius bound coefficient ≤
      2 * (boundCeiling * radiusCeiling + coefficientSqCeiling) := by
  unfold evalSqBoundStep
  apply Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
  · exact add_le_add
      (Order.Arithmetic.mul_le_mul_direct boundLe radiusLe
        radiusNonnegative boundCeilingNonnegative)
      coefficientSqLe
  · decide

/-- A three-coefficient polynomial needs exactly three displayed Horner
steps.  This compact bound lets explicit finite calculations compare simple
coefficient-square ceilings without normalizing a large rational fold.

The original coefficient list has exactly the three displayed entries.
Their separate square ceilings and the retained radius ceiling bound
the same three successive accumulator updates. -/
public theorem evalSqBound_three_le
    (polynomial : Basic.CoordinatePolynomial) (a b c : Fraction.Rational)
    (coefficients : polynomial.coeffs = [a, b, c])
    (interval : Data.Rat.Interval.Bounds)
    (radiusCeiling aSqCeiling bSqCeiling cSqCeiling : Fraction.Rational)
    (radiusCeilingNonnegative : 0 ≤ radiusCeiling)
    (aSqCeilingNonnegative : 0 ≤ aSqCeiling)
    (bSqCeilingNonnegative : 0 ≤ bSqCeiling)
    (radiusLe : interval.squareBound ≤ radiusCeiling)
    (aSqLe : a ^ 2 ≤ aSqCeiling)
    (bSqLe : b ^ 2 ≤ bSqCeiling)
    (cSqLe : c ^ 2 ≤ cSqCeiling) :
    evalSqBound polynomial interval ≤
      2 *
        ((2 * ((2 * aSqCeiling) * radiusCeiling + bSqCeiling)) *
            radiusCeiling +
          cSqCeiling) := by
  unfold evalSqBound
  rw [coefficients]
  simp only [List.foldl_cons, List.foldl_nil]
  have firstLe : evalSqBoundStep interval.squareBound 0 a ≤
      2 * aSqCeiling := by
    convert evalSqBoundStep_le interval.squareBound_nonneg radiusLe le_rfl
      aSqLe (show (0 : Fraction.Rational) ≤ 0 by exact le_rfl) using 1
    all_goals ring1
  have firstCeilingNonnegative : 0 ≤ 2 * aSqCeiling :=
    Order.Arithmetic.mul_nonneg_direct (by decide)
      aSqCeilingNonnegative
  have secondLe : evalSqBoundStep interval.squareBound
      (evalSqBoundStep interval.squareBound 0 a) b ≤
        2 * ((2 * aSqCeiling) * radiusCeiling + bSqCeiling) :=
    evalSqBoundStep_le interval.squareBound_nonneg radiusLe firstLe bSqLe
      firstCeilingNonnegative
  have secondCeilingNonnegative :
      0 ≤ 2 * ((2 * aSqCeiling) * radiusCeiling + bSqCeiling) :=
    Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Order.Arithmetic.mul_nonneg_direct
          firstCeilingNonnegative radiusCeilingNonnegative)
        bSqCeilingNonnegative)
  exact evalSqBoundStep_le interval.squareBound_nonneg radiusLe secondLe
    cSqLe secondCeilingNonnegative

section
/-- Enlarging a nonnegative squared radius and accumulator bound enlarges the finite Horner majorant.

The original coefficient list is fixed while both nonnegative radii
and initial accumulator bounds are ordered. Structural induction retains
each coefficient and bounds the two original successor updates. -/
private theorem evalSqBoundCoeffs_monotone
    (coefficients : List Fraction.Rational) {smallRadius largeRadius : Fraction.Rational}
    {smallBound largeBound : Fraction.Rational}
    (smallRadiusNonnegative : 0 ≤ smallRadius)
    (largeRadiusNonnegative : 0 ≤ largeRadius)
    (smallBoundNonnegative : 0 ≤ smallBound)
    (largeBoundNonnegative : 0 ≤ largeBound)
    (radiusLe : smallRadius ≤ largeRadius)
    (boundLe : smallBound ≤ largeBound) :
    coefficients.foldl (evalSqBoundStep smallRadius) smallBound ≤
      coefficients.foldl (evalSqBoundStep largeRadius) largeBound := by
  induction coefficients generalizing smallBound largeBound with
  | nil => exact boundLe
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.foldl_cons]
      have productLe : smallBound * smallRadius ≤
          largeBound * largeRadius :=
        Order.Arithmetic.mul_le_mul_direct boundLe radiusLe
          smallRadiusNonnegative largeBoundNonnegative
      have nextLe : evalSqBoundStep smallRadius smallBound coefficient ≤
          evalSqBoundStep largeRadius largeBound coefficient := by
        exact twice_le_twice (add_le_add productLe (le_refl _))
      apply inductionHypothesis
      · apply twice_nonneg
        exact add_nonneg
          (Order.Arithmetic.mul_nonneg_direct
            smallBoundNonnegative smallRadiusNonnegative)
          (Order.Arithmetic.sq_nonneg_direct coefficient)
      · apply twice_nonneg
        exact add_nonneg
          (Order.Arithmetic.mul_nonneg_direct
            largeBoundNonnegative largeRadiusNonnegative)
          (Order.Arithmetic.sq_nonneg_direct coefficient)
      · exact nextLe
end

/-- Restricting to a refining rational interval cannot increase the computed squared Horner bound.

The supplied interval refines the original root interval, so its retained
square bound does not increase. The same original coefficient fold
transports that scalar radius order from the zero accumulator. -/
public theorem evalSqBound_le_of_refines (p : Basic.CoordinatePolynomial) {interval root : Data.Rat.Interval.Bounds}
    (refines : interval.Refines root) :
    evalSqBound p interval ≤ evalSqBound p root := by
  unfold evalSqBound
  exact Purelib.Polynomial.Dense.Rational.Bounds.Horner.evalSqBoundCoeffs_monotone p.coeffs
    interval.squareBound_nonneg root.squareBound_nonneg
    (le_refl 0) (le_refl 0) (interval.squareBound_le_of_refines refines)
    (le_refl 0)

section
/-- Propagate a nonnegative squared-value majorant through the finite Horner fold.

The supplied point belongs to the original interval and its retained
accumulator square is bounded by a nonnegative rational. Each original
coefficient update preserves nonnegativity and the displayed square bound. -/
private theorem evalSqBoundCoeffs_spec (coefficients : List Fraction.Rational)
    (interval : Data.Rat.Interval.Bounds) {x accumulator bound : Fraction.Rational}
    (inside : interval.Contains x) (boundNonnegative : 0 ≤ bound)
    (accumulatorBound : accumulator ^ 2 ≤ bound) :
    let finalValue := coefficients.foldl
      (fun value coefficient => value * x + coefficient) accumulator
    let finalBound := coefficients.foldl
      (evalSqBoundStep interval.squareBound) bound
    0 ≤ finalBound ∧ finalValue ^ 2 ≤ finalBound := by
  induction coefficients generalizing accumulator bound with
  | nil => exact ⟨boundNonnegative, accumulatorBound⟩
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.foldl_cons]
      apply inductionHypothesis
      · apply twice_nonneg
        exact add_nonneg
          (Order.Arithmetic.mul_nonneg_direct boundNonnegative
            interval.squareBound_nonneg)
          (Order.Arithmetic.sq_nonneg_direct coefficient)
      · have productBound : (accumulator * x) ^ 2 ≤
            bound * interval.squareBound := by
          rw [Normalization.product_pow accumulator x 2]
          exact Order.Arithmetic.mul_le_mul_direct accumulatorBound
            (interval.sq_le_squareBound inside)
            (Order.Arithmetic.sq_nonneg_direct x) boundNonnegative
        exact (add_sq_le_two (accumulator * x) coefficient).trans
          (twice_le_twice
            (add_le_add productBound (le_refl (coefficient ^ 2))))
end

/-- The finite squared Horner bound is nonnegative on every valid rational interval.

The original interval supplies its lower endpoint as a retained member.
The zero initial accumulator and bound propagate nonnegativity through
the exact coefficient list. -/
public theorem evalSqBound_nonneg (p : Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) :
    0 ≤ evalSqBound p interval := by
  have specification := Purelib.Polynomial.Dense.Rational.Bounds.Horner.evalSqBoundCoeffs_spec p.coeffs interval
    (x := interval.lower) (accumulator := 0) (bound := 0)
    ⟨le_rfl, interval.valid⟩ (le_refl 0) (by
      change (0 : Fraction.Rational) ≤ 0
      exact le_rfl)
  exact specification.1

/-- The computed Horner majorant bounds the polynomial value squared at every point of the retained interval.

The supplied point belongs to the retained interval. The original
polynomial evaluation and its squared majorant fold the same coefficient
list from their respective zero accumulators. -/
public theorem eval_sq_le_evalSqBound (p : Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds)
    {x : Fraction.Rational} (inside : interval.Contains x) :
    p.eval x ^ 2 ≤ evalSqBound p interval := by
  have specification := Purelib.Polynomial.Dense.Rational.Bounds.Horner.evalSqBoundCoeffs_spec p.coeffs interval
    (x := x) (accumulator := 0) (bound := 0) inside (le_refl 0) (by
      change (0 : Fraction.Rational) ≤ 0
      exact le_rfl)
  simpa only [Dense.Basic.DensePolynomial.eval, Dense.Basic.DensePolynomial.evalCoeffs, evalSqBound] using
    specification.2

end Purelib.Polynomial.Dense.Rational.Bounds.Horner
