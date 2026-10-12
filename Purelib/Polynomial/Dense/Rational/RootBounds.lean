module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Int.Divisibility
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Integer.Homogeneous
public import Purelib.Polynomial.Dense.Rational.Denominator
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Nat.Divisibility

/-!
# Endpoint divisors of retained rational homogeneous zeros

The original reduced numerator and positive denominator remain paired with
the exact cleared descending table. Scalar homogeneous identities and retained
coprimality witnesses establish the endpoint divisors and finite magnitude bounds.
-/

namespace Purelib.Polynomial.Dense.Rational.RootBounds

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Algebra
open Purelib.Data
open Purelib.Data.Int

/-- Sum of absolute values, used as a deliberately coarse common bound for
the finitely many cleared coefficients.

The original ordered table contributes each displayed integer magnitude once.
Its finite natural sum bounds every retained coefficient occurrence. -/
@[expose] public def coefficientBound : List Int → Nat
  | [] => 0
  | coefficient :: remaining =>
      coefficient.natAbs + coefficientBound remaining

/-- The absolute value of each retained integer coefficient is bounded by the sum of all coefficient absolute values.

The actual occurrence selects its retained head magnitude or a magnitude
in the unchanged tail. Their natural sum supplies the exact scalar bound. -/
public theorem coefficient_natAbs_le_bound
    {coefficient : Int} {coefficients : List Int}
    (member : coefficient ∈ coefficients) :
    coefficient.natAbs ≤ coefficientBound coefficients := by
  induction coefficients with
  | nil => cases member
  | cons head remaining inductionHypothesis =>
      cases member with
      | head => exact Nat.le_add_right _ _
      | tail _ inTail =>
          exact Nat.le_trans (inductionHypothesis inTail) (Nat.le_add_left _ _)

/-- The constant coefficient of a nonempty descending integer list is one of its retained entries.

The original final-entry accumulator returns one actual coefficient occurrence.
Removing a preceding head preserves that same retained tail occurrence. -/
public theorem constantCoefficient_mem
    (leading : Int) (remaining : List Int) :
    Dense.Integer.Homogeneous.constantCoefficient (leading :: remaining) ∈ leading :: remaining := by
  induction remaining generalizing leading with
  | nil => exact List.mem_cons_self
  | cons next remaining inductionHypothesis =>
      rw [Dense.Integer.Homogeneous.constantCoefficient_cons_cons]
      exact List.mem_cons_of_mem leading (inductionHypothesis next)

/-- A homogeneous zero with coprime numerator and denominator has numerator
dividing the displayed constant coefficient and denominator dividing the
displayed leading coefficient.  These are the sharp finite facts consumed by
the divisor candidate enumerator below.

The original homogeneous zero and the retained coprimality certificate isolate
the endpoint divisors. Their explicit powers and canonical magnitudes retain
the same numerator, denominator and descending coefficient order. -/
public theorem reduced_divisors_of_homogeneous_zero
    (reduced : Fraction.Basic.ReducedFraction) (leading : Int) (remaining : List Int)
    (_leadingNonzero : leading ≠ 0)
    (_constantNonzero :
      Dense.Integer.Homogeneous.constantCoefficient (leading :: remaining) ≠ 0)
    (zero : Dense.Integer.Homogeneous.homogeneousEval reduced.num reduced.den
      (leading :: remaining) = 0) :
    reduced.num.natAbs ∣
        (Dense.Integer.Homogeneous.constantCoefficient (leading :: remaining)).natAbs ∧
      reduced.den ∣ leading.natAbs := open Purelib in by
  have denominatorDvdInteger :=
    Dense.Integer.Homogeneous.denominator_dvd_homogeneousEval_sub_leading reduced.num reduced.den
      leading remaining
  rewrite [zero, Arithmetic.zero_sub] at denominatorDvdInteger
  have denominatorDvdNat :=
    Divisibility.natAbs_dvd_natAbs_of_dvd denominatorDvdInteger
  simp only [Int.natAbs_natCast, Int.natAbs_neg, Arithmetic.natAbs_mul,
    Arithmetic.natAbs_pow] at denominatorDvdNat
  have denominatorDvdLeading : reduced.den ∣ leading.natAbs :=
    by
      rcases reduced.reduced with ⟨certificate⟩
      exact certificate.symm.dvd_of_dvd_mul_right_pow
        remaining.length denominatorDvdNat

  have numeratorDvdInteger :=
    Dense.Integer.Homogeneous.numerator_dvd_homogeneousEval_sub_constant reduced.num reduced.den
      leading remaining
  rewrite [zero, Arithmetic.zero_sub] at numeratorDvdInteger
  have numeratorDvdNat := Divisibility.natAbs_dvd_natAbs_of_dvd numeratorDvdInteger
  simp only [Int.natAbs_neg, Arithmetic.natAbs_mul, Arithmetic.natAbs_pow,
    Int.natAbs_natCast] at numeratorDvdNat
  have numeratorDvdConstant :
      reduced.num.natAbs ∣
        (Dense.Integer.Homogeneous.constantCoefficient (leading :: remaining)).natAbs :=
    by
      rcases reduced.reduced with ⟨certificate⟩
      exact certificate.dvd_of_dvd_mul_right_pow
        remaining.length numeratorDvdNat

  exact ⟨numeratorDvdConstant, denominatorDvdLeading⟩

/-- Bound the reduced numerator magnitude and denominator of a homogeneous rational zero.

Nonzero leading and constant coefficients give endpoint divisibility, and their magnitudes are bounded by the finite sum
of coefficient absolute values. -/
public theorem reduced_bounds_of_homogeneous_zero
    (reduced : Fraction.Basic.ReducedFraction) (leading : Int) (remaining : List Int)
    (leadingNonzero : leading ≠ 0)
    (constantNonzero :
      Dense.Integer.Homogeneous.constantCoefficient (leading :: remaining) ≠ 0)
    (zero : Dense.Integer.Homogeneous.homogeneousEval reduced.num reduced.den
      (leading :: remaining) = 0) :
    reduced.num.natAbs ≤ coefficientBound (leading :: remaining) ∧
      reduced.den ≤ coefficientBound (leading :: remaining) := by
  have divisors := reduced_divisors_of_homogeneous_zero reduced leading
    remaining leadingNonzero constantNonzero zero
  constructor
  · exact Nat.le_trans
      (Nat.Divisibility.le_of_dvd (Arithmetic.natAbs_pos_of_ne_zero constantNonzero) divisors.1)
      (coefficient_natAbs_le_bound
        (constantCoefficient_mem leading remaining))
  · exact Nat.le_trans
      (Nat.Divisibility.le_of_dvd (Arithmetic.natAbs_pos_of_ne_zero leadingNonzero) divisors.2)
      (coefficient_natAbs_le_bound List.mem_cons_self)

/-- An exact rational zero of a nonempty displayed coefficient list gives a
zero of its finitely cleared homogeneous integer list.

The exact cached common-denominator result scales the original rational zero.
Its retained representative and same integer table supply the homogeneous zero. -/
public theorem homogeneous_zero_of_eval_zero
    (point : Fraction.Rational) (coefficient : Fraction.Rational) (remaining : List Fraction.Rational)
    (zero : Dense.Basic.DensePolynomial.evalCoeffs point (coefficient :: remaining) = 0) :
    Dense.Integer.Homogeneous.homogeneousEval (Fraction.Basic.representative point).num (Fraction.Basic.representative
      point).den
      (Dense.Rational.Denominator.clear (coefficient :: remaining)).coefficients = 0 := by
  have clearedZero :
      Dense.Integer.Homogeneous.evalIntegers point (Dense.Rational.Denominator.clear (coefficient ::
        remaining)).coefficients = 0 := by
    rw [Dense.Rational.Denominator.eval_clear, zero, mul_zero]
  let leading :=
    (Fraction.Basic.representative coefficient).num *
      ((Dense.Rational.Denominator.clear remaining).denominator : Int)
  let integerRemaining :=
    (Dense.Rational.Denominator.clear remaining).coefficients.map
      (fun value => ((Fraction.Basic.representative coefficient).den : Int) * value)
  have clearedShape :
      (Dense.Rational.Denominator.clear (coefficient :: remaining)).coefficients =
        leading :: integerRemaining := rfl
  rw [clearedShape] at clearedZero ⊢
  rw [Fraction.Cast.representative_eq_num_div_den point] at clearedZero
  have scaled := Dense.Integer.Homogeneous.homogeneousEval_cons_eq_scaled
    (Fraction.Basic.representative point).num (Fraction.Basic.representative point).den_pos
    leading integerRemaining
  rw [clearedZero, mul_zero] at scaled
  exact Fraction.Cast.Compatibility.intCast_injective_direct scaled

end Purelib.Polynomial.Dense.Rational.RootBounds
