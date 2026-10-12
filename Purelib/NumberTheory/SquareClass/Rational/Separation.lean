module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.NumberTheory.Prime.Factor
import Purelib.NumberTheory.Prime.Basic
import Purelib.Data.Int.Arithmetic
public import Purelib.NumberTheory.Prime.FinitePacks
public import Purelib.NumberTheory.SquareClass.Rational.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.SquareClass.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat

open Purelib.NumberTheory

open Purelib.NumberTheory.SquareClass
open Purelib.Data.Int

section
public section

/-!
# Arbitrarily large finite packs of rational square classes

The infinitude sentence following Theorem 62 is exposed through a finite
request: a natural number produces exactly that many positive square-class
representatives, explicit rotation preimages, and pairwise inequivalence
certificates.  The construction performs only the requested number of finite
Euclid steps.  It neither forms the carrier of all square classes nor imports
an infinite-primes theorem.
-/

namespace Purelib.NumberTheory.SquareClass.Rational.Separation

namespace SquareClassPacks

/-! ## Positive square-class entries -/

/-- The positive rational square class represented by one displayed prime. -/
@[expose] def positivePrimeClass (prime : Prime.FinitePacks.SquareClassPacks.EuclidPrime) :
    Rational.Basic.TheoremSixtyTwo.PositiveSquareClassRepresentative where
  representative :=
    { value := (prime.value : Fraction.Rational)
      nonzero := (Fraction.Cast.Order.natCast_pos_direct
        (Prime.pos prime.prime)).ne' }
  positive := Fraction.Cast.Order.natCast_pos_direct (Prime.pos prime.prime)

/-- Distinct retained primes represent different positive rational square classes.

Clearing a proposed square ratio forces a common prime divisor of its reduced numerator and denominator. -/
theorem distinct_primes_not_equivalent
    (left right : Prime.FinitePacks.SquareClassPacks.EuclidPrime) (different : left ≠ right) :
    ¬ (positivePrimeClass left).representative.Equivalent
      (positivePrimeClass right).representative := by
  intro equivalent
  rcases equivalent with ⟨factor, _factorNonzero, classEquation⟩
  change (right.value : Fraction.Rational) =
    factor ^ 2 * (left.value : Fraction.Rational) at classEquation
  have primeValuesDifferent : left.value ≠ right.value := by
    intro equal
    apply different
    exact Prime.FinitePacks.SquareClassPacks.EuclidPrime.ext equal
  let reduced := Fraction.Basic.representative factor
  have cleared := Fraction.Cast.representative_mul_den factor
  change factor * (reduced.den : Fraction.Rational) = (reduced.num : Fraction.Rational) at cleared
  have rationalEquation :
      (right.value : Fraction.Rational) * (reduced.den : Fraction.Rational) ^ 2 =
        (reduced.num : Fraction.Rational) ^ 2 * (left.value : Fraction.Rational) := by
    calc
      (right.value : Fraction.Rational) * (reduced.den : Fraction.Rational) ^ 2 =
          (factor ^ 2 * (left.value : Fraction.Rational)) *
            (reduced.den : Fraction.Rational) ^ 2 := by
              rw [classEquation]
      _ = (factor * (reduced.den : Fraction.Rational)) ^ 2 *
            (left.value : Fraction.Rational) := by ring1
      _ = (reduced.num : Fraction.Rational) ^ 2 * (left.value : Fraction.Rational) := by
            rw [cleared]
  have integerEquation :
      (right.value : Int) *
          ((reduced.den : Int) * (reduced.den : Int)) =
        (reduced.num * reduced.num) * (left.value : Int) := by
    apply Fraction.Cast.Compatibility.intCast_injective_direct
    rw [Fraction.Cast.intCast_mul_direct,
      Fraction.Cast.intCast_mul_direct,
      Fraction.Cast.intCast_mul_direct,
      Fraction.Cast.intCast_mul_direct]
    simpa only [Int.cast_natCast, pow_two] using rationalEquation
  have absoluteEquation := congrArg Int.natAbs integerEquation
  have naturalEquation :
      right.value * (reduced.den * reduced.den) =
        (reduced.num.natAbs * reduced.num.natAbs) * left.value := by
    simpa only [Arithmetic.natAbs_mul, Int.natAbs_natCast] using absoluteEquation
  have leftDividesLeftSide :
      left.value ∣ right.value * (reduced.den * reduced.den) := by
    refine ⟨reduced.num.natAbs * reduced.num.natAbs, ?_⟩
    calc
      right.value * (reduced.den * reduced.den) =
          (reduced.num.natAbs * reduced.num.natAbs) * left.value :=
        naturalEquation
      _ = left.value *
          (reduced.num.natAbs * reduced.num.natAbs) := by ring1
  have leftDoesNotDivideRight : ¬ left.value ∣ right.value :=
    Prime.not_dvd_of_ne left.prime right.prime primeValuesDifferent
  have leftDividesDenominatorSquare :
      left.value ∣ reduced.den * reduced.den :=
    Prime.Factor.prime_dvd_right_of_dvd_mul_of_not_dvd
      left.prime leftDoesNotDivideRight leftDividesLeftSide
  have leftDividesDenominator : left.value ∣ reduced.den :=
    Prime.Factor.prime_dvd_of_dvd_square left.prime
      leftDividesDenominatorSquare
  rcases leftDividesDenominator with ⟨denominatorFactor,
    denominatorEquation⟩
  have canceledEquation :
      right.value * left.value *
          (denominatorFactor * denominatorFactor) =
        reduced.num.natAbs * reduced.num.natAbs := by
    apply Nat.eq_of_mul_eq_mul_left (Prime.pos left.prime)
    calc
      left.value *
          (right.value * left.value *
            (denominatorFactor * denominatorFactor)) =
        right.value *
          ((left.value * denominatorFactor) *
            (left.value * denominatorFactor)) := by ring1
      _ = right.value * (reduced.den * reduced.den) := by
        rw [← denominatorEquation]
      _ = (reduced.num.natAbs * reduced.num.natAbs) * left.value :=
        naturalEquation
      _ = left.value *
          (reduced.num.natAbs * reduced.num.natAbs) := by ring1
  have leftDividesNumeratorSquare :
      left.value ∣ reduced.num.natAbs * reduced.num.natAbs := by
    refine ⟨right.value *
      (denominatorFactor * denominatorFactor), ?_⟩
    calc
      reduced.num.natAbs * reduced.num.natAbs =
          right.value * left.value *
            (denominatorFactor * denominatorFactor) :=
        canceledEquation.symm
      _ = left.value *
          (right.value *
            (denominatorFactor * denominatorFactor)) := by ring1
  have leftDividesNumerator : left.value ∣ reduced.num.natAbs :=
    Prime.Factor.prime_dvd_of_dvd_square left.prime
      leftDividesNumeratorSquare
  rcases reduced.reduced with ⟨coprime⟩
  have leftIsOne := coprime.eq_one_of_dvd
    leftDividesNumerator ⟨denominatorFactor, denominatorEquation⟩
  exact Prime.ne_one left.prime leftIsOne

end SquareClassPacks

end Purelib.NumberTheory.SquareClass.Rational.Separation

end
