module

meta import Purelib.Elab.ConstructiveInjectivity
-- Exposed integer builders retain the ring frontend's generated class references.
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Basic
public import Purelib.Data.Int.Parity
public import Purelib.Data.Nat.Divisibility.IntCast
public import Purelib.Data.Int.Division
public import Purelib.NumberTheory.FourSquares.PrimeSeed
import Purelib.NumberTheory.FourSquares.Basic
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Divisibility
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Nat.Parity
import Purelib.Data.Nat.Remainder.Arithmetic
import Purelib.Algebra.Semiring.Nat
import Purelib.Algebra.Ring.Int
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib
open Purelib.NumberTheory
open Purelib.Data
open Purelib.Data.Nat
open Purelib.Algebra

/-!
# Retained odd and even four-square descent

Centered residues cache their original signed value and quotient. Odd steps
retain the four Euler quotients and their natural magnitudes; even steps
retain the original quotient by two and chosen equal-parity pairing. The
same positive multiplier controls the well-founded descent to a prime.
-/

public section

namespace Purelib.NumberTheory.FourSquares.Descent

attribute [local instance high] Semiring.Nat.commSemiring Ring.Int.commRing
attribute [local instance high] CommSemiring.toSemiring Semiring.toMonoid
attribute [local instance high] Monoid.toSemigroup

set_option genInjectivity false in
/-- A centered residue retains its original signed value and quotient.

Their decomposition identifies the same natural source. Twice the retained
magnitude is strictly below the original odd modulus. -/
structure CenteredResidue (modulus source : Nat) where
  /-- The retained signed residue centered around zero. -/ value : Int
  /-- The retained integer quotient in the centered decomposition. -/ quotient : Int
  /-- The original natural source equals the centered residue plus the modulus times the retained quotient. -/
    decomposition :
    (source : Int) = value + (modulus : Int) * quotient
  /-- Twice the retained residue magnitude is strictly below the modulus. -/ small : 2 * value.natAbs < modulus

constructive_injectivity CenteredResidue

/-- Compute a centered representative with its cached original quotient.

The original remainder comparison selects its natural cast or negative
complement. That same branch retains the original quotient or its successor
and certifies the strict half-modulus magnitude bound. -/
@[expose] def centeredResidue (modulus source : Nat) (modulusPositive : 0 < modulus)
    (modulusOdd : Parity.Odd modulus) : CenteredResidue modulus source := by
  let remainder := source % modulus
  let quotient := source / modulus
  have remainderBelow : remainder < modulus :=
    Nat.mod_lt source modulusPositive
  have divisionEquation : remainder + modulus * quotient = source := by
    exact Division.mod_add_div source modulus
  have castDivisionEquation :
      (source : Int) =
        (remainder : Int) + (modulus : Int) * (quotient : Int) := by
    calc
      (source : Int) = ((remainder + modulus * quotient : Nat) : Int) :=
        congrArg (fun value : Nat => (value : Int)) divisionEquation.symm
      _ = (remainder : Int) + ((modulus * quotient : Nat) : Int) :=
        (Int.ofNat_add_ofNat remainder (modulus * quotient)).symm
      _ = (remainder : Int) + (modulus : Int) * (quotient : Int) := by
        rw [Int.ofNat_mul_ofNat]
  by_cases lowerHalf : 2 * remainder < modulus
  · exact
      { value := (remainder : Int)
        quotient := (quotient : Int)
        decomposition := castDivisionEquation
        small := lowerHalf }
  · have modulusBelowDouble : modulus < 2 * remainder := by
      have weak : modulus ≤ 2 * remainder := Nat.le_of_not_gt lowerHalf
      have unequal : modulus ≠ 2 * remainder := by
        rintro equality
        rcases modulusOdd with ⟨half, oddEquation⟩
        omega0
      clear modulusOdd
      omega0
    have centeredSmall : 2 * (modulus - remainder) < modulus := by
      clear modulusOdd
      omega0
    exact
      { value := -((modulus - remainder : Nat) : Int)
        quotient := (quotient : Int) + 1
        decomposition := by
          have remainderLe : remainder ≤ modulus := Nat.le_of_lt remainderBelow
          have castDifference :
              ((modulus - remainder : Nat) : Int) =
                (modulus : Int) - (remainder : Int) := by
            exact Int.Arithmetic.natCast_sub_of_le remainderLe
          rw [castDifference]
          calc
            (source : Int) =
                (remainder : Int) + (modulus : Int) * (quotient : Int) :=
              castDivisionEquation
            _ = -((modulus : Int) - (remainder : Int)) +
                (modulus : Int) * ((quotient : Int) + 1) := by ring1
        small := by
          have magnitude : (-((modulus - remainder : Nat) : Int)).natAbs =
              modulus - remainder := Int.natAbs_negOfNat (modulus - remainder)
          rewrite [magnitude]
          exact centeredSmall }

/-- Four strict half-modulus bounds place their square sum below the modulus square.

Doubling the four squares bounds them by the modulus times their root sum.
The same strict root bounds make that sum smaller than twice the modulus. -/
theorem small_four_square_sum_lt
    {modulus first second third fourth : Nat}
    (modulusPositive : 0 < modulus)
    (firstSmall : 2 * first < modulus)
    (secondSmall : 2 * second < modulus)
    (thirdSmall : 2 * third < modulus)
    (fourthSmall : 2 * fourth < modulus) :
    first ^ 2 + second ^ 2 + third ^ 2 + fourth ^ 2 <
      modulus * modulus := by
  have firstBound :=
    Nat.mul_le_mul_right first (Nat.le_of_lt firstSmall)
  have secondBound :=
    Nat.mul_le_mul_right second (Nat.le_of_lt secondSmall)
  have thirdBound :=
    Nat.mul_le_mul_right third (Nat.le_of_lt thirdSmall)
  have fourthBound :=
    Nat.mul_le_mul_right fourth (Nat.le_of_lt fourthSmall)
  have firstBound' : 2 * (first * first) ≤ modulus * first := by
    simpa only [Multiplication.mul_assoc] using firstBound
  have secondBound' : 2 * (second * second) ≤ modulus * second := by
    simpa only [Multiplication.mul_assoc] using secondBound
  have thirdBound' : 2 * (third * third) ≤ modulus * third := by
    simpa only [Multiplication.mul_assoc] using thirdBound
  have fourthBound' : 2 * (fourth * fourth) ≤ modulus * fourth := by
    simpa only [Multiplication.mul_assoc] using fourthBound
  have rootsBelow : first + second + third + fourth < 2 * modulus := by
    omega0
  have doubledSquaresBound :
      2 * (first ^ 2 + second ^ 2 + third ^ 2 + fourth ^ 2) ≤
        modulus * (first + second + third + fourth) := by
    simp only [Multiplication.pow_two, Multiplication.left_distrib]
    omega0
  have scaledRootsBelow :
      modulus * (first + second + third + fourth) <
        modulus * (2 * modulus) :=
    Nat.mul_lt_mul_of_pos_left rootsBelow modulusPositive
  have doubledSquaresBelow :
      2 * (first ^ 2 + second ^ 2 + third ^ 2 + fourth ^ 2) <
        2 * (modulus * modulus) := by
    apply Nat.lt_of_le_of_lt doubledSquaresBound
    calc
      modulus * (first + second + third + fourth) <
          modulus * (2 * modulus) := scaledRootsBelow
      _ = 2 * (modulus * modulus) := by ring1
  omega0

/-- A natural value whose original square is zero is zero.

A successor has a positive self-product. The zero-square certificate
excludes that constructor without changing the natural power operation. -/
theorem nat_eq_zero_of_square_eq_zero {value : Nat}
    (squareZero : value ^ 2 = 0) : value = 0 := by
  cases value with
  | zero => rfl
  | succ value =>
      have squarePositive : 0 < (value + 1) * (value + 1) :=
        Nat.mul_pos (Nat.zero_lt_succ value) (Nat.zero_lt_succ value)
      rw [Multiplication.pow_two] at squareZero
      exact (Nat.ne_of_gt squarePositive squareZero).elim

set_option genInjectivity false in
/-- A descent step retains a smaller positive multiplier and its representation.

Its four roots certify the product of that exact multiplier with the
original target. The retained strict bound supplies the recursive descent. -/
structure DescentStep (previous target : Nat) where
  /-- The smaller retained multiplier of the original target. -/ multiplier : Nat
  /-- The retained smaller multiplier is positive. -/ positive : 0 < multiplier
  /-- The retained multiplier is strictly below the previous multiplier. -/ below : multiplier < previous
  /-- A certified four-square representation of the retained multiplier times the original target. -/ representation :
    Basic.Representation (multiplier * target)

constructive_injectivity DescentStep

/-- Compute the original odd-multiplier descent step.

Four centered residues retain their signed values and quotients. The same
four Euler products are divided by the original multiplier, and their
natural magnitudes represent the retained smaller positive multiplier. -/
@[expose] def oddDescentStep (prime multiplier : Nat)
    (primeIsPrime : NumberTheory.Prime prime)
    (multiplierPositive : 0 < multiplier)
    (multiplierBelowPrime : multiplier < prime)
    (multiplierGreaterOne : 1 < multiplier)
    (multiplierOdd : Parity.Odd multiplier)
    (input : Basic.Representation (multiplier * prime)) :
    DescentStep multiplier prime := by
  let firstCentered := centeredResidue multiplier input.first
    multiplierPositive multiplierOdd
  let secondCentered := centeredResidue multiplier input.second
    multiplierPositive multiplierOdd
  let thirdCentered := centeredResidue multiplier input.third
    multiplierPositive multiplierOdd
  let fourthCentered := centeredResidue multiplier input.fourth
    multiplierPositive multiplierOdd
  let centeredSum :=
    firstCentered.value.natAbs ^ 2 +
      secondCentered.value.natAbs ^ 2 +
      thirdCentered.value.natAbs ^ 2 +
      fourthCentered.value.natAbs ^ 2
  have inputCast :
      (input.first : Int) ^ 2 + (input.second : Int) ^ 2 +
          (input.third : Int) ^ 2 + (input.fourth : Int) ^ 2 =
        (multiplier : Int) * (prime : Int) := by
    have castEquation :=
      congrArg (fun value : Nat => (value : Int)) input.equation
    exact castEquation
  have centeredSumCast :
      (centeredSum : Int) =
        firstCentered.value ^ 2 + secondCentered.value ^ 2 +
          thirdCentered.value ^ 2 + fourthCentered.value ^ 2 := by
    unfold centeredSum
    change (firstCentered.value.natAbs : Int) ^ 2 +
        (secondCentered.value.natAbs : Int) ^ 2 +
        (thirdCentered.value.natAbs : Int) ^ 2 +
        (fourthCentered.value.natAbs : Int) ^ 2 = _
    exact (congrArg₂ (fun left right : Int => left + right)
      (congrArg₂ (fun left right : Int => left + right)
        (congrArg₂ (fun left right : Int => left + right)
          (Int.Arithmetic.natAbs_pow_two firstCentered.value)
          (Int.Arithmetic.natAbs_pow_two secondCentered.value))
        (Int.Arithmetic.natAbs_pow_two thirdCentered.value))
      (Int.Arithmetic.natAbs_pow_two fourthCentered.value))
  let correction : Int :=
    2 * firstCentered.value * firstCentered.quotient +
      (multiplier : Int) * firstCentered.quotient ^ 2 +
      2 * secondCentered.value * secondCentered.quotient +
      (multiplier : Int) * secondCentered.quotient ^ 2 +
      2 * thirdCentered.value * thirdCentered.quotient +
      (multiplier : Int) * thirdCentered.quotient ^ 2 +
      2 * fourthCentered.value * fourthCentered.quotient +
      (multiplier : Int) * fourthCentered.quotient ^ 2
  have expandedCentered :
      (firstCentered.value ^ 2 + secondCentered.value ^ 2 +
          thirdCentered.value ^ 2 + fourthCentered.value ^ 2) +
          (multiplier : Int) * correction =
        (multiplier : Int) * (prime : Int) := by
    calc
      (firstCentered.value ^ 2 + secondCentered.value ^ 2 +
            thirdCentered.value ^ 2 + fourthCentered.value ^ 2) +
            (multiplier : Int) * correction =
          (firstCentered.value +
              (multiplier : Int) * firstCentered.quotient) ^ 2 +
            (secondCentered.value +
              (multiplier : Int) * secondCentered.quotient) ^ 2 +
            (thirdCentered.value +
              (multiplier : Int) * thirdCentered.quotient) ^ 2 +
            (fourthCentered.value +
              (multiplier : Int) * fourthCentered.quotient) ^ 2 := by
        unfold correction
        ring1
      _ = (input.first : Int) ^ 2 + (input.second : Int) ^ 2 +
            (input.third : Int) ^ 2 + (input.fourth : Int) ^ 2 := by
        rw [← firstCentered.decomposition,
          ← secondCentered.decomposition,
          ← thirdCentered.decomposition,
          ← fourthCentered.decomposition]
      _ = (multiplier : Int) * (prime : Int) := inputCast
  have centeredDividesInt :
      (multiplier : Int) ∣
        firstCentered.value ^ 2 + secondCentered.value ^ 2 +
          thirdCentered.value ^ 2 + fourthCentered.value ^ 2 := by
    refine ⟨(prime : Int) - correction, ?_⟩
    calc
      firstCentered.value ^ 2 + secondCentered.value ^ 2 +
            thirdCentered.value ^ 2 + fourthCentered.value ^ 2 =
          (multiplier : Int) * (prime : Int) -
            (multiplier : Int) * correction :=
        by
          have subtracted := congrArg
            (fun value : Int => value - (multiplier : Int) * correction)
            expandedCentered
          rewrite [Int.sub_eq_add_neg, Int.Arithmetic.add_assoc] at subtracted
          rewrite [Int.Arithmetic.add_comm ((multiplier : Int) * correction)
            (-((multiplier : Int) * correction)),
            Int.Arithmetic.neg_add_cancel, Int.add_zero] at subtracted
          exact subtracted
      _ = (multiplier : Int) * ((prime : Int) - correction) := by ring1
  have centeredDivides : multiplier ∣ centeredSum := by
    apply Divisibility.IntCast.nat_dvd_of_int_natCast_dvd multiplierPositive
    rw [centeredSumCast]
    exact centeredDividesInt
  let nextMultiplier := centeredSum / multiplier
  have nextEquation : centeredSum = nextMultiplier * multiplier :=
    (Division.div_mul_cancel centeredDivides).symm
  have centeredSumBelow : centeredSum < multiplier * multiplier := by
    unfold centeredSum
    exact small_four_square_sum_lt multiplierPositive
      firstCentered.small secondCentered.small thirdCentered.small
      fourthCentered.small
  have nextBelow : nextMultiplier < multiplier := by
    apply Divisibility.IntCast.nat_lt_of_mul_lt_mul_right
    rw [← nextEquation]
    exact centeredSumBelow
  have nextPositive : 0 < nextMultiplier := by
    by_contra nextNotPositive
    have nextZero : nextMultiplier = 0 :=
      Nat.eq_zero_of_not_pos nextNotPositive
    have centeredSumZero : centeredSum = 0 := by
      rw [nextEquation, nextZero, Nat.zero_mul]
    have squareZeros :
        ((firstCentered.value.natAbs ^ 2 = 0 ∧
            secondCentered.value.natAbs ^ 2 = 0) ∧
          thirdCentered.value.natAbs ^ 2 = 0) ∧
          fourthCentered.value.natAbs ^ 2 = 0 := by
      unfold centeredSum at centeredSumZero
      have outer := Nat.add_eq_zero_iff.mp centeredSumZero
      have middle := Nat.add_eq_zero_iff.mp outer.1
      have inner := Nat.add_eq_zero_iff.mp middle.1
      exact ⟨⟨⟨inner.1, inner.2⟩, middle.2⟩, outer.2⟩
    have zeroFromMagnitude : ∀ value : Int, value.natAbs = 0 → value = 0 := by
      intro value magnitudeZero
      cases value with
      | ofNat value => exact congrArg Int.ofNat magnitudeZero
      | negSucc value => exact Nat.noConfusion magnitudeZero
    have centeredZeros :
        firstCentered.value = 0 ∧ secondCentered.value = 0 ∧
          thirdCentered.value = 0 ∧ fourthCentered.value = 0 :=
      ⟨zeroFromMagnitude _ (nat_eq_zero_of_square_eq_zero squareZeros.1.1.1),
        zeroFromMagnitude _ (nat_eq_zero_of_square_eq_zero squareZeros.1.1.2),
        zeroFromMagnitude _ (nat_eq_zero_of_square_eq_zero squareZeros.1.2),
        zeroFromMagnitude _ (nat_eq_zero_of_square_eq_zero squareZeros.2)⟩
    have firstDivides : multiplier ∣ input.first := by
      apply Divisibility.IntCast.nat_dvd_of_int_natCast_dvd multiplierPositive
      refine ⟨firstCentered.quotient, ?_⟩
      simpa only [centeredZeros.1, zero_add] using
        firstCentered.decomposition
    have secondDivides : multiplier ∣ input.second := by
      apply Divisibility.IntCast.nat_dvd_of_int_natCast_dvd multiplierPositive
      refine ⟨secondCentered.quotient, ?_⟩
      simpa only [centeredZeros.2.1, zero_add] using
        secondCentered.decomposition
    have thirdDivides : multiplier ∣ input.third := by
      apply Divisibility.IntCast.nat_dvd_of_int_natCast_dvd multiplierPositive
      refine ⟨thirdCentered.quotient, ?_⟩
      simpa only [centeredZeros.2.2.1, zero_add] using
        thirdCentered.decomposition
    have fourthDivides : multiplier ∣ input.fourth := by
      apply Divisibility.IntCast.nat_dvd_of_int_natCast_dvd multiplierPositive
      refine ⟨fourthCentered.quotient, ?_⟩
      simpa only [centeredZeros.2.2.2, zero_add] using
        fourthCentered.decomposition
    have firstSquareDivides :
        multiplier * multiplier ∣ input.first ^ 2 := by
      obtain ⟨factor, factorEquation⟩ := firstDivides
      refine ⟨factor * factor, ?_⟩
      rw [Multiplication.pow_two, factorEquation]
      ring1
    have secondSquareDivides :
        multiplier * multiplier ∣ input.second ^ 2 := by
      obtain ⟨factor, factorEquation⟩ := secondDivides
      refine ⟨factor * factor, ?_⟩
      rw [Multiplication.pow_two, factorEquation]
      ring1
    have thirdSquareDivides :
        multiplier * multiplier ∣ input.third ^ 2 := by
      obtain ⟨factor, factorEquation⟩ := thirdDivides
      refine ⟨factor * factor, ?_⟩
      rw [Multiplication.pow_two, factorEquation]
      ring1
    have fourthSquareDivides :
        multiplier * multiplier ∣ input.fourth ^ 2 := by
      obtain ⟨factor, factorEquation⟩ := fourthDivides
      refine ⟨factor * factor, ?_⟩
      rw [Multiplication.pow_two, factorEquation]
      ring1
    have squareSumDivides :
        multiplier * multiplier ∣
          input.first ^ 2 + input.second ^ 2 +
            input.third ^ 2 + input.fourth ^ 2 :=
      Divisibility.add
        (Divisibility.add (Divisibility.add firstSquareDivides secondSquareDivides)
          thirdSquareDivides) fourthSquareDivides
    have squareMultiplierDividesProduct :
        multiplier * multiplier ∣ multiplier * prime := by
      rw [← input.equation]
      exact squareSumDivides
    have multiplierDividesPrime : multiplier ∣ prime := by
      rcases squareMultiplierDividesProduct with ⟨factor, factorEquation⟩
      refine ⟨factor, ?_⟩
      apply Nat.eq_of_mul_eq_mul_left multiplierPositive
      calc
        multiplier * prime = (multiplier * multiplier) * factor :=
          factorEquation
        _ = multiplier * (multiplier * factor) := by ring1
    rcases primeIsPrime.eq_one_or_self_of_dvd multiplier
        multiplierDividesPrime with multiplierOne | multiplierPrime
    · exact (Nat.ne_of_gt multiplierGreaterOne) multiplierOne
    · exact (Nat.ne_of_lt multiplierBelowPrime) multiplierPrime
  have centeredMultiplierCast :
      firstCentered.value ^ 2 + secondCentered.value ^ 2 +
          thirdCentered.value ^ 2 + fourthCentered.value ^ 2 =
        (nextMultiplier : Int) * (multiplier : Int) := by
    have castEquation :=
      congrArg (fun value : Nat => (value : Int)) nextEquation
    rw [centeredSumCast] at castEquation
    exact castEquation
  let firstEuler : Int :=
    secondCentered.value * (input.first : Int) -
      firstCentered.value * (input.second : Int) -
      fourthCentered.value * (input.third : Int) -
      (-thirdCentered.value) * (input.fourth : Int)
  let secondEuler : Int :=
    secondCentered.value * (input.second : Int) +
      firstCentered.value * (input.first : Int) +
      fourthCentered.value * (input.fourth : Int) -
      (-thirdCentered.value) * (input.third : Int)
  let thirdEuler : Int :=
    secondCentered.value * (input.third : Int) -
      firstCentered.value * (input.fourth : Int) +
      fourthCentered.value * (input.first : Int) +
      (-thirdCentered.value) * (input.second : Int)
  let fourthEuler : Int :=
    secondCentered.value * (input.fourth : Int) +
      firstCentered.value * (input.third : Int) -
      fourthCentered.value * (input.second : Int) +
      (-thirdCentered.value) * (input.first : Int)
  have firstEulerDivides : (multiplier : Int) ∣ firstEuler := by
    refine ⟨secondCentered.value * firstCentered.quotient -
      firstCentered.value * secondCentered.quotient -
      fourthCentered.value * thirdCentered.quotient +
      thirdCentered.value * fourthCentered.quotient, ?_⟩
    unfold firstEuler
    rw [firstCentered.decomposition, secondCentered.decomposition,
      thirdCentered.decomposition, fourthCentered.decomposition]
    ring1
  have secondEulerDivides : (multiplier : Int) ∣ secondEuler := by
    refine ⟨(nextMultiplier : Int) +
      secondCentered.value * secondCentered.quotient +
      firstCentered.value * firstCentered.quotient +
      fourthCentered.value * fourthCentered.quotient +
      thirdCentered.value * thirdCentered.quotient, ?_⟩
    unfold secondEuler
    rw [firstCentered.decomposition, secondCentered.decomposition,
      thirdCentered.decomposition, fourthCentered.decomposition]
    calc
      secondCentered.value *
              (secondCentered.value +
                (multiplier : Int) * secondCentered.quotient) +
            firstCentered.value *
              (firstCentered.value +
                (multiplier : Int) * firstCentered.quotient) +
            fourthCentered.value *
              (fourthCentered.value +
                (multiplier : Int) * fourthCentered.quotient) -
            -thirdCentered.value *
              (thirdCentered.value +
                (multiplier : Int) * thirdCentered.quotient) =
          (firstCentered.value ^ 2 + secondCentered.value ^ 2 +
              thirdCentered.value ^ 2 + fourthCentered.value ^ 2) +
            (multiplier : Int) *
              (secondCentered.value * secondCentered.quotient +
                firstCentered.value * firstCentered.quotient +
                fourthCentered.value * fourthCentered.quotient +
                thirdCentered.value * thirdCentered.quotient) := by ring1
      _ = (multiplier : Int) *
          ((nextMultiplier : Int) +
            secondCentered.value * secondCentered.quotient +
            firstCentered.value * firstCentered.quotient +
            fourthCentered.value * fourthCentered.quotient +
            thirdCentered.value * thirdCentered.quotient) := by
        rw [centeredMultiplierCast]
        ring1
  have thirdEulerDivides : (multiplier : Int) ∣ thirdEuler := by
    refine ⟨secondCentered.value * thirdCentered.quotient -
      firstCentered.value * fourthCentered.quotient +
      fourthCentered.value * firstCentered.quotient -
      thirdCentered.value * secondCentered.quotient, ?_⟩
    unfold thirdEuler
    rw [firstCentered.decomposition, secondCentered.decomposition,
      thirdCentered.decomposition, fourthCentered.decomposition]
    ring1
  have fourthEulerDivides : (multiplier : Int) ∣ fourthEuler := by
    refine ⟨secondCentered.value * fourthCentered.quotient +
      firstCentered.value * thirdCentered.quotient -
      fourthCentered.value * secondCentered.quotient -
      thirdCentered.value * firstCentered.quotient, ?_⟩
    unfold fourthEuler
    rw [firstCentered.decomposition, secondCentered.decomposition,
      thirdCentered.decomposition, fourthCentered.decomposition]
    ring1
  let firstQuotient := firstEuler / (multiplier : Int)
  let secondQuotient := secondEuler / (multiplier : Int)
  let thirdQuotient := thirdEuler / (multiplier : Int)
  let fourthQuotient := fourthEuler / (multiplier : Int)
  have firstScaled :
      (multiplier : Int) * firstQuotient = firstEuler := by
    exact (Int.Arithmetic.mul_comm _ _).trans (Int.Division.ediv_mul_cancel firstEulerDivides)
  have secondScaled :
      (multiplier : Int) * secondQuotient = secondEuler := by
    exact (Int.Arithmetic.mul_comm _ _).trans (Int.Division.ediv_mul_cancel secondEulerDivides)
  have thirdScaled :
      (multiplier : Int) * thirdQuotient = thirdEuler := by
    exact (Int.Arithmetic.mul_comm _ _).trans (Int.Division.ediv_mul_cancel thirdEulerDivides)
  have fourthScaled :
      (multiplier : Int) * fourthQuotient = fourthEuler := by
    exact (Int.Arithmetic.mul_comm _ _).trans (Int.Division.ediv_mul_cancel fourthEulerDivides)
  have eulerProduct :
      firstEuler ^ 2 + secondEuler ^ 2 + thirdEuler ^ 2 +
          fourthEuler ^ 2 =
        (firstCentered.value ^ 2 + secondCentered.value ^ 2 +
          thirdCentered.value ^ 2 + fourthCentered.value ^ 2) *
        ((input.first : Int) ^ 2 + (input.second : Int) ^ 2 +
          (input.third : Int) ^ 2 + (input.fourth : Int) ^ 2) := by
    unfold firstEuler secondEuler thirdEuler fourthEuler
    ring1
  have scaledQuotientNorm :
      (multiplier : Int) ^ 2 *
          (firstQuotient ^ 2 + secondQuotient ^ 2 +
            thirdQuotient ^ 2 + fourthQuotient ^ 2) =
        (multiplier : Int) ^ 2 *
          ((nextMultiplier : Int) * (prime : Int)) := by
    calc
      (multiplier : Int) ^ 2 *
            (firstQuotient ^ 2 + secondQuotient ^ 2 +
              thirdQuotient ^ 2 + fourthQuotient ^ 2) =
          firstEuler ^ 2 + secondEuler ^ 2 + thirdEuler ^ 2 +
            fourthEuler ^ 2 := by
        rw [← firstScaled, ← secondScaled, ← thirdScaled,
          ← fourthScaled]
        ring1
      _ = (firstCentered.value ^ 2 + secondCentered.value ^ 2 +
            thirdCentered.value ^ 2 + fourthCentered.value ^ 2) *
          ((input.first : Int) ^ 2 + (input.second : Int) ^ 2 +
            (input.third : Int) ^ 2 + (input.fourth : Int) ^ 2) :=
        eulerProduct
      _ = (multiplier : Int) ^ 2 *
          ((nextMultiplier : Int) * (prime : Int)) := by
        rw [centeredMultiplierCast, inputCast]
        ring1
  have quotientNorm :
      firstQuotient ^ 2 + secondQuotient ^ 2 +
          thirdQuotient ^ 2 + fourthQuotient ^ 2 =
        (nextMultiplier : Int) * (prime : Int) :=
    Int.Arithmetic.eq_of_mul_eq_mul_left (by
      intro squareZero
      have castSquare :
          ((multiplier * multiplier : Nat) : Int) =
            (multiplier : Int) ^ 2 := by
        change (multiplier : Int) * (multiplier : Int) = (multiplier : Int) ^ 2
        rw [Int.Arithmetic.pow_succ, Int.Arithmetic.pow_succ,
          Int.Arithmetic.pow_zero, Int.one_mul]
      rw [← castSquare] at squareZero
      have naturalSquareZero := Int.ofNat.inj squareZero
      exact (Nat.ne_of_gt (Nat.mul_pos multiplierPositive multiplierPositive))
        naturalSquareZero) scaledQuotientNorm
  have naturalQuotientNorm :
      firstQuotient.natAbs ^ 2 + secondQuotient.natAbs ^ 2 +
          thirdQuotient.natAbs ^ 2 + fourthQuotient.natAbs ^ 2 =
        nextMultiplier * prime := by
    apply Int.ofNat.inj
    change (firstQuotient.natAbs : Int) ^ 2 + (secondQuotient.natAbs : Int) ^ 2 +
        (thirdQuotient.natAbs : Int) ^ 2 + (fourthQuotient.natAbs : Int) ^ 2 =
      (nextMultiplier : Int) * (prime : Int)
    exact (congrArg₂ (fun left right : Int => left + right)
      (congrArg₂ (fun left right : Int => left + right)
        (congrArg₂ (fun left right : Int => left + right)
          (Int.Arithmetic.natAbs_pow_two firstQuotient)
          (Int.Arithmetic.natAbs_pow_two secondQuotient))
        (Int.Arithmetic.natAbs_pow_two thirdQuotient))
      (Int.Arithmetic.natAbs_pow_two fourthQuotient)).trans quotientNorm
  exact
    { multiplier := nextMultiplier
      positive := nextPositive
      below := nextBelow
      representation :=
        ⟨firstQuotient.natAbs, secondQuotient.natAbs,
          thirdQuotient.natAbs, fourthQuotient.natAbs,
          naturalQuotientNorm⟩ }

/-- An even four-square sum admits one of the three equal-parity pairings.

Scalar remainder transports retain the original four parity observations.
The sixteen explicit residue tuples either supply a displayed pairing or
contradict the retained zero remainder of the same square sum. -/
theorem four_parity_pairing
    {first second third fourth : Nat}
    (sumEven :
      2 ∣ first ^ 2 + second ^ 2 + third ^ 2 + fourth ^ 2) :
    (first % 2 = second % 2 ∧ third % 2 = fourth % 2) ∨
      (first % 2 = third % 2 ∧ second % 2 = fourth % 2) ∨
      (first % 2 = fourth % 2 ∧ second % 2 = third % 2) := by
  have totalMod := Divisibility.mod_eq_zero_of_dvd sumEven
  have reduceAdd (left right : Nat) :
      (left % 2 + right % 2) % 2 = (left + right) % 2 :=
    (Remainder.Arithmetic.add_mod_right (left % 2) right 2).trans
      (Remainder.Arithmetic.add_mod_left left right 2)
  have firstTwo : (first ^ 2 + second ^ 2) % 2 =
      (first % 2 + second % 2) % 2 :=
    (reduceAdd (first ^ 2) (second ^ 2)).symm.trans
      (congrArg₂ (fun left right : Nat => (left + right) % 2)
        (Parity.square_mod_two first) (Parity.square_mod_two second))
  have firstThree : (first ^ 2 + second ^ 2 + third ^ 2) % 2 =
      (first % 2 + second % 2 + third % 2) % 2 :=
    ((reduceAdd (first ^ 2 + second ^ 2) (third ^ 2)).symm.trans
      (congrArg₂ (fun left right : Nat => (left + right) % 2)
        firstTwo (Parity.square_mod_two third))).trans
      (Remainder.Arithmetic.add_mod_left (first % 2 + second % 2) (third % 2) 2)
  have allFour : (first ^ 2 + second ^ 2 + third ^ 2 + fourth ^ 2) % 2 =
      (first % 2 + second % 2 + third % 2 + fourth % 2) % 2 :=
    ((reduceAdd (first ^ 2 + second ^ 2 + third ^ 2) (fourth ^ 2)).symm.trans
      (congrArg₂ (fun left right : Nat => (left + right) % 2)
        firstThree (Parity.square_mod_two fourth))).trans
      (Remainder.Arithmetic.add_mod_left
        (first % 2 + second % 2 + third % 2) (fourth % 2) 2)
  have retainedParity : (first % 2 + second % 2 + third % 2 + fourth % 2) % 2 = 0 :=
    allFour.symm.trans totalMod
  cases Parity.consecutive first with
  | inl firstParity =>
      cases Parity.consecutive second with
      | inl secondParity =>
          cases Parity.consecutive third with
          | inl thirdParity =>
              cases Parity.consecutive fourth with
              | inl fourthParity =>
                  exact Or.inl ⟨firstParity.1.trans secondParity.1.symm, thirdParity.1.trans fourthParity.1.symm⟩
              | inr fourthParity =>
                  have impossible := retainedParity
                  rw [firstParity.1, secondParity.1, thirdParity.1, fourthParity.1] at impossible
                  exact Nat.noConfusion impossible
          | inr thirdParity =>
              cases Parity.consecutive fourth with
              | inl fourthParity =>
                  have impossible := retainedParity
                  rw [firstParity.1, secondParity.1, thirdParity.1, fourthParity.1] at impossible
                  exact Nat.noConfusion impossible
              | inr fourthParity =>
                  exact Or.inl ⟨firstParity.1.trans secondParity.1.symm, thirdParity.1.trans fourthParity.1.symm⟩
      | inr secondParity =>
          cases Parity.consecutive third with
          | inl thirdParity =>
              cases Parity.consecutive fourth with
              | inl fourthParity =>
                  have impossible := retainedParity
                  rw [firstParity.1, secondParity.1, thirdParity.1, fourthParity.1] at impossible
                  exact Nat.noConfusion impossible
              | inr fourthParity =>
                  exact Or.inr (Or.inl ⟨firstParity.1.trans thirdParity.1.symm, secondParity.1.trans
                    fourthParity.1.symm⟩)
          | inr thirdParity =>
              cases Parity.consecutive fourth with
              | inl fourthParity =>
                  exact Or.inr (Or.inr ⟨firstParity.1.trans fourthParity.1.symm, secondParity.1.trans
                    thirdParity.1.symm⟩)
              | inr fourthParity =>
                  have impossible := retainedParity
                  rw [firstParity.1, secondParity.1, thirdParity.1, fourthParity.1] at impossible
                  exact Nat.noConfusion impossible
  | inr firstParity =>
      cases Parity.consecutive second with
      | inl secondParity =>
          cases Parity.consecutive third with
          | inl thirdParity =>
              cases Parity.consecutive fourth with
              | inl fourthParity =>
                  have impossible := retainedParity
                  rw [firstParity.1, secondParity.1, thirdParity.1, fourthParity.1] at impossible
                  exact Nat.noConfusion impossible
              | inr fourthParity =>
                  exact Or.inr (Or.inr ⟨firstParity.1.trans fourthParity.1.symm, secondParity.1.trans
                    thirdParity.1.symm⟩)
          | inr thirdParity =>
              cases Parity.consecutive fourth with
              | inl fourthParity =>
                  exact Or.inr (Or.inl ⟨firstParity.1.trans thirdParity.1.symm, secondParity.1.trans
                    fourthParity.1.symm⟩)
              | inr fourthParity =>
                  have impossible := retainedParity
                  rw [firstParity.1, secondParity.1, thirdParity.1, fourthParity.1] at impossible
                  exact Nat.noConfusion impossible
      | inr secondParity =>
          cases Parity.consecutive third with
          | inl thirdParity =>
              cases Parity.consecutive fourth with
              | inl fourthParity =>
                  exact Or.inl ⟨firstParity.1.trans secondParity.1.symm, thirdParity.1.trans fourthParity.1.symm⟩
              | inr fourthParity =>
                  have impossible := retainedParity
                  rw [firstParity.1, secondParity.1, thirdParity.1, fourthParity.1] at impossible
                  exact Nat.noConfusion impossible
          | inr thirdParity =>
              cases Parity.consecutive fourth with
              | inl fourthParity =>
                  have impossible := retainedParity
                  rw [firstParity.1, secondParity.1, thirdParity.1, fourthParity.1] at impossible
                  exact Nat.noConfusion impossible
              | inr fourthParity =>
                  exact Or.inl ⟨firstParity.1.trans secondParity.1.symm, thirdParity.1.trans fourthParity.1.symm⟩

/-- An explicit even natural decomposition gives divisibility by two.

The retained half in the original addition equation supplies the natural
factor after direct transport through the doubled-product identity. -/
theorem two_dvd_of_even {value : Nat} (valueEven : Parity.Even value) :
    2 ∣ value := by
  rcases valueEven with ⟨half, equation⟩
  exact ⟨half, equation.trans (Nat.two_mul half).symm⟩

/-- Halve four retained roots using two same-parity pairs.

The original signed half-differences and half-sums divide by integer two.
Their unchanged natural magnitudes satisfy the exact target square sum,
using the supplied twice-target equation and the two retained parity proofs. -/
@[expose] def halvePairedFourSquaresData
    (target first second third fourth : Nat)
    (equation :
      first ^ 2 + second ^ 2 + third ^ 2 + fourth ^ 2 = 2 * target)
    (firstPair : first % 2 = second % 2)
    (secondPair : third % 2 = fourth % 2) :
    Basic.Representation target := by
  let firstHalf : Int := ((first : Int) - (second : Int)) / 2
  let secondHalf : Int := ((first : Int) + (second : Int)) / 2
  let thirdHalf : Int := ((third : Int) - (fourth : Int)) / 2
  let fourthHalf : Int := ((third : Int) + (fourth : Int)) / 2
  have firstDifferenceDivides :
      (2 : Int) ∣ (first : Int) - (second : Int) :=
    Int.Parity.two_dvd_int_sub_of_same_parity firstPair
  have firstSumDivides :
      (2 : Int) ∣ (first : Int) + (second : Int) :=
    Int.Parity.two_dvd_int_add_of_same_parity firstPair
  have secondDifferenceDivides :
      (2 : Int) ∣ (third : Int) - (fourth : Int) :=
    Int.Parity.two_dvd_int_sub_of_same_parity secondPair
  have secondSumDivides :
      (2 : Int) ∣ (third : Int) + (fourth : Int) :=
    Int.Parity.two_dvd_int_add_of_same_parity secondPair
  have firstScaled : 2 * firstHalf = (first : Int) - (second : Int) :=
    (Int.Arithmetic.mul_comm _ _).trans (Int.Division.ediv_mul_cancel firstDifferenceDivides)
  have secondScaled : 2 * secondHalf = (first : Int) + (second : Int) :=
    (Int.Arithmetic.mul_comm _ _).trans (Int.Division.ediv_mul_cancel firstSumDivides)
  have thirdScaled : 2 * thirdHalf = (third : Int) - (fourth : Int) :=
    (Int.Arithmetic.mul_comm _ _).trans (Int.Division.ediv_mul_cancel secondDifferenceDivides)
  have fourthScaled : 2 * fourthHalf = (third : Int) + (fourth : Int) :=
    (Int.Arithmetic.mul_comm _ _).trans (Int.Division.ediv_mul_cancel secondSumDivides)
  have equationCast :
      (first : Int) ^ 2 + (second : Int) ^ 2 +
          (third : Int) ^ 2 + (fourth : Int) ^ 2 =
        2 * (target : Int) := by
    have castEquation :=
      congrArg (fun value : Nat => (value : Int)) equation
    exact castEquation
  have scaledNorm :
      (4 : Int) *
          (firstHalf ^ 2 + secondHalf ^ 2 +
            thirdHalf ^ 2 + fourthHalf ^ 2) =
        (4 : Int) * (target : Int) := by
    calc
      (4 : Int) *
            (firstHalf ^ 2 + secondHalf ^ 2 +
              thirdHalf ^ 2 + fourthHalf ^ 2) =
          (2 * firstHalf) ^ 2 + (2 * secondHalf) ^ 2 +
            (2 * thirdHalf) ^ 2 + (2 * fourthHalf) ^ 2 := by ring1
      _ = ((first : Int) - (second : Int)) ^ 2 +
            ((first : Int) + (second : Int)) ^ 2 +
            ((third : Int) - (fourth : Int)) ^ 2 +
            ((third : Int) + (fourth : Int)) ^ 2 := by
        rw [firstScaled, secondScaled, thirdScaled, fourthScaled]
      _ =
          2 * ((first : Int) ^ 2 + (second : Int) ^ 2 +
            (third : Int) ^ 2 + (fourth : Int) ^ 2) := by
        ring1
      _ = (4 : Int) * (target : Int) := by
        rw [equationCast]
        ring1
  have halfNorm :
      firstHalf ^ 2 + secondHalf ^ 2 +
          thirdHalf ^ 2 + fourthHalf ^ 2 = (target : Int) :=
    Int.Arithmetic.eq_of_mul_eq_mul_left (by decide : (4 : Int) ≠ 0) scaledNorm
  have naturalHalfNorm :
      firstHalf.natAbs ^ 2 + secondHalf.natAbs ^ 2 +
          thirdHalf.natAbs ^ 2 + fourthHalf.natAbs ^ 2 = target := by
    apply Int.ofNat.inj
    change (firstHalf.natAbs : Int) ^ 2 + (secondHalf.natAbs : Int) ^ 2 +
        (thirdHalf.natAbs : Int) ^ 2 + (fourthHalf.natAbs : Int) ^ 2 = (target : Int)
    exact (congrArg₂ (fun left right : Int => left + right)
      (congrArg₂ (fun left right : Int => left + right)
        (congrArg₂ (fun left right : Int => left + right)
          (Int.Arithmetic.natAbs_pow_two firstHalf)
          (Int.Arithmetic.natAbs_pow_two secondHalf))
        (Int.Arithmetic.natAbs_pow_two thirdHalf))
      (Int.Arithmetic.natAbs_pow_two fourthHalf)).trans halfNorm
  exact
    ⟨firstHalf.natAbs, secondHalf.natAbs, thirdHalf.natAbs,
      fourthHalf.natAbs, naturalHalfNorm⟩

/-- Compute the original even-multiplier descent step.

The original quotient by two gives the smaller positive multiplier. The
same two parity comparisons select one of the three retained root orders
for the unchanged half-sum and half-difference construction. -/
@[expose] def evenDescentStep (prime multiplier : Nat)
    (multiplierPositive : 0 < multiplier)
    (multiplierEven : Parity.Even multiplier)
    (input : Basic.Representation (multiplier * prime)) :
    DescentStep multiplier prime := by
  let halfMultiplier := multiplier / 2
  have twoDivides : 2 ∣ multiplier := two_dvd_of_even multiplierEven
  have halfEquation : halfMultiplier * 2 = multiplier :=
    Division.div_mul_cancel twoDivides
  have halfPositive : 0 < halfMultiplier :=
    Division.div_pos (Divisibility.le_of_dvd multiplierPositive twoDivides) (by decide)
  have halfBelow : halfMultiplier < multiplier :=
    Division.div_lt_self multiplierPositive (by decide)
  have pairedTargetEquation :
      input.first ^ 2 + input.second ^ 2 +
          input.third ^ 2 + input.fourth ^ 2 =
        2 * (halfMultiplier * prime) := by
    calc
      input.first ^ 2 + input.second ^ 2 +
            input.third ^ 2 + input.fourth ^ 2 =
          multiplier * prime := input.equation
      _ = 2 * (halfMultiplier * prime) := by
        rw [← halfEquation]
        ring1
  have sumEven :
      2 ∣ input.first ^ 2 + input.second ^ 2 +
        input.third ^ 2 + input.fourth ^ 2 :=
    ⟨halfMultiplier * prime, pairedTargetEquation⟩
  have pairing := four_parity_pairing sumEven
  by_cases firstSecond : input.first % 2 = input.second % 2
  · have thirdFourth : input.third % 2 = input.fourth % 2 := by
      rcases pairing with direct | cross | cross
      · exact direct.2
      · exact cross.1.symm.trans (firstSecond.trans cross.2)
      · exact cross.2.symm.trans (firstSecond.symm.trans cross.1)
    exact
      { multiplier := halfMultiplier
        positive := halfPositive
        below := halfBelow
        representation := halvePairedFourSquaresData
          (halfMultiplier * prime) input.first input.second input.third
          input.fourth pairedTargetEquation firstSecond thirdFourth }
  · by_cases firstThird : input.first % 2 = input.third % 2
    · have secondFourth : input.second % 2 = input.fourth % 2 := by
        rcases pairing with direct | cross | cross
        · exact False.elim (firstSecond direct.1)
        · exact cross.2
        · exact False.elim (firstSecond (firstThird.trans cross.2.symm))
      have reorderedEquation :
          input.first ^ 2 + input.third ^ 2 +
              input.second ^ 2 + input.fourth ^ 2 =
            2 * (halfMultiplier * prime) := by
        rw [← pairedTargetEquation]
        ring1
      exact
        { multiplier := halfMultiplier
          positive := halfPositive
          below := halfBelow
          representation := halvePairedFourSquaresData
            (halfMultiplier * prime) input.first input.third input.second
            input.fourth reorderedEquation firstThird secondFourth }
    · have firstFourth : input.first % 2 = input.fourth % 2 := by
        rcases pairing with direct | cross | cross
        · exact False.elim (firstSecond direct.1)
        · exact False.elim (firstThird cross.1)
        · exact cross.1
      have secondThird : input.second % 2 = input.third % 2 := by
        rcases pairing with direct | cross | cross
        · exact False.elim (firstSecond direct.1)
        · exact False.elim (firstThird cross.1)
        · exact cross.2
      have reorderedEquation :
          input.first ^ 2 + input.fourth ^ 2 +
              input.second ^ 2 + input.third ^ 2 =
            2 * (halfMultiplier * prime) := by
        rw [← pairedTargetEquation]
        ring1
      exact
        { multiplier := halfMultiplier
          positive := halfPositive
          below := halfBelow
          representation := halvePairedFourSquaresData
            (halfMultiplier * prime) input.first input.fourth input.second
            input.third reorderedEquation firstFourth secondThird }

/-- Descend a retained represented prime multiple to the prime itself.

The same multiplier-one check terminates the computation. Otherwise its
original remainder modulo two selects the even or odd step, whose retained
strict multiplier bound controls the unchanged well-founded recursion. -/
@[expose] def descendPrime (prime : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (multiplier : Nat) (multiplierPositive : 0 < multiplier)
    (multiplierBelowPrime : multiplier < prime)
    (input : Basic.Representation (multiplier * prime)) :
    Basic.Representation prime := by
  by_cases multiplierOne : multiplier = 1
  · subst multiplier
    rw [Nat.one_mul] at input
    exact input
  · have multiplierGreaterOne : 1 < multiplier :=
      Nat.lt_of_le_of_ne (Nat.succ_le_of_lt multiplierPositive) (Ne.symm multiplierOne)
    by_cases remainderZero : multiplier % 2 = 0
    · have multiplierEven : Parity.Even multiplier := by
        refine ⟨multiplier / 2, ?_⟩
        have divisionEquation := Division.mod_add_div multiplier 2
        rw [remainderZero, Nat.zero_add] at divisionEquation
        exact divisionEquation.symm.trans (Nat.two_mul _)
      let next := evenDescentStep prime multiplier multiplierPositive
        multiplierEven input
      exact Purelib.NumberTheory.FourSquares.Descent.descendPrime prime primeIsPrime next.multiplier next.positive
        (Nat.lt_trans next.below multiplierBelowPrime) next.representation
    · have multiplierOdd : Parity.Odd multiplier :=
        ⟨multiplier / 2, by
          have remainderOne : multiplier % 2 = 1 := by
            cases Parity.consecutive multiplier with
            | inl even => exact (remainderZero even.1).elim
            | inr odd => exact odd.1
          have divisionEquation := Division.mod_add_div multiplier 2
          rw [remainderOne] at divisionEquation
          exact divisionEquation.symm.trans (Nat.add_comm _ _)⟩
      let next := oddDescentStep prime multiplier primeIsPrime
        multiplierPositive multiplierBelowPrime multiplierGreaterOne
        multiplierOdd input
      exact Purelib.NumberTheory.FourSquares.Descent.descendPrime prime primeIsPrime next.multiplier next.positive
        (Nat.lt_trans next.below multiplierBelowPrime) next.representation
termination_by multiplier
decreasing_by
  · exact next.below
  · exact next.below

/-- Construct the retained four-square representation of a natural prime.

The original prime seed supplies its bounded positive multiplier and
representation. The same multiplier descent returns four roots at the
original prime index. -/
@[expose] def primeRepresentation (prime : Nat) (primeIsPrime : NumberTheory.Prime prime) :
    Basic.Representation prime := by
  let initial := PrimeSeed.primeInitialMultiple prime primeIsPrime
  exact descendPrime prime primeIsPrime initial.multiplier initial.positive
    initial.below initial.representation
end Purelib.NumberTheory.FourSquares.Descent

end
