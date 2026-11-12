module
import Purelib.Data.Nat.Order
import Purelib.Algebra.Binomial.Parity
import Purelib.Algebra.Semiring.Normalization
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Algebra.Quadratic.Pair.FiniteSum
import Purelib.Data.Nat.Choose
public import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Formula
import Purelib.Polynomial.Recurrence.Spread.QuadraticPair

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Choose.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Algebra

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: odd spread-polynomial squares

Exercise 8.7 is proved in two nested executable quadratic-pair rings.  They
adjoin only the two formal relations needed by the finite binomial argument;
no root is selected in the coefficient field.
-/

namespace Purelib.Polynomial.Recurrence.Spread.OddSquare

variable {K : Type*} [ExplicitField K]

/-- A term of the finite odd-binomial factor of a spread polynomial.

It combines the odd binomial coefficient with powers of minus the argument and its complement. -/
def oddSpreadRootTerm
    (half : Nat) (value : K) (index : Nat) : K :=
  (-value) ^ index * (1 - value) ^ (half - index) *
    ((half + half + 1).choose (index + index + 1) : K)

/-- The finite odd-binomial polynomial whose square factors an odd-index spread.

The requested half-index determines exactly half plus one terms. -/
def oddSpreadRootExpansion (half : Nat) (value : K) : K :=
  FiniteSum.Prefix.prefixSum (half + 1) (oddSpreadRootTerm half value)

/-- The last displayed term is exactly `(-s)^l`. -/
theorem oddSpreadRootTerm_last (half : Nat) (value : K) :
    oddSpreadRootTerm half value half = (-value) ^ half := open Purelib in by
  unfold oddSpreadRootTerm
  rw [Nat.sub_self,
    show half + half + 1 = half + half + 1 by rfl,
    Data.Nat.Choose.choose_self, pow_zero, Nat.cast_one]
  ring1
section ExerciseEightSeven

section
open Purelib
/-- Even powers of the inner quadratic generator embed powers of the spread complement. -/
private theorem
  innerGenerator_even_power
    (value : K) (index : Nat) :
    let generator :=
      Quadratic.Pair.generator (K := K)
        (radialSquare := value - 1)
    generator ^ (index + index) =
      Quadratic.Pair.scalar
        (radialSquare := value - 1) ((1 - value) ^ index) := by
  dsimp only
  calc
    Quadratic.Pair.generator (K := K)
          (radialSquare := value - 1) ^ (index + index) =
        Quadratic.Pair.scalar ((-(value - 1)) ^ index) :=
      Quadratic.Pair.generator_even_power index
    _ = Quadratic.Pair.scalar ((1 - value) ^ index) := by
      congr 1
      congr 1
      ring1
/-- Convert a nested quadratic-pair odd-binomial term to its scalar spread term.

The bounded term index permits the remaining exponent to split into two equal natural powers. -/
private theorem
  antisymmetricTerm_nested
    (half index : Nat) (value : K) (indexBound : index < half + 1) :
    let innerScalar :=
      Quadratic.Pair.scalar (radialSquare := value - 1)
    let innerGenerator :=
      Quadratic.Pair.generator (K := K)
        (radialSquare := value - 1)
    let outerScalar :=
      Quadratic.Pair.scalar
        (radialSquare := innerScalar value)
    let outerGenerator :=
      Quadratic.Pair.generator
        (K := Quadratic.Pair K (value - 1))
        (radialSquare := innerScalar value)
    outerGenerator ^ (index + index) *
          (outerScalar innerGenerator) ^
            (half + half + 1 - (index + index + 1)) *
        ((half + half + 1).choose (index + index + 1) :
          Quadratic.Pair
            (Quadratic.Pair K (value - 1)) (innerScalar value)) =
      outerScalar (innerScalar (oddSpreadRootTerm half value index)) := by
  dsimp only
  let innerScalar :=
    Quadratic.Pair.scalar (radialSquare := value - 1)
  let innerGenerator :=
    Quadratic.Pair.generator (K := K)
      (radialSquare := value - 1)
  let outerScalar :=
    Quadratic.Pair.scalar (radialSquare := innerScalar value)
  let outerGenerator :=
    Quadratic.Pair.generator
      (K := Quadratic.Pair K (value - 1))
      (radialSquare := innerScalar value)
  have outerEvenPower :
      outerGenerator ^ (index + index) =
        outerScalar (innerScalar ((-value) ^ index)) := by
    calc
      outerGenerator ^ (index + index) =
          outerScalar ((-innerScalar value) ^ index) :=
        Quadratic.Pair.generator_even_power index
      _ = outerScalar (innerScalar ((-value) ^ index)) := by
        rw [← Quadratic.Pair.scalar_neg,
          ← Quadratic.Pair.scalar_pow]
  have exponentEquation :
      half + half + 1 - (index + index + 1) =
        (half - index) + (half - index) := by omega0
  have centerPower :
      (outerScalar innerGenerator) ^
          (half + half + 1 - (index + index + 1)) =
        outerScalar (innerScalar ((1 - value) ^ (half - index))) := by
    rw [exponentEquation]
    rw [← Quadratic.Pair.scalar_pow]
    rw [innerGenerator_even_power]
  have coefficientCast :
      ((half + half + 1).choose (index + index + 1) :
          Quadratic.Pair
            (Quadratic.Pair K (value - 1)) (innerScalar value)) =
        outerScalar (innerScalar
          ((half + half + 1).choose (index + index + 1) : K)) := by
    rw [Quadratic.Pair.natCast_eq_scalar,
      Quadratic.Pair.natCast_eq_scalar]
  rw [outerEvenPower, centerPower, coefficientCast]
  unfold oddSpreadRootTerm
  rw [← Quadratic.Pair.scalar_mul,
    ← Quadratic.Pair.scalar_mul]
  congr 1
  rw [← Quadratic.Pair.scalar_mul,
    ← Quadratic.Pair.scalar_mul]
end

open Purelib.Data.Nat in
attribute [local instance 2000] successorNeZero in
/-- Every odd-index spread is its argument times a finite polynomial square.

The square factor is the explicit odd-binomial prefix; two must be nonzero in the supplied explicit field. -/
theorem ExerciseEightSeven.exercise_8_7
    (half : Nat) (value : K) (twoNonzero : (2 : K) ≠ 0) :
    Basic.spreadPolynomial (half + half + 1) value =
      value * oddSpreadRootExpansion half value ^ 2 := open Purelib in by
  let innerScalar :=
    Quadratic.Pair.scalar (radialSquare := value - 1)
  let innerGenerator :=
    Quadratic.Pair.generator (K := K)
      (radialSquare := value - 1)
  let outerScalar :=
    Quadratic.Pair.scalar (radialSquare := innerScalar value)
  let outerGenerator :=
    Quadratic.Pair.generator
      (K := Quadratic.Pair K (value - 1))
      (radialSquare := innerScalar value)
  let embeddedValue := outerScalar (innerScalar value)
  let embeddedRoot :=
    outerScalar (innerScalar (oddSpreadRootExpansion half value))
  let positive := outerScalar innerGenerator + outerGenerator
  let negative := outerScalar innerGenerator - outerGenerator
  let offset := 2 * outerScalar innerGenerator * outerGenerator
  have innerSquare : innerGenerator ^ 2 = innerScalar (1 - value) := by
    unfold innerGenerator innerScalar
    calc
      Quadratic.Pair.generator (K := K)
            (radialSquare := value - 1) ^ 2 =
          Quadratic.Pair.scalar ((1 - value) ^ 1) := by
            simpa only [show 1 + 1 = 2 by omega0] using
              innerGenerator_even_power
                value 1
      _ = Quadratic.Pair.scalar (1 - value) := by rw [pow_one]
  have outerSquare : outerGenerator ^ 2 = -embeddedValue := by
    unfold outerGenerator embeddedValue outerScalar
    calc
      Quadratic.Pair.generator
            (K := Quadratic.Pair K (value - 1))
            (radialSquare := innerScalar value) ^ 2 =
          outerScalar (-innerScalar value) :=
        Quadratic.Pair.generator_square
      _ = -outerScalar (innerScalar value) := by
        exact Quadratic.Pair.scalar_neg (innerScalar value)
  have embeddedInnerSquare :
      (outerScalar innerGenerator) ^ 2 = 1 - embeddedValue := by
    rw [← Quadratic.Pair.scalar_pow, innerSquare]
    unfold embeddedValue
    rw [← Quadratic.Pair.scalar_one,
      ← Quadratic.Pair.scalar_one,
      ← Quadratic.Pair.scalar_sub,
      ← Quadratic.Pair.scalar_sub]
  have positiveNegative : positive * negative = 1 := by
    unfold positive negative
    calc
      (outerScalar innerGenerator + outerGenerator) *
          (outerScalar innerGenerator - outerGenerator) =
        (outerScalar innerGenerator) ^ 2 - outerGenerator ^ 2 := by ring1
      _ = (1 - embeddedValue) - (-embeddedValue) := by
        rw [embeddedInnerSquare, outerSquare]
      _ = 1 := by ring1
  have powerProduct :
      positive ^ (half + half + 1) *
          negative ^ (half + half + 1) = 1 := by
    rw [← Semiring.Normalization.product_pow, positiveNegative, one_pow]
  have antisymmetricRaw := Binomial.Parity.antisymmetric_binomial_odd half
    (outerScalar innerGenerator) outerGenerator
  have antisymmetricTerms :
      FiniteSum.Prefix.prefixSum (half + 1) (fun index =>
          outerGenerator ^ (index + index) *
            (outerScalar innerGenerator) ^
              (half + half + 1 - (index + index + 1)) *
              ((half + half + 1).choose (index + index + 1) :
                Quadratic.Pair
                  (Quadratic.Pair K (value - 1))
                  (innerScalar value))) = embeddedRoot := by
    unfold embeddedRoot oddSpreadRootExpansion
    calc
      FiniteSum.Prefix.prefixSum (half + 1) (fun index =>
          outerGenerator ^ (index + index) *
            (outerScalar innerGenerator) ^
              (half + half + 1 - (index + index + 1)) *
              ((half + half + 1).choose (index + index + 1) :
                Quadratic.Pair
                  (Quadratic.Pair K (value - 1))
                  (innerScalar value))) =
        FiniteSum.Prefix.prefixSum (half + 1) (fun index =>
          outerScalar (innerScalar (oddSpreadRootTerm half value index))) := by
            apply FiniteSum.Prefix.prefixSum_congr
            intro index indexBound
            exact antisymmetricTerm_nested
              half index value indexBound
      _ = outerScalar (FiniteSum.Prefix.prefixSum (half + 1) (fun index =>
          innerScalar (oddSpreadRootTerm half value index))) :=
        Quadratic.Pair.FiniteSum.prefixSum_quadraticPair_scalar
          (innerScalar value) (half + 1) _
      _ = outerScalar (innerScalar (FiniteSum.Prefix.prefixSum (half + 1)
          (oddSpreadRootTerm half value))) := by
            rw [Quadratic.Pair.FiniteSum.prefixSum_quadraticPair_scalar]
  have antisymmetric :
      positive ^ (half + half + 1) -
          negative ^ (half + half + 1) =
        2 * outerGenerator * embeddedRoot := by
    unfold positive negative
    rw [antisymmetricTerms] at antisymmetricRaw
    exact antisymmetricRaw
  have offsetSquare :
      offset ^ 2 = -(4 * embeddedValue * (1 - embeddedValue)) := by
    unfold offset
    calc
      (2 * outerScalar innerGenerator * outerGenerator) ^ 2 =
          4 * (outerScalar innerGenerator) ^ 2 *
            outerGenerator ^ 2 := by ring1
      _ = 4 * (1 - embeddedValue) * (-embeddedValue) := by
        rw [embeddedInnerSquare, outerSquare]
      _ = -(4 * embeddedValue * (1 - embeddedValue)) := by ring1
  have positiveSquare :
      positive ^ 2 = 1 - 2 * embeddedValue + offset := by
    unfold positive offset
    have squareExpansion :
        (outerScalar innerGenerator + outerGenerator) ^ 2 =
          (outerScalar innerGenerator) ^ 2 +
            2 * outerScalar innerGenerator * outerGenerator + outerGenerator ^ 2 := by ring1
    rw [squareExpansion]
    rw [embeddedInnerSquare, outerSquare]
    ring1
  have negativeSquare :
      negative ^ 2 = 1 - 2 * embeddedValue - offset := by
    unfold negative offset
    have squareExpansion :
        (outerScalar innerGenerator - outerGenerator) ^ 2 =
          (outerScalar innerGenerator) ^ 2 -
            2 * outerScalar innerGenerator * outerGenerator + outerGenerator ^ 2 := by ring1
    rw [squareExpansion]
    rw [embeddedInnerSquare, outerSquare]
    ring1
  have positiveEvenPower :
      (1 - 2 * embeddedValue + offset) ^ (half + half + 1) =
        positive ^ ((half + half + 1) + (half + half + 1)) := by
    rw [← positiveSquare, ← pow_mul]
    congr 1
    omega0
  have negativeEvenPower :
      (1 - 2 * embeddedValue - offset) ^ (half + half + 1) =
        negative ^ ((half + half + 1) + (half + half + 1)) := by
    rw [← negativeSquare, ← pow_mul]
    congr 1
    omega0
  have embeddedSpread :
      Basic.spreadPolynomial (half + half + 1) embeddedValue =
        outerScalar (innerScalar
          (Basic.spreadPolynomial (half + half + 1) value)) := by
    unfold embeddedValue
    rw [QuadraticPair.spreadPolynomial_quadraticPair_scalar,
      QuadraticPair.spreadPolynomial_quadraticPair_scalar]
  have spreadFormula := Formula.spread_polynomial_offset_formula_cleared
    embeddedValue offset offsetSquare (half + half + 1)
  rw [positiveEvenPower, negativeEvenPower, embeddedSpread] at spreadFormula
  have positivePowerSquare :
      (positive ^ (half + half + 1)) ^ 2 =
        positive ^ ((half + half + 1) + (half + half + 1)) := by
    rw [pow_two, ← pow_add]
  have negativePowerSquare :
      (negative ^ (half + half + 1)) ^ 2 =
        negative ^ ((half + half + 1) + (half + half + 1)) := by
    rw [pow_two, ← pow_add]
  have embeddedEquation :
      4 * outerScalar (innerScalar
          (Basic.spreadPolynomial (half + half + 1) value)) =
        4 * embeddedValue * embeddedRoot ^ 2 := by
    calc
      4 * outerScalar (innerScalar
          (Basic.spreadPolynomial (half + half + 1) value)) =
        2 - positive ^ ((half + half + 1) + (half + half + 1)) -
          negative ^ ((half + half + 1) + (half + half + 1)) :=
            spreadFormula
      _ = -(positive ^ (half + half + 1) -
          negative ^ (half + half + 1)) ^ 2 := by
            rw [← positivePowerSquare, ← negativePowerSquare]
            calc
              2 - (positive ^ (half + half + 1)) ^ 2 -
                    (negative ^ (half + half + 1)) ^ 2 =
                  2 * (positive ^ (half + half + 1) *
                      negative ^ (half + half + 1)) -
                    (positive ^ (half + half + 1)) ^ 2 -
                    (negative ^ (half + half + 1)) ^ 2 := by
                      rw [powerProduct]
                      generalize positive ^ (half + half + 1) = positivePower
                      generalize negative ^ (half + half + 1) = negativePower
                      ring1
              _ = -(positive ^ (half + half + 1) -
                  negative ^ (half + half + 1)) ^ 2 := by
                    generalize positive ^ (half + half + 1) = positivePower
                    generalize negative ^ (half + half + 1) = negativePower
                    ring1
      _ = -(2 * outerGenerator * embeddedRoot) ^ 2 := by
            rw [antisymmetric]
      _ = 4 * embeddedValue * embeddedRoot ^ 2 := by
            calc
              -(2 * outerGenerator * embeddedRoot) ^ 2 =
                  -4 * outerGenerator ^ 2 * embeddedRoot ^ 2 := by ring1
              _ = 4 * embeddedValue * embeddedRoot ^ 2 := by
                rw [outerSquare]
                ring1
  have embeddedRootSquare :
      embeddedRoot ^ 2 = outerScalar (innerScalar
        (oddSpreadRootExpansion half value ^ 2)) := by
    unfold embeddedRoot
    rw [← Quadratic.Pair.scalar_pow,
      ← Quadratic.Pair.scalar_pow]
  rw [embeddedRootSquare] at embeddedEquation
  rw [Quadratic.Pair.four_eq_scalar] at embeddedEquation
  rw [← Quadratic.Pair.scalar_mul,
    ← Quadratic.Pair.scalar_mul] at embeddedEquation
  have innerEquation := congrArg Quadratic.Pair.re embeddedEquation
  simp only [Quadratic.Pair.scalar_re] at innerEquation
  rw [Quadratic.Pair.four_eq_scalar] at innerEquation
  rw [← Quadratic.Pair.scalar_mul,
    ← Quadratic.Pair.scalar_mul] at innerEquation
  have baseEquation := congrArg Quadratic.Pair.re innerEquation
  unfold innerScalar at baseEquation
  have scalarSubZero (scalar : K) : scalar - 0 = scalar := by ring1
  simp only [Quadratic.Pair.mul_re, Quadratic.Pair.scalar_re,
    Quadratic.Pair.scalar_im, mul_zero, scalarSubZero, -eq_self, -iff_self] at baseEquation
  have fourNonzero : (4 : K) ≠ 0 := by
    intro fourZero
    have twoProductZero : (2 : K) * 2 = 0 := by
      calc
        (2 : K) * 2 = 4 := by ring1
        _ = 0 := fourZero
    exact (ExplicitField.mul_ne_zero twoNonzero twoNonzero)
      twoProductZero
  apply ExplicitField.eq_of_mul_eq_mul_left fourNonzero
  calc
    4 * Basic.spreadPolynomial (half + half + 1) value =
        4 * value * oddSpreadRootExpansion half value ^ 2 := baseEquation
    _ = 4 * (value * oddSpreadRootExpansion half value ^ 2) := by ring1

end ExerciseEightSeven

end Purelib.Polynomial.Recurrence.Spread.OddSquare

end
