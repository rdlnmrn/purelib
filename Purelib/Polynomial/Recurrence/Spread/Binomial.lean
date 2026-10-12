module
import Purelib.Algebra.Binomial.Parity
import Purelib.Algebra.NatCast
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Algebra.Quadratic.Pair.FiniteSum
import Purelib.Data.Nat.Choose
import Purelib.Polynomial.Recurrence.Chebyshev.First.Basic
import Purelib.Polynomial.Recurrence.Chebyshev.First.QuadraticPair
public import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Chebyshev

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
# Divine Proportions, Chapter 8: the alternating binomial formula

Exercise 8.6 is proved by expanding the two finite powers in Theorem 59 and
pairing their even and odd terms.  Every sum below has an explicit natural
bound and is implemented by primitive recursion.
-/

namespace Purelib.Polynomial.Recurrence.Spread.Binomial

variable {K : Type*} [ExplicitField K]

/-- An alternating even-binomial term for a spread expansion.

The index chooses an even binomial coefficient, a power of the negative radial square, and the remaining center power.
-/
def spreadBinomialTerm
    (exponent : Nat) (center radialSquare : K) (index : Nat) : K :=
  (-radialSquare) ^ index *
    center ^ (exponent - (index + index)) *
      (exponent.choose (index + index) : K)

/-- A finite prefix of alternating even-binomial terms.

The exponent and requested term count are explicit natural inputs. -/
def spreadBinomialExpansion
    (exponent termCount : Nat) (center radialSquare : K) : K :=
  FiniteSum.Prefix.prefixSum termCount
    (Recurrence.Spread.Binomial.spreadBinomialTerm exponent center radialSquare)

/-- An even quadratic-pair binomial term is the scalar embedding of the spread term.

The pair generator squares to minus the supplied radial parameter. -/
private theorem
  binomialTerm_quadraticPair
    (exponent index : Nat) (center radialSquare : K) :
    Purelib.Algebra.Binomial.binomialTerm exponent
        (Algebra.Quadratic.Pair.scalar (radialSquare := radialSquare) center)
        (Algebra.Quadratic.Pair.generator (K := K)
          (radialSquare := radialSquare))
        (index + index) =
      Algebra.Quadratic.Pair.scalar
        (Recurrence.Spread.Binomial.spreadBinomialTerm exponent center radialSquare index) := open Purelib in by
  unfold Binomial.binomialTerm Recurrence.Spread.Binomial.spreadBinomialTerm
  rw [Algebra.Quadratic.Pair.generator_even_power]
  rw [← Algebra.Quadratic.Pair.scalar_pow]
  rw [Algebra.Quadratic.Pair.natCast_eq_scalar]
  rw [← Algebra.Quadratic.Pair.scalar_mul,
    ← Algebra.Quadratic.Pair.scalar_mul]

open Purelib in
/-- A symmetric quadratic-pair power expansion gives a Chebyshev expansion.

The radial parameter equals one minus the center square, and two is nonzero so the scalar trace can be cancelled. -/
private theorem
  chebyshev_eq_spreadBinomialExpansion
    (exponent termCount : Nat) (center radialSquare : K)
    (twoNonzero : (2 : K) ≠ 0)
    (radialEquation : radialSquare = 1 - center ^ 2)
    (symmetricExpansion :
      let scalar :=
        Algebra.Quadratic.Pair.scalar (radialSquare := radialSquare)
      let generator :=
        Algebra.Quadratic.Pair.generator (K := K)
          (radialSquare := radialSquare)
      (scalar center + generator) ^ exponent +
          (scalar center - generator) ^ exponent =
        2 * FiniteSum.Prefix.prefixSum termCount (fun index =>
          Purelib.Algebra.Binomial.binomialTerm exponent (scalar center)
            generator
            (index + index))) :
    Purelib.Polynomial.Recurrence.Chebyshev.First.Basic.chebyshevFirst exponent center =
      Recurrence.Spread.Binomial.spreadBinomialExpansion exponent termCount center radialSquare := by
  dsimp only at symmetricExpansion
  let scalar :=
    Algebra.Quadratic.Pair.scalar (radialSquare := radialSquare)
  let generator :=
    Algebra.Quadratic.Pair.generator (K := K)
      (radialSquare := radialSquare)
  have termConversion :
      FiniteSum.Prefix.prefixSum termCount (fun index =>
          Binomial.binomialTerm exponent (scalar center) generator
            (index + index)) =
        scalar (Recurrence.Spread.Binomial.spreadBinomialExpansion exponent termCount center
          radialSquare) := by
    unfold Recurrence.Spread.Binomial.spreadBinomialExpansion
    calc
      FiniteSum.Prefix.prefixSum termCount (fun index =>
          Binomial.binomialTerm exponent (scalar center) generator
            (index + index)) =
        FiniteSum.Prefix.prefixSum termCount (fun index =>
          scalar (Recurrence.Spread.Binomial.spreadBinomialTerm exponent center radialSquare index)) := by
            apply FiniteSum.Prefix.prefixSum_congr
            intro index indexBound
            exact Recurrence.Spread.Binomial.binomialTerm_quadraticPair exponent index
              center radialSquare
      _ = scalar (FiniteSum.Prefix.prefixSum termCount
          (Recurrence.Spread.Binomial.spreadBinomialTerm exponent center radialSquare)) :=
        Algebra.Quadratic.Pair.FiniteSum.prefixSum_quadraticPair_scalar radialSquare termCount _
  have trace :=
    Recurrence.Chebyshev.First.QuadraticPair.chebyshevFirst_quadraticPair_trace exponent
    center radialSquare
    radialEquation
  have scalarProducts :
      scalar (2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst exponent center) =
        scalar (2 * Recurrence.Spread.Binomial.spreadBinomialExpansion exponent termCount center
          radialSquare) := by
    calc
      scalar (2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst exponent center) =
          (scalar center + generator) ^ exponent +
            (scalar center - generator) ^ exponent := trace.symm
      _ = 2 * FiniteSum.Prefix.prefixSum termCount (fun index =>
          Binomial.binomialTerm exponent (scalar center) generator
            (index + index)) := symmetricExpansion
      _ = 2 * scalar (Recurrence.Spread.Binomial.spreadBinomialExpansion exponent termCount center
          radialSquare) := by rw [termConversion]
      _ = scalar (2 * Recurrence.Spread.Binomial.spreadBinomialExpansion exponent termCount center
          radialSquare) := by
            rw [Algebra.Quadratic.Pair.two_eq_scalar]
            rw [← Algebra.Quadratic.Pair.scalar_mul]
  have productsEqual :
      2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst exponent center =
        2 * Recurrence.Spread.Binomial.spreadBinomialExpansion exponent termCount center radialSquare :=
    congrArg Algebra.Quadratic.Pair.re scalarProducts
  exact ExplicitField.eq_of_mul_eq_mul_left twoNonzero productsEqual

/-- Transport a symmetric quadratic-pair expansion to a spread-polynomial formula.

The center is one minus twice the spread and the radial parameter is four times the spread times its complement; two
must be nonzero. -/
private theorem
  spreadPolynomial_eq_spreadBinomialExpansion_of_symmetricExpansion
    (exponent termCount : Nat) (value : K)
    (twoNonzero : (2 : K) ≠ 0)
    (symmetricExpansion :
      let center := 1 - 2 * value
      let radialSquare := 4 * value * (1 - value)
      let scalar :=
        Algebra.Quadratic.Pair.scalar (radialSquare := radialSquare)
      let generator :=
        Algebra.Quadratic.Pair.generator (K := K)
          (radialSquare := radialSquare)
      (scalar center + generator) ^ exponent +
          (scalar center - generator) ^ exponent =
        2 * FiniteSum.Prefix.prefixSum termCount (fun index =>
          Purelib.Algebra.Binomial.binomialTerm exponent (scalar center)
            generator
            (index + index))) :
    1 - 2 * Recurrence.Spread.Basic.spreadPolynomial exponent value =
      Recurrence.Spread.Binomial.spreadBinomialExpansion exponent termCount
        (1 - 2 * value) (4 * value * (1 - value)) := by
  dsimp only at symmetricExpansion
  have radialEquation :
      4 * value * (1 - value) = 1 - (1 - 2 * value) ^ 2 := by ring1
  have binomialFormula := Recurrence.Spread.Binomial.chebyshev_eq_spreadBinomialExpansion
    exponent termCount (1 - 2 * value) (4 * value * (1 - value))
    twoNonzero radialEquation symmetricExpansion
  have cleared := Recurrence.Spread.Chebyshev.exercise_8_4_cleared exponent value
  calc
    1 - 2 * Recurrence.Spread.Basic.spreadPolynomial exponent value =
        Recurrence.Chebyshev.First.Basic.chebyshevFirst exponent (1 - 2 * value) := by rw [cleared]; ring1
    _ = Recurrence.Spread.Binomial.spreadBinomialExpansion exponent termCount
        (1 - 2 * value) (4 * value * (1 - value)) := binomialFormula

/-- The alternating binomial formula for an even-index spread polynomial.

The prefix has half the index plus one terms and requires only that two be nonzero in the explicit field. -/
theorem exercise_8_6_even
    (half : Nat) (value : K) (twoNonzero : (2 : K) ≠ 0) :
    1 - 2 * Recurrence.Spread.Basic.spreadPolynomial (half + half) value =
      Recurrence.Spread.Binomial.spreadBinomialExpansion (half + half) (half + 1)
        (1 - 2 * value) (4 * value * (1 - value)) :=
  open Purelib in
  Recurrence.Spread.Binomial.spreadPolynomial_eq_spreadBinomialExpansion_of_symmetricExpansion (half + half)
    (half + 1) value twoNonzero
    (Algebra.Binomial.Parity.symmetric_binomial_even half
      (Algebra.Quadratic.Pair.scalar
        (radialSquare := 4 * value * (1 - value)) (1 - 2 * value))
      (Algebra.Quadratic.Pair.generator (K := K)
        (radialSquare := 4 * value * (1 - value))))

/-- The alternating binomial formula for an odd-index spread polynomial.

The prefix has half the preceding even index plus one terms and requires only that two be nonzero in the explicit field.
-/
theorem exercise_8_6_odd
    (half : Nat) (value : K) (twoNonzero : (2 : K) ≠ 0) :
    1 - 2 * Recurrence.Spread.Basic.spreadPolynomial (half + half + 1) value =
      Recurrence.Spread.Binomial.spreadBinomialExpansion (half + half + 1) (half + 1)
        (1 - 2 * value) (4 * value * (1 - value)) :=
  open Purelib in
  Recurrence.Spread.Binomial.spreadPolynomial_eq_spreadBinomialExpansion_of_symmetricExpansion (half + half +
    1) (half + 1) value
    twoNonzero
    (Algebra.Binomial.Parity.symmetric_binomial_odd half
      (Algebra.Quadratic.Pair.scalar
        (radialSquare := 4 * value * (1 - value)) (1 - 2 * value))
      (Algebra.Quadratic.Pair.generator (K := K)
        (radialSquare := 4 * value * (1 - value))))

/-- The last term of the even expansion is exactly `(-b)^l`. -/
theorem spreadBinomialTerm_even_last
    (half : Nat) (center radialSquare : K) :
    Recurrence.Spread.Binomial.spreadBinomialTerm (half + half) center radialSquare half =
      (-radialSquare) ^ half := open Purelib in by
  unfold Recurrence.Spread.Binomial.spreadBinomialTerm
  rw [show half + half - (half + half) = 0 by omega0,
    Data.Nat.Choose.choose_self, pow_zero, Nat.cast_one]
  ring1

/-- The last term of the odd expansion is exactly `(2l+1)a(-b)^l`. -/
theorem spreadBinomialTerm_odd_last
    (half : Nat) (center radialSquare : K) :
    Recurrence.Spread.Binomial.spreadBinomialTerm (half + half + 1) center radialSquare half =
      (half + half + 1 : K) * center * (-radialSquare) ^ half := open Purelib in by
  unfold Recurrence.Spread.Binomial.spreadBinomialTerm
  rw [show half + half + 1 - (half + half) = 1 by omega0,
    show (half + half + 1).choose (half + half) = half + half + 1 by
      exact Data.Nat.Choose.choose_succ_self_right (half + half),
    pow_one, NatCast.add, NatCast.add, Nat.cast_one]
  ring1

end Purelib.Polynomial.Recurrence.Spread.Binomial

end
