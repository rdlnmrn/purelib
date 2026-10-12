module

import Purelib.Algebra.Binomial
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Algebra.Quadratic.Pair.FiniteSum
import Purelib.Algebra.Quadratic.Pair.Power
public import Purelib.Geometry.Trigonometry.Turn.Rational.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Bounded binomial coordinates of rational turns

The original alternating even and odd terms retain their natural choose
coefficients, ascending scalar powers and signed pair powers. The original
bounded prefixes give the two coordinates of the requested finite turn and
the numerator and denominator of its field-valued rational function.
-/

namespace Purelib.Geometry.Trigonometry.Turn.Rational.Binomial

open Purelib
open Purelib.Algebra.FiniteSum
open Purelib.Algebra.Quadratic
open _root_.Purelib.Algebra.Quadratic renaming Pair -> QuadraticPair
open Purelib.Geometry.Trigonometry.Turn

public section

/-- An even-index binomial term gives a signed scalar contribution.

The natural coefficient retains the displayed row and doubled index. The
index also determines the sign and the original input's even power. -/
@[expose] def turnRationalEvenTerm
    {R : Type*} [CommRing R]
    (row : Nat) (value : R) (index : Nat) : R :=
  (row.choose (index + index) : R) * (-1) ^ index *
    value ^ (index + index)

/-- An odd-index binomial term gives a signed scalar contribution.

The natural coefficient retains the displayed row and doubled successor
index. The same index determines the sign and the original input's odd power. -/
@[expose] def turnRationalOddTerm
    {R : Type*} [CommRing R]
    (row : Nat) (value : R) (index : Nat) : R :=
  (row.choose (index + index + 1) : R) * (-1) ^ index *
    value ^ (index + index + 1)

/-- Sum the bounded alternating even-index binomial terms.

The prefix retains exactly half plus one entries of the original row and
scalar input, in ascending doubled-index order. -/
@[expose] def turnRationalEvenExpansion
    {R : Type*} [CommRing R]
    (row half : Nat) (value : R) : R :=
  Prefix.prefixSum (half + 1) (Geometry.Trigonometry.Turn.Rational.Binomial.turnRationalEvenTerm row value)

/-- Sum the bounded alternating odd-index binomial terms.

The prefix retains exactly half plus one entries of the original row and
scalar input, in ascending odd-index order. -/
@[expose] def turnRationalOddExpansion
    {R : Type*} [CommRing R]
    (row half : Nat) (value : R) : R :=
  Prefix.prefixSum (half + 1) (Geometry.Trigonometry.Turn.Rational.Binomial.turnRationalOddTerm row value)

section
/-- One binomial term in the quadratic-pair expansion of an iterated turn.

The term is the displayed pure-imaginary pair power multiplied by its natural binomial coefficient. -/
private def turnRationalBinomialPairTerm
    {R : Type*} [CommRing R]
    (row : Nat) (value : R) (index : Nat) : QuadraticPair R 1 :=
  (⟨0, value⟩ : Algebra.Quadratic.Pair R 1) ^ index *
    (row.choose index : Algebra.Quadratic.Pair R 1)
/-- An even quadratic-pair binomial term has its signed scalar coordinate.

Its imaginary coordinate is zero. The retained binomial coefficient and
input power give the original alternating even scalar term. -/
private theorem turnRationalBinomialPairTerm_even
    {R : Type*} [CommRing R]
    (row : Nat) (value : R) (index : Nat) :
    turnRationalBinomialPairTerm row value (index + index) =
      QuadraticPair.scalar
        (turnRationalEvenTerm row value index) := by
  unfold turnRationalBinomialPairTerm turnRationalEvenTerm
  rw [Pair.Power.pureImaginary_even_power,
    QuadraticPair.natCast_eq_scalar,
    ← QuadraticPair.scalar_mul]
  congr 1
  ring1
/-- An odd quadratic-pair binomial term has its signed imaginary coordinate.

Its real coordinate is zero. The retained binomial coefficient and input
power give the original alternating odd scalar term. -/
private theorem turnRationalBinomialPairTerm_odd
    {R : Type*} [CommRing R]
    (row : Nat) (value : R) (index : Nat) :
    turnRationalBinomialPairTerm row value (index + index + 1) =
      ⟨0, turnRationalOddTerm row value index⟩ := by
  unfold turnRationalBinomialPairTerm turnRationalOddTerm
  rw [Pair.Power.pureImaginary_odd_power,
    QuadraticPair.natCast_eq_scalar]
  ext <;> simp only [QuadraticPair.scalar_re,
    QuadraticPair.scalar_im, QuadraticPair.mul_re,
    QuadraticPair.mul_im]
  all_goals ring1
/-- An iterated turn pair equals its finite binomial expansion.

The prefix contains exactly the terms indexed from zero through the requested row. -/
private theorem turnRationalPair_binomial
    {R : Type*} [CommRing R] (row : Nat) (value : R) :
    Rational.Basic.turnRationalPair row value =
      Prefix.prefixSum (row + 1)
        (turnRationalBinomialPairTerm row value) := by
  let offset : QuadraticPair R 1 := ⟨0, value⟩
  calc
    Rational.Basic.turnRationalPair row value = (1 + offset) ^ row := by
      unfold Rational.Basic.turnRationalPair offset
      congr 1
      ext <;> simp only [QuadraticPair.one_re,
        QuadraticPair.one_im, QuadraticPair.add_re,
        QuadraticPair.add_im]
      all_goals ring1
    _ = Algebra.Binomial.binomialExpansion row 1 offset :=
      Algebra.Binomial.binomial_theorem row 1 offset
    _ = Prefix.prefixSum (row + 1)
        (turnRationalBinomialPairTerm row value) := by
      unfold Algebra.Binomial.binomialExpansion
        turnRationalBinomialPairTerm offset
      apply Prefix.prefixSum_congr
      intro index indexBound
      rewrite [one_pow, _root_.mul_one]
      exact Eq.refl _
end

/-- An even iterated turn has the bounded alternating binomial coordinates.

The real coordinate contains the even-index terms and the imaginary coordinate
contains the odd-index terms. Both prefixes retain the displayed half index,
including the last even term and the certified zero next odd term. -/
theorem turnRationalPair_even_binomial
    {R : Type*} [CommRing R] (half : Nat) (value : R) :
    Rational.Basic.turnRationalPair (half + half) value =
      ⟨turnRationalEvenExpansion (half + half) half value,
        turnRationalOddExpansion (half + half) half value⟩ := by
  rw [turnRationalPair_binomial]
  rw [Prefix.prefixSum_pairs_and_last]
  have pairedTerms :
      Prefix.prefixSum half (fun index =>
          turnRationalBinomialPairTerm (half + half) value
              (index + index) +
            turnRationalBinomialPairTerm (half + half) value
              (index + index + 1)) =
        Prefix.prefixSum half (fun index =>
          (⟨turnRationalEvenTerm (half + half) value index,
            turnRationalOddTerm (half + half) value index⟩ :
              QuadraticPair R 1)) := by
    apply Prefix.prefixSum_congr
    intro index indexBound
    rw [turnRationalBinomialPairTerm_even,
      turnRationalBinomialPairTerm_odd]
    ext <;> simp only [QuadraticPair.scalar_re,
      QuadraticPair.scalar_im, QuadraticPair.add_re,
      QuadraticPair.add_im]
    all_goals ring1
  rw [pairedTerms, Pair.FiniteSum.finitePrefixSum_quadraticPair_coordinates]
  rw [turnRationalBinomialPairTerm_even]
  have finalOddZero :
      turnRationalOddTerm (half + half) value half = 0 := by
    unfold turnRationalOddTerm
    rw [Nat.choose_succ_self]
    rewrite [Nat.cast_zero]
    exact (congrArg (fun coefficient : R =>
      coefficient * value ^ (half + half + 1))
      (MulZeroClass.zero_mul ((-1 : R) ^ half))).trans
        (MulZeroClass.zero_mul (value ^ (half + half + 1)))
  ext
  · simp only [QuadraticPair.scalar_re,
      QuadraticPair.add_re]
    unfold turnRationalEvenExpansion
    rw [Prefix.prefixSum_succ_last]
  · simp only [QuadraticPair.scalar_im,
      QuadraticPair.add_im, add_zero]
    unfold turnRationalOddExpansion
    rw [Prefix.prefixSum_succ_last, finalOddZero, add_zero]

/-- An odd iterated turn has the bounded alternating binomial coordinates.

The retained half index gives the same number of even and odd terms. Pairing
those original ordered terms yields the two displayed scalar prefixes. -/
theorem turnRationalPair_odd_binomial
    {R : Type*} [CommRing R] (half : Nat) (value : R) :
    Rational.Basic.turnRationalPair (half + half + 1) value =
      ⟨turnRationalEvenExpansion (half + half + 1) half value,
        turnRationalOddExpansion (half + half + 1) half value⟩ := by
  rw [turnRationalPair_binomial]
  rw [show half + half + 1 + 1 =
    (half + 1) + (half + 1) by omega0]
  rw [Prefix.prefixSum_pairs]
  have pairedTerms :
      Prefix.prefixSum (half + 1) (fun index =>
          turnRationalBinomialPairTerm (half + half + 1) value
              (index + index) +
            turnRationalBinomialPairTerm (half + half + 1) value
              (index + index + 1)) =
        Prefix.prefixSum (half + 1) (fun index =>
          (⟨turnRationalEvenTerm (half + half + 1) value index,
            turnRationalOddTerm (half + half + 1) value index⟩ :
              QuadraticPair R 1)) := by
    apply Prefix.prefixSum_congr
    intro index indexBound
    rw [turnRationalBinomialPairTerm_even,
      turnRationalBinomialPairTerm_odd]
    ext <;> simp only [QuadraticPair.scalar_re,
      QuadraticPair.scalar_im, QuadraticPair.add_re,
      QuadraticPair.add_im]
    all_goals ring1
  rw [pairedTerms, Pair.FiniteSum.finitePrefixSum_quadraticPair_coordinates]
  rfl

/-- An even turn-rational function is the quotient of its two binomial prefixes.

The numerator is the alternating odd prefix and the denominator is the
alternating even prefix, with both retaining the same half index and input. -/
theorem exercise_9_3_even
    {K : Type*} [Algebra.Field.ExplicitField K] (half : Nat) (value : K) :
    Rational.Basic.turnRationalFunction (half + half) value =
      turnRationalOddExpansion (half + half) half value /
        turnRationalEvenExpansion (half + half) half value := by
  unfold Rational.Basic.turnRationalFunction Rational.Basic.turnRationalNumerator
    Rational.Basic.turnRationalDenominator
  rw [turnRationalPair_even_binomial]

/-- An odd turn-rational function is the quotient of its two binomial prefixes.

The numerator and denominator retain the respective odd and even prefixes
with the same displayed row, half index and scalar input. -/
theorem exercise_9_3_odd
    {K : Type*} [Algebra.Field.ExplicitField K] (half : Nat) (value : K) :
    Rational.Basic.turnRationalFunction (half + half + 1) value =
      turnRationalOddExpansion (half + half + 1) half value /
        turnRationalEvenExpansion (half + half + 1) half value := by
  unfold Rational.Basic.turnRationalFunction Rational.Basic.turnRationalNumerator
    Rational.Basic.turnRationalDenominator
  rw [turnRationalPair_odd_binomial]

end

end Purelib.Geometry.Trigonometry.Turn.Rational.Binomial
