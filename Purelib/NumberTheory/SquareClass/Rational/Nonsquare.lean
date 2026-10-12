module
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Nat.Divisibility
import Purelib.Data.Nat.Remainder.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Algebra.Field.ExplicitField

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

open Purelib.Data.Rat

/-!
# Literal nonsquare classes over canonical rational displays

The retained numerator and positive denominator clear each rational square
identity. Finite remainder cases force a common divisor of those same original
components, contradicting their displayed reducedness certificate.
-/

open Purelib.Data.Nat
open Purelib.Data.Int

namespace Purelib.NumberTheory.SquareClass.Rational.Nonsquare

open Purelib.Algebra.Field (ExplicitField)

/-- If two divides a natural square, it divides its base.

The original remainder modulo two has exactly two possible values.
The nonzero residue has nonzero square remainder, so the supplied square
divisibility retains a zero remainder for the original natural base. -/
private theorem two_dvd_of_two_dvd_square {value : Nat}
    (divides : 2 ∣ value * value) : 2 ∣ value := by
  have reducedDivides := Divisibility.mod_eq_zero_of_dvd divides
  apply Divisibility.of_mod_eq_zero
  have remainderLt : value % 2 < 2 := Nat.mod_lt value (by decide)
  have squareRemainder :
      value * value % 2 = (value % 2) * (value % 2) % 2 := by
    exact ((Remainder.Arithmetic.mul_mod_left value (value % 2) 2).trans
      (Remainder.Arithmetic.mul_mod_right value value 2)).symm
  rewrite [squareRemainder] at reducedDivides
  cases remainderEq : value % 2 with
  | zero => rfl
  | succ remainder =>
      cases remainder with
      | zero =>
          rewrite [remainderEq] at reducedDivides
          exact ((by decide : (1 * 1 % 2 : Nat) ≠ 0) reducedDivides).elim
      | succ remainder =>
          rw [remainderEq] at remainderLt
          have twoLe : 2 ≤ Nat.succ (Nat.succ remainder) :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le remainder))
          exact (Nat.not_lt_of_ge twoLe remainderLt).elim

/-- A positive nonunit natural detected by square divisibility is not a rational square.

The same natural must divide every base whose square it divides. Clearing the
original positive rational denominator forces it to divide both retained
canonical components, contradicting their original coprimality certificate. -/
private theorem square_ne_nat_of_dvd_square (prime : Nat)
    (primePositive : 0 < prime) (primeNeOne : prime ≠ 1)
    (dvdSquare : ∀ {value : Nat}, prime ∣ value * value → prime ∣ value)
    (value : Fraction.Rational) : value ^ 2 ≠ (prime : Fraction.Rational) := by
  intro square
  let reduced := Fraction.Basic.representative value
  have cleared := Fraction.Cast.representative_mul_den value
  change value * (reduced.den : Fraction.Rational) = (reduced.num : Fraction.Rational) at cleared
  have rationalSquare :
      (reduced.num : Fraction.Rational) ^ 2 =
        (prime : Fraction.Rational) * (reduced.den : Fraction.Rational) ^ 2 := by
    calc
      (reduced.num : Fraction.Rational) ^ 2 =
          (value * (reduced.den : Fraction.Rational)) ^ 2 := by rw [cleared]
      _ = value ^ 2 * (reduced.den : Fraction.Rational) ^ 2 := by ring1
      _ = (prime : Fraction.Rational) * (reduced.den : Fraction.Rational) ^ 2 := by rw [square]
  have integerSquare :
      reduced.num * reduced.num =
        (prime : Int) * ((reduced.den : Int) * (reduced.den : Int)) := by
    apply Fraction.Cast.Compatibility.intCast_injective_direct
    rw [Fraction.Cast.intCast_mul_direct, Fraction.Cast.intCast_mul_direct, Fraction.Cast.intCast_mul_direct]
    simpa only [Int.cast_natCast, pow_two] using rationalSquare
  have absoluteSquare := congrArg Int.natAbs integerSquare
  have naturalSquare :
      reduced.num.natAbs * reduced.num.natAbs =
        prime * (reduced.den * reduced.den) := by
    rewrite [Arithmetic.natAbs_mul, Arithmetic.natAbs_mul,
      Arithmetic.natAbs_mul] at absoluteSquare
    change reduced.num.natAbs * reduced.num.natAbs =
      prime * (reduced.den * reduced.den) at absoluteSquare
    exact absoluteSquare
  have primeDvdNumerator : prime ∣ reduced.num.natAbs :=
    dvdSquare ⟨reduced.den * reduced.den, naturalSquare⟩
  have numeratorDivides : prime ∣ reduced.num.natAbs := primeDvdNumerator
  rcases primeDvdNumerator with ⟨numeratorFactor, numeratorEquation⟩
  have denominatorSquare :
      reduced.den * reduced.den =
        prime * (numeratorFactor * numeratorFactor) := by
    have scaled :
        prime * (prime * (numeratorFactor * numeratorFactor)) =
          prime * (reduced.den * reduced.den) := by
      calc
        prime * (prime * (numeratorFactor * numeratorFactor)) =
            (prime * numeratorFactor) * (prime * numeratorFactor) := by ring1
        _ = prime * (reduced.den * reduced.den) := by
          rw [← numeratorEquation]
          exact naturalSquare
    exact (Nat.eq_of_mul_eq_mul_left primePositive scaled).symm
  have primeDvdDenominator : prime ∣ reduced.den :=
    dvdSquare ⟨numeratorFactor * numeratorFactor, denominatorSquare⟩
  rcases reduced.reduced with ⟨certificate⟩
  have absurd : prime = 1 :=
    certificate.eq_one_of_dvd numeratorDivides primeDvdDenominator
  exact primeNeOne absurd

/-- No canonical rational has square two.

The two original residue cases detect divisibility of a natural square.
Clearing the original positive denominator makes both canonical components
divisible by two, contrary to their retained reducedness certificate. -/
public theorem square_ne_two (value : Fraction.Rational) : value ^ 2 ≠ 2 := by
  exact square_ne_nat_of_dvd_square 2 (by decide) (by decide)
    two_dvd_of_two_dvd_square value

/-- If three divides a natural square, it divides its base.

The original remainder modulo three has exactly three possible values.
Both nonzero literal residues have nonzero square remainder, leaving only
the original base remainder zero under the supplied divisibility. -/
private theorem three_dvd_of_three_dvd_square {value : Nat}
    (divides : 3 ∣ value * value) : 3 ∣ value := by
  have reducedDivides := Divisibility.mod_eq_zero_of_dvd divides
  apply Divisibility.of_mod_eq_zero
  have remainderLt : value % 3 < 3 := Nat.mod_lt value (by decide)
  have squareRemainder :
      value * value % 3 = (value % 3) * (value % 3) % 3 := by
    exact ((Remainder.Arithmetic.mul_mod_left value (value % 3) 3).trans
      (Remainder.Arithmetic.mul_mod_right value value 3)).symm
  rewrite [squareRemainder] at reducedDivides
  cases remainderEq : value % 3 with
  | zero => rfl
  | succ remainder =>
      cases remainder with
      | zero =>
          rewrite [remainderEq] at reducedDivides
          have impossible : (1 * 1 % 3 : Nat) ≠ 0 := by decide
          exact (impossible reducedDivides).elim
      | succ remainder =>
          cases remainder with
          | zero =>
              rewrite [remainderEq] at reducedDivides
              have impossible : (2 * 2 % 3 : Nat) ≠ 0 := by decide
              exact (impossible reducedDivides).elim
          | succ remainder =>
              rw [remainderEq] at remainderLt
              have threeLe : 3 ≤ Nat.succ (Nat.succ (Nat.succ remainder)) :=
                Nat.succ_le_succ (Nat.succ_le_succ
                  (Nat.succ_le_succ (Nat.zero_le remainder)))
              exact (Nat.not_lt_of_ge threeLe remainderLt).elim

/-- No canonical rational has square three.

The three original residue cases detect divisibility of a natural square.
Clearing the retained positive denominator forces a common divisor of the
same canonical components, contradicting their Bézout certificate. -/
public theorem square_ne_three (value : Fraction.Rational) : value ^ 2 ≠ 3  := by
  exact square_ne_nat_of_dvd_square 3 (by decide) (by decide)
    three_dvd_of_three_dvd_square value

/-- No canonical rational has square twelve.

Dividing a proposed root by the nonzero rational two would give a root of three in the same explicit field. -/
public theorem square_ne_twelve (value : Fraction.Rational) : value ^ 2 ≠ 12 := by
  intro square
  apply square_ne_three (value / 2)
  have cancel := ExplicitField.mul_inv_cancel (2 : Fraction.Rational) (by decide)
  rw [ExplicitField.div_eq_mul_inv]
  calc
    _ = value ^ 2 * (2 : Fraction.Rational)⁻¹ ^ 2 := by ring1
    _ = 12 * (2 : Fraction.Rational)⁻¹ ^ 2 := congrArg (fun scalar => scalar * (2 : Fraction.Rational)⁻¹ ^ 2) square
    _ = 3 * (2 * (2 : Fraction.Rational)⁻¹) ^ 2 := by ring1
    _ = 3 := by rw [cancel]; ring1

/-- Divisibility of a displayed natural square by five forces divisibility of its base.

The five literal original remainder cases exhaust the bounded possibilities.
Each nonzero residue has nonzero square remainder, so direct divisibility
readback certifies the same original natural base. -/
private theorem five_dvd_of_five_dvd_square {value : Nat}
    (divides : 5 ∣ value * value) : 5 ∣ value := by
  have reducedDivides := Divisibility.mod_eq_zero_of_dvd divides
  apply Divisibility.of_mod_eq_zero
  have remainderLt : value % 5 < 5 := Nat.mod_lt value (by decide)
  have squareRemainder :
      value * value % 5 = (value % 5) * (value % 5) % 5 := by
    exact ((Remainder.Arithmetic.mul_mod_left value (value % 5) 5).trans
      (Remainder.Arithmetic.mul_mod_right value value 5)).symm
  rewrite [squareRemainder] at reducedDivides
  cases remainderEq : value % 5 with
  | zero => rfl
  | succ remainder =>
      cases remainder with
      | zero =>
          rewrite [remainderEq] at reducedDivides
          exact ((by decide : (1 * 1 % 5 : Nat) ≠ 0) reducedDivides).elim
      | succ remainder =>
          cases remainder with
          | zero =>
              rewrite [remainderEq] at reducedDivides
              exact ((by decide : (2 * 2 % 5 : Nat) ≠ 0) reducedDivides).elim
          | succ remainder =>
              cases remainder with
              | zero =>
                  rewrite [remainderEq] at reducedDivides
                  exact ((by decide : (3 * 3 % 5 : Nat) ≠ 0) reducedDivides).elim
              | succ remainder =>
                  cases remainder with
                  | zero =>
                      rewrite [remainderEq] at reducedDivides
                      exact ((by decide : (4 * 4 % 5 : Nat) ≠ 0) reducedDivides).elim
                  | succ remainder =>
                      rw [remainderEq] at remainderLt
                      have fiveLe :
                          5 ≤ Nat.succ (Nat.succ (Nat.succ
                            (Nat.succ (Nat.succ remainder)))) :=
                        Nat.succ_le_succ (Nat.succ_le_succ
                          (Nat.succ_le_succ (Nat.succ_le_succ
                            (Nat.succ_le_succ (Nat.zero_le remainder)))))
                      exact (Nat.not_lt_of_ge fiveLe remainderLt).elim

/-- No canonical rational has square five.

Its original positive denominator clears the square identity. The five
literal remainder cases force both original reduced components divisible
by five, contradicting their retained coprimality certificate. -/
public theorem square_ne_five (value : Fraction.Rational) : value ^ 2 ≠ 5 := by
  exact square_ne_nat_of_dvd_square 5 (by decide) (by decide)
    five_dvd_of_five_dvd_square value

/-- No canonical rational has square 455.

Clearing its original positive denominator gives the retained integer equation
num² = 455 den². The five-residue calculation makes both same canonical
components divisible by five, contradicting their Bézout certificate. -/
public theorem square_ne_455 (value : Fraction.Rational) : value ^ 2 ≠ 455 := by
  intro square
  let reduced := Fraction.Basic.representative value
  have cleared := Fraction.Cast.representative_mul_den value
  change value * (reduced.den : Fraction.Rational) = (reduced.num : Fraction.Rational) at cleared
  have rationalSquare :
      (reduced.num : Fraction.Rational) ^ 2 =
        455 * (reduced.den : Fraction.Rational) ^ 2 := by
    calc
      (reduced.num : Fraction.Rational) ^ 2 =
          (value * (reduced.den : Fraction.Rational)) ^ 2 := by rw [cleared]
      _ = value ^ 2 * (reduced.den : Fraction.Rational) ^ 2 := by ring1
      _ = 455 * (reduced.den : Fraction.Rational) ^ 2 := by rw [square]
  have integerSquare :
      reduced.num * reduced.num =
        (455 : Int) * ((reduced.den : Int) * (reduced.den : Int)) := by
    apply Fraction.Cast.Compatibility.intCast_injective_direct
    rw [Fraction.Cast.intCast_mul_direct, Fraction.Cast.intCast_mul_direct, Fraction.Cast.intCast_mul_direct]
    simpa only [Int.cast_natCast, Int.cast_ofNat, pow_two] using
      rationalSquare
  have absoluteSquare := congrArg Int.natAbs integerSquare
  have naturalSquare :
      reduced.num.natAbs * reduced.num.natAbs =
        455 * (reduced.den * reduced.den) := by
    rewrite [Arithmetic.natAbs_mul, Arithmetic.natAbs_mul,
      Arithmetic.natAbs_mul] at absoluteSquare
    change reduced.num.natAbs * reduced.num.natAbs =
      455 * (reduced.den * reduced.den) at absoluteSquare
    exact absoluteSquare
  have fiveDvdNumeratorSquare :
      5 ∣ reduced.num.natAbs * reduced.num.natAbs := by
    refine ⟨91 * (reduced.den * reduced.den), ?_⟩
    calc
      reduced.num.natAbs * reduced.num.natAbs =
          455 * (reduced.den * reduced.den) := naturalSquare
      _ = 5 * (91 * (reduced.den * reduced.den)) := by ring1
  have fiveDvdNumerator : 5 ∣ reduced.num.natAbs :=
    five_dvd_of_five_dvd_square fiveDvdNumeratorSquare
  have numeratorDivides : 5 ∣ reduced.num.natAbs := fiveDvdNumerator
  rcases fiveDvdNumerator with ⟨numeratorFactor, numeratorEquation⟩
  have reducedEquation :
      5 * (numeratorFactor * numeratorFactor) =
        91 * (reduced.den * reduced.den) := by
    have scaled :
        5 * (5 * (numeratorFactor * numeratorFactor)) =
          5 * (91 * (reduced.den * reduced.den)) := by
      calc
        5 * (5 * (numeratorFactor * numeratorFactor)) =
            (5 * numeratorFactor) * (5 * numeratorFactor) := by ring1
        _ = 455 * (reduced.den * reduced.den) := by
          rw [← numeratorEquation]
          exact naturalSquare
        _ = 5 * (91 * (reduced.den * reduced.den)) := by ring1
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 5) scaled
  have denominatorSquareMod :
      (reduced.den * reduced.den) % 5 = 0 := by
    have productDivisible : 5 ∣ 91 * (reduced.den * reduced.den) :=
      ⟨numeratorFactor * numeratorFactor, reducedEquation.symm⟩
    have unitRemainder : 91 % 5 = 1 := by decide
    calc
      (reduced.den * reduced.den) % 5 =
          ((reduced.den * reduced.den) % 5) % 5 :=
        (Remainder.mod_eq_of_lt (Nat.mod_lt _ (by decide : 0 < 5))).symm
      _ = ((91 % 5) * ((reduced.den * reduced.den) % 5)) % 5 := by
        rw [unitRemainder, Nat.one_mul]
      _ = (91 * (reduced.den * reduced.den)) % 5 :=
        (Remainder.Arithmetic.mul_mod_right (91 % 5) (reduced.den * reduced.den) 5).trans
          (Remainder.Arithmetic.mul_mod_left 91 (reduced.den * reduced.den) 5)
      _ = 0 := Divisibility.mod_eq_zero_of_dvd productDivisible
  have fiveDvdDenominatorSquare : 5 ∣ reduced.den * reduced.den :=
    Divisibility.of_mod_eq_zero denominatorSquareMod
  have fiveDvdDenominator : 5 ∣ reduced.den :=
    five_dvd_of_five_dvd_square fiveDvdDenominatorSquare
  rcases reduced.reduced with ⟨certificate⟩
  have absurd : 5 = 1 :=
    certificate.eq_one_of_dvd numeratorDivides fiveDvdDenominator
  exact (by decide : (5 : Nat) ≠ 1) absurd

end Purelib.NumberTheory.SquareClass.Rational.Nonsquare
