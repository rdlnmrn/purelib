module
import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Divisibility
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Bool.Decide
import Purelib.Data.Nat.Decide
import Purelib.Data.Nat.FiniteSum
import Purelib.Data.Nat.GCD.Extended
import Purelib.Data.Rat.Fraction.Field
import Purelib.NumberTheory.Divisor
public import Purelib.NumberTheory.Totient.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Divisibility
import Purelib.Polynomial.Dense.Rational.Division.Normalized
import Purelib.Polynomial.Dense.Rational.Extensionality
public import Purelib.Polynomial.Dense.Rational.FiniteProduct
public import Purelib.Polynomial.Dense.Rational.PowerMinusOne

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Data.Rat

open Purelib.Data.Nat

open Purelib.NumberTheory

open Purelib.Polynomial

section
@[expose] public section

/-!
# Constructive finite cyclotomic factors

Ordinary cyclotomic factors are constructed here without roots of unity or
Mathlib's noncomputable cyclotomic hierarchy.  The coefficient program uses
the project's canonical rational records and finite dense long division.
The proof follows the elementary square-free divisor argument: previously
constructed pairwise-coprime factors all divide `X^n-1`, so their product
does too, and the next executable quotient is exact.
-/

namespace Purelib.NumberTheory.Cyclotomic.Basic

/-- Fuelled implementation of the finite cyclotomic construction.  The
first argument is structural recursion fuel; the proof below shows that any
fuel strictly larger than the requested stage gives the same result. -/
def cyclotomicAux : Nat → Nat → Polynomial.Dense.Rational.Divisibility.CoefficientPolynomial
  | 0, _ => Dense.Basic.DensePolynomial.constant 1
  | _ + 1, 0 => Dense.Basic.DensePolynomial.constant 1
  | fuel + 1, number + 1 =>
      let properProduct := Dense.Rational.FiniteProduct.productFin (number + 2) fun divisor =>
        if _evidence : 2 ≤ divisor.val ∧ divisor.val ∣ number + 1 then
          Purelib.NumberTheory.Cyclotomic.Basic.cyclotomicAux fuel ((number + 1) / divisor.val)
        else Dense.Basic.DensePolynomial.constant 1
      (Dense.Basic.DensePolynomial.divMod (Dense.Rational.PowerMinusOne.powerMinusOne (number + 1))
        properProduct).quotient

/-- Extra structural fuel does not change a stage once the fuel exceeds its
index. -/
theorem cyclotomicAux_eq_of_enough_fuel : ∀ number : Nat,
    ∀ leftFuel rightFuel : Nat, number < leftFuel → number < rightFuel →
      Cyclotomic.Basic.cyclotomicAux leftFuel number =
        Cyclotomic.Basic.cyclotomicAux rightFuel number := by
  intro number
  induction number using Nat.strong_induction_on with
  | h number inductionHypothesis =>
      intro leftFuel rightFuel leftEnough rightEnough
      cases leftFuel with
      | zero => exact False.elim ((Nat.not_lt_zero _) leftEnough)
      | succ leftFuel =>
          cases rightFuel with
          | zero => exact False.elim ((Nat.not_lt_zero _) rightEnough)
          | succ rightFuel =>
              cases number with
              | zero => rfl
              | succ previous =>
                  rw [Cyclotomic.Basic.cyclotomicAux, Cyclotomic.Basic.cyclotomicAux]
                  apply congrArg fun product =>
                    (Dense.Basic.DensePolynomial.divMod (Dense.Rational.PowerMinusOne.powerMinusOne (previous + 1))
                      product).quotient
                  apply Dense.Rational.FiniteProduct.productFin_congr
                  intro divisor
                  by_cases selected :
                      2 ≤ divisor.val ∧ divisor.val ∣ previous + 1
                  · rw [dif_pos selected, dif_pos selected]
                    have quotientProper :
                        (previous + 1) / divisor.val < previous + 1 :=
                      Division.div_lt_self (by omega0) (by omega0)
                    apply inductionHypothesis _ quotientProper
                    · omega0
                    · omega0
                  · rw [dif_neg selected, dif_neg selected]

/-- Executable finite cyclotomic factor, evaluated with the least uniformly
sufficient structural fuel. -/
def cyclotomic (number : Nat) : (Dense.Basic.DensePolynomial
  Fraction.Rational) :=
  Cyclotomic.Basic.cyclotomicAux (number + 1) number

/-- One slot in the literal divisor-coordinate product at stage `number`. -/
def properCyclotomicFactor (number : Nat) (divisor : Fin (number + 1)) :
    (Dense.Basic.DensePolynomial Fraction.Rational) :=
    if _evidence : 2 ≤ divisor.val ∧ divisor.val ∣ number then
      Cyclotomic.Basic.cyclotomic (number / divisor.val)
    else Dense.Basic.DensePolynomial.constant 1

/-- The literal product of all earlier divisor-indexed factors used to
construct `cyclotomic number`. -/
def properCyclotomicProduct (number : Nat) : (Dense.Basic.DensePolynomial
  Fraction.Rational) :=
  Dense.Rational.FiniteProduct.productFin (number + 1) (Cyclotomic.Basic.properCyclotomicFactor number)

/-- The stage-zero convention is the unit polynomial. -/
@[simp] theorem cyclotomic_zero :
    Cyclotomic.Basic.cyclotomic 0 = Dense.Basic.DensePolynomial.constant 1 := rfl

/-- A positive cyclotomic stage is the quotient of the power-minus-one polynomial by its proper-divisor product. -/
theorem cyclotomic_succ (number : Nat) :
    Cyclotomic.Basic.cyclotomic (number + 1) =
      (Dense.Basic.DensePolynomial.divMod (Dense.Rational.PowerMinusOne.powerMinusOne (number + 1))
        (Cyclotomic.Basic.properCyclotomicProduct (number + 1))).quotient := by
  unfold Cyclotomic.Basic.cyclotomic
  rw [Cyclotomic.Basic.cyclotomicAux]
  unfold Cyclotomic.Basic.properCyclotomicProduct Cyclotomic.Basic.properCyclotomicFactor
  apply congrArg fun product =>
    (Dense.Basic.DensePolynomial.divMod (Dense.Rational.PowerMinusOne.powerMinusOne (number + 1)) product).quotient
  apply Dense.Rational.FiniteProduct.productFin_congr
  intro divisor
  by_cases selected : 2 ≤ divisor.val ∧ divisor.val ∣ number + 1
  · rw [dif_pos selected, dif_pos selected]
    apply Cyclotomic.Basic.cyclotomicAux_eq_of_enough_fuel
    · exact Division.div_lt_self (by omega0) (by omega0)
    · omega0
  · rw [dif_neg selected, dif_neg selected]

/-- Every earlier positive divisor factor occurs in the later stage's
literal quotient-coordinate product. -/
theorem cyclotomic_evalDvd_properProduct
    {divisor number : Nat} (divisorPositive : 0 < divisor)
    (divides : divisor ∣ number) (proper : divisor < number) :
    Dense.Rational.Divisibility.EvalDvd (Cyclotomic.Basic.cyclotomic divisor)
      (Cyclotomic.Basic.properCyclotomicProduct number) := by
  let coordinate : Fin (number + 1) :=
    ⟨number / divisor, Nat.lt_succ_of_le (Division.div_le_self _ _)⟩
  have coordinateDivides : coordinate.val ∣ number := by
    refine ⟨divisor, ?_⟩
    dsimp only [coordinate]
    exact (Division.div_mul_cancel divides).symm
  have coordinateLarge : 2 ≤ coordinate.val := by
    exact Divisor.divisorQuotient_two_le divisorPositive divides proper
  have selected : Cyclotomic.Basic.properCyclotomicFactor number coordinate =
      Cyclotomic.Basic.cyclotomic divisor := by
    unfold Cyclotomic.Basic.properCyclotomicFactor
    rw [dif_pos ⟨coordinateLarge, coordinateDivides⟩]
    congr 1
    exact Divisor.divide_by_divisorQuotient (by omega0) divides
  rw [Cyclotomic.Basic.properCyclotomicProduct]
  rw [← selected]
  exact Dense.Rational.FiniteProduct.evalDvd_factor_productFin (number + 1)
    (Cyclotomic.Basic.properCyclotomicFactor number) coordinate

/-- The simultaneous induction invariant for the finite construction. -/
structure StageSpec (number : Nat) : Prop where
  /-- The computed cyclotomic factor is already in normalized coefficient form. -/ normalized :
    (Cyclotomic.Basic.cyclotomic number).normalize = Cyclotomic.Basic.cyclotomic number
  /-- The computed cyclotomic factor is nonzero. -/ nonzero : (Cyclotomic.Basic.cyclotomic number).isZero = false
  /-- The proper-divisor product times this factor evaluates to the power-minus-one polynomial. -/ factorization :
    Dense.Rational.Divisibility.EvalEq (Dense.Rational.PowerMinusOne.powerMinusOne number)
    (Cyclotomic.Basic.properCyclotomicProduct number * Cyclotomic.Basic.cyclotomic number)
  /-- The retained factor and its proper-divisor product admit an evaluation Bézout identity. -/ properCoprime :
    Dense.Rational.Divisibility.EvalCoprime (Cyclotomic.Basic.properCyclotomicProduct number)
    (Cyclotomic.Basic.cyclotomic number)
  /-- Every earlier positive cyclotomic factor is evaluation-coprime to this stage. -/ earlierCoprime : ∀ earlier : Nat,
    0 < earlier → earlier < number →
    Dense.Rational.Divisibility.EvalCoprime (Cyclotomic.Basic.cyclotomic earlier) (Cyclotomic.Basic.cyclotomic number)

open Purelib.Data in
/-- Every positive stage of the executable construction is exact, nonzero,
and coprime to all earlier stages. -/
theorem cyclotomic_stageSpec :
    ∀ number : Nat, 0 < number → Cyclotomic.Basic.StageSpec number
  | 0, positive => False.elim ((Nat.not_lt_zero 0) positive)
  | previous + 1, positive => by
      have quotientPositive (stage : Nat) (stagePositive : 0 < stage)
          (index : Fin (stage + 1))
          (selected : 2 ≤ index.val ∧ index.val ∣ stage) :
          0 < stage / index.val :=
        Divisor.divisorQuotient_positive stagePositive selected.2
      have quotientProper (stage : Nat) (stagePositive : 0 < stage)
          (index : Fin (stage + 1))
          (selected : 2 ≤ index.val ∧ index.val ∣ stage) :
          stage / index.val < stage :=
        Division.div_lt_self stagePositive (by omega0)
      have quotientDivides (stage : Nat) (index : Fin (stage + 1))
          (selected : 2 ≤ index.val ∧ index.val ∣ stage) :
          stage / index.val ∣ stage :=
        Divisor.divisorQuotient_dvd selected.2
      have factorNormalized (stage : Nat) (stagePositive : 0 < stage)
          (stageBound : stage ≤ previous + 1)
          (index : Fin (stage + 1)) :
          (Cyclotomic.Basic.properCyclotomicFactor stage index).normalize =
            Cyclotomic.Basic.properCyclotomicFactor stage index := by
        by_cases selected : 2 ≤ index.val ∧ index.val ∣ stage
        · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_pos selected]
          have quotientLt := quotientProper stage stagePositive index selected
          exact (Purelib.NumberTheory.Cyclotomic.Basic.cyclotomic_stageSpec (stage / index.val)
            (quotientPositive stage stagePositive index selected)).normalized
        · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_neg selected]
          exact Dense.Basic.DensePolynomial.normalize_constant_of_ne
            Fraction.Field.zero_ne_one.symm
      have factorNonzero (stage : Nat) (stagePositive : 0 < stage)
          (stageBound : stage ≤ previous + 1)
          (index : Fin (stage + 1)) :
          (Cyclotomic.Basic.properCyclotomicFactor stage index).isZero = false := by
        by_cases selected : 2 ≤ index.val ∧ index.val ∣ stage
        · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_pos selected]
          have quotientLt := quotientProper stage stagePositive index selected
          exact (Purelib.NumberTheory.Cyclotomic.Basic.cyclotomic_stageSpec (stage / index.val)
            (quotientPositive stage stagePositive index selected)).nonzero
        · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_neg selected]
          exact Dense.Basic.DensePolynomial.isZero_false_of_eval_ne (x := 0) (by
            rw [Dense.Basic.DensePolynomial.eval_constant]
            exact Fraction.Field.zero_ne_one.symm)
      have factorsPairwise (stage : Nat) (stagePositive : 0 < stage)
          (stageBound : stage ≤ previous + 1) :
          ∀ first second : Fin (stage + 1), first ≠ second →
            Dense.Rational.Divisibility.EvalCoprime (Cyclotomic.Basic.properCyclotomicFactor stage first)
              (Cyclotomic.Basic.properCyclotomicFactor stage second) := by
        intro first second different
        by_cases firstSelected :
            2 ≤ first.val ∧ first.val ∣ stage
        · by_cases secondSelected :
              2 ≤ second.val ∧ second.val ∣ stage
          · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_pos firstSelected,
              Cyclotomic.Basic.properCyclotomicFactor, dif_pos secondSelected]
            have firstPositive := quotientPositive stage stagePositive
              first firstSelected
            have secondPositive := quotientPositive stage stagePositive
              second secondSelected
            have firstProper := quotientProper stage stagePositive
              first firstSelected
            have secondProper := quotientProper stage stagePositive
              second secondSelected
            have quotientDifferent : stage / first.val ≠
                stage / second.val := by
              intro quotientEqual
              apply different
              apply Fin.ext
              apply Nat.eq_of_mul_eq_mul_left firstPositive
              calc
                stage / first.val * first.val = stage :=
                  Division.div_mul_cancel firstSelected.2
                _ = stage / second.val * second.val :=
                  (Division.div_mul_cancel secondSelected.2).symm
                _ = stage / first.val * second.val := by
                  rw [quotientEqual]
            by_cases ordered : stage / first.val < stage / second.val
            · exact (Purelib.NumberTheory.Cyclotomic.Basic.cyclotomic_stageSpec (stage / second.val)
                secondPositive).earlierCoprime (stage / first.val)
                  firstPositive ordered
            · have reverse : stage / second.val < stage / first.val := by
                omega0
              exact Dense.Rational.Divisibility.evalCoprime_symm
                ((Purelib.NumberTheory.Cyclotomic.Basic.cyclotomic_stageSpec (stage / first.val)
                  firstPositive).earlierCoprime (stage / second.val)
                    secondPositive reverse)
          · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_pos firstSelected,
              Cyclotomic.Basic.properCyclotomicFactor, dif_neg secondSelected]
            exact Dense.Rational.Divisibility.evalCoprime_one_right _
        · by_cases secondSelected :
              2 ≤ second.val ∧ second.val ∣ stage
          · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_neg firstSelected,
              Cyclotomic.Basic.properCyclotomicFactor, dif_pos secondSelected]
            exact Dense.Rational.Divisibility.evalCoprime_one_left _
          · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_neg firstSelected,
              Cyclotomic.Basic.properCyclotomicFactor, dif_neg secondSelected]
            exact Dense.Rational.Divisibility.evalCoprime_one_left _
      have factorsDividePower : ∀ index : Fin (previous + 2),
          Dense.Rational.Divisibility.EvalDvd (Cyclotomic.Basic.properCyclotomicFactor (previous + 1) index)
            (Dense.Rational.PowerMinusOne.powerMinusOne (previous + 1)) := by
        intro index
        by_cases selected :
            2 ≤ index.val ∧ index.val ∣ previous + 1
        · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_pos selected]
          let quotient := (previous + 1) / index.val
          have quotientPos : 0 < quotient :=
            quotientPositive (previous + 1) positive index selected
          have quotientLt : quotient < previous + 1 :=
            quotientProper (previous + 1) positive index selected
          have quotientDvd : quotient ∣ previous + 1 :=
            quotientDivides (previous + 1) index selected
          apply Dense.Rational.Divisibility.evalDvd_trans
            (Dense.Rational.Divisibility.evalDvd_right_of_factorization
              (Purelib.NumberTheory.Cyclotomic.Basic.cyclotomic_stageSpec quotient quotientPos).factorization)
          exact Dense.Rational.PowerMinusOne.powerMinusOne_evalDvd_of_dvd quotientDvd
        · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_neg selected]
          exact Dense.Rational.Divisibility.evalDvd_one _
      have properDividesPower :
          Dense.Rational.Divisibility.EvalDvd (Cyclotomic.Basic.properCyclotomicProduct (previous + 1))
            (Dense.Rational.PowerMinusOne.powerMinusOne (previous + 1)) := by
        rw [Cyclotomic.Basic.properCyclotomicProduct]
        exact Dense.Rational.FiniteProduct.evalDvd_productFin_of_pairwise (previous + 2)
          (Cyclotomic.Basic.properCyclotomicFactor (previous + 1))
          (Dense.Rational.PowerMinusOne.powerMinusOne (previous + 1)) factorsDividePower
          (factorsPairwise (previous + 1) positive (Nat.le_refl _))
      have properNonzero :
          (Cyclotomic.Basic.properCyclotomicProduct (previous + 1)).isZero = false := by
        rw [Cyclotomic.Basic.properCyclotomicProduct]
        exact Dense.Rational.FiniteProduct.productFin_nonzero (previous + 2)
          (Cyclotomic.Basic.properCyclotomicFactor (previous + 1))
          (factorNonzero (previous + 1) positive (Nat.le_refl _))
      have remainderZero :
          (Dense.Basic.DensePolynomial.divMod (Dense.Rational.PowerMinusOne.powerMinusOne (previous + 1))
            (Cyclotomic.Basic.properCyclotomicProduct (previous + 1))).remainder.isZero = true :=
        Dense.Rational.Divisibility.divMod_remainder_isZero_of_evalDvd _ _ properNonzero
          properDividesPower
      have factorization : Dense.Rational.Divisibility.EvalEq (Dense.Rational.PowerMinusOne.powerMinusOne (previous +
        1))
          (Cyclotomic.Basic.properCyclotomicProduct (previous + 1) *
            Cyclotomic.Basic.cyclotomic (previous + 1)) := by
        intro point
        have division := Dense.Basic.DensePolynomial.divMod_eval_equation
          (Dense.Rational.PowerMinusOne.powerMinusOne (previous + 1))
          (Cyclotomic.Basic.properCyclotomicProduct (previous + 1)) point
        have remainderAtPoint := Dense.Basic.DensePolynomial.eval_eq_zero_of_isZero remainderZero point
        rw [remainderAtPoint, zero_add] at division
        rw [Cyclotomic.Basic.cyclotomic_succ, Dense.Basic.DensePolynomial.eval_mul]
        exact division.symm
      have cyclotomicNonzero :
          (Cyclotomic.Basic.cyclotomic (previous + 1)).isZero = false := by
        by_cases zero : (Cyclotomic.Basic.cyclotomic (previous + 1)).isZero = true
        · have zeroAtPoint := Dense.Basic.DensePolynomial.eval_eq_zero_of_isZero zero (0 : Fraction.Rational)
          have identity := factorization (0 : Fraction.Rational)
          rw [Dense.Rational.PowerMinusOne.eval_powerMinusOne, zero_pow (by omega0),
            Dense.Basic.DensePolynomial.eval_mul,
            zeroAtPoint, mul_zero] at identity
          have oneZero : (1 : Fraction.Rational) = 0 := by
            calc
              1 = -(-1 : Fraction.Rational) := by ring0
              _ = -0 := congrArg Neg.neg identity
              _ = 0 := by ring0
          exact (Fraction.Field.zero_ne_one oneZero.symm).elim
        · exact Bool.Decide.bool_eq_false_of_not_eq_true _ zero
      have properCoprime : Dense.Rational.Divisibility.EvalCoprime
          (Cyclotomic.Basic.properCyclotomicProduct (previous + 1))
          (Cyclotomic.Basic.cyclotomic (previous + 1)) :=
        Dense.Rational.Divisibility.evalCoprime_factors_of_squarefree
          (Dense.Rational.PowerMinusOne.powerMinusOne_normalized (previous + 1)) factorization
          (Dense.Rational.PowerMinusOne.powerMinusOne_evalCoprime_derivative previous)
      have properProductDivides (divisor : Nat) (divisorPositive : 0 < divisor)
          (divisorProper : divisor < previous + 1)
          (divisorDivides : divisor ∣ previous + 1) :
          Dense.Rational.Divisibility.EvalDvd (Cyclotomic.Basic.properCyclotomicProduct divisor)
            (Cyclotomic.Basic.properCyclotomicProduct (previous + 1)) := by
        rw [Cyclotomic.Basic.properCyclotomicProduct]
        apply Dense.Rational.FiniteProduct.evalDvd_productFin_of_pairwise
        · intro index
          by_cases selected :
              2 ≤ index.val ∧ index.val ∣ divisor
          · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_pos selected]
            have quotientPos := quotientPositive divisor divisorPositive
              index selected
            have quotientDvdDivisor := quotientDivides divisor index selected
            have quotientDvdCurrent :=
              Divisibility.trans quotientDvdDivisor divisorDivides
            have quotientLtDivisor := quotientProper divisor divisorPositive
              index selected
            exact Cyclotomic.Basic.cyclotomic_evalDvd_properProduct quotientPos
              quotientDvdCurrent (by omega0)
          · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_neg selected]
            exact Dense.Rational.Divisibility.evalDvd_one _
        · exact factorsPairwise divisor divisorPositive
            (Nat.le_of_lt divisorProper)
      have earlierCoprime : ∀ earlier : Nat, 0 < earlier →
          earlier < previous + 1 →
          Dense.Rational.Divisibility.EvalCoprime (Cyclotomic.Basic.cyclotomic earlier)
            (Cyclotomic.Basic.cyclotomic (previous + 1)) := by
        intro earlier earlierPositive earlierProper
        let common :=
          (Nat.GCD.Extended.compute earlier (previous + 1)).gcd
        have commonPositive : 0 < common := by
          exact Nat.GCD.Extended.compute_gcd_positive_right earlier positive
        have commonDividesCurrent : common ∣ previous + 1 := by
          exact (Nat.GCD.Extended.compute_spec earlier (previous + 1)).2.2
        have commonAtMostEarlier : common ≤ earlier := by
          exact Divisibility.le_of_dvd earlierPositive
            (Nat.GCD.Extended.compute_spec earlier (previous + 1)).2.1
        have commonProper : common < previous + 1 := by omega0
        have commonStage := Purelib.NumberTheory.Cyclotomic.Basic.cyclotomic_stageSpec common commonPositive
        have commonProperProductDivides := properProductDivides common
          commonPositive commonProper commonDividesCurrent
        have commonCyclotomicDivides :=
          Cyclotomic.Basic.cyclotomic_evalDvd_properProduct commonPositive
            commonDividesCurrent commonProper
        have representedCommonDivides : Dense.Rational.Divisibility.EvalDvd
            (Cyclotomic.Basic.properCyclotomicProduct common * Cyclotomic.Basic.cyclotomic common)
            (Cyclotomic.Basic.properCyclotomicProduct (previous + 1)) :=
          Dense.Rational.Divisibility.evalDvd_mul_of_coprime commonProperProductDivides
            commonCyclotomicDivides commonStage.properCoprime
        have commonPowerDivides : Dense.Rational.Divisibility.EvalDvd (Dense.Rational.PowerMinusOne.powerMinusOne
          common)
            (Cyclotomic.Basic.properCyclotomicProduct (previous + 1)) :=
          Dense.Rational.Divisibility.evalDvd_of_evalEq_divisor commonStage.factorization
            representedCommonDivides
        have commonPowerCoprime : Dense.Rational.Divisibility.EvalCoprime (Dense.Rational.PowerMinusOne.powerMinusOne
          common)
            (Cyclotomic.Basic.cyclotomic (previous + 1)) :=
          Dense.Rational.Divisibility.evalCoprime_of_evalDvd_left commonPowerDivides properCoprime
        rcases Dense.Rational.PowerMinusOne.powerMinusOne_evalBezout_gcd earlier (previous + 1) with
          ⟨gcdLeft, gcdRight, gcdIdentity⟩
        rcases commonPowerCoprime with
          ⟨commonLeft, cyclotomicRight, commonIdentity⟩
        have earlierPowerCoprime : Dense.Rational.Divisibility.EvalCoprime (Dense.Rational.PowerMinusOne.powerMinusOne
          earlier)
            (Cyclotomic.Basic.cyclotomic (previous + 1)) := by
          refine ⟨commonLeft * gcdLeft,
            commonLeft * gcdRight * Cyclotomic.Basic.properCyclotomicProduct (previous + 1) +
              cyclotomicRight, ?_⟩
          intro point
          simp only [-eq_self, -iff_self, Dense.Basic.DensePolynomial.eval_mul, Dense.Basic.DensePolynomial.eval_add]
          have gcdAtPoint := gcdIdentity point
          change (Dense.Rational.PowerMinusOne.powerMinusOne common).eval point = _ at gcdAtPoint
          calc
            1 = commonLeft.eval point * (Dense.Rational.PowerMinusOne.powerMinusOne common).eval point +
                cyclotomicRight.eval point *
                  (Cyclotomic.Basic.cyclotomic (previous + 1)).eval point :=
              commonIdentity point
            _ = commonLeft.eval point *
                  (gcdLeft.eval point * (Dense.Rational.PowerMinusOne.powerMinusOne earlier).eval point +
                    gcdRight.eval point *
                      (Dense.Rational.PowerMinusOne.powerMinusOne (previous + 1)).eval point) +
                cyclotomicRight.eval point *
                  (Cyclotomic.Basic.cyclotomic (previous + 1)).eval point := by
                    rw [gcdAtPoint]
            _ = (commonLeft.eval point * gcdLeft.eval point) *
                  (Dense.Rational.PowerMinusOne.powerMinusOne earlier).eval point +
                (commonLeft.eval point * gcdRight.eval point *
                    (Cyclotomic.Basic.properCyclotomicProduct (previous + 1)).eval point +
                  cyclotomicRight.eval point) *
                    (Cyclotomic.Basic.cyclotomic (previous + 1)).eval point := by
                      rw [factorization point, Dense.Basic.DensePolynomial.eval_mul]
                      ring0
        exact Dense.Rational.Divisibility.evalCoprime_of_evalDvd_left
          (Dense.Rational.Divisibility.evalDvd_right_of_factorization
            (Purelib.NumberTheory.Cyclotomic.Basic.cyclotomic_stageSpec earlier earlierPositive).factorization)
          earlierPowerCoprime
      exact
        { normalized := by
            rw [Cyclotomic.Basic.cyclotomic_succ]
            exact Dense.Rational.Division.Normalized.divMod_quotient_normalized _ _
          nonzero := cyclotomicNonzero
          factorization := factorization
          properCoprime := properCoprime
          earlierCoprime := earlierCoprime }
termination_by number => number
decreasing_by all_goals omega0

/-- Every slot in the proper-divisor product at a positive stage is nonzero. -/
theorem properCyclotomicFactor_nonzero (number : Nat)
    (positive : 0 < number) (index : Fin (number + 1)) :
    (Cyclotomic.Basic.properCyclotomicFactor number index).isZero = false := by
  by_cases selected : 2 ≤ index.val ∧ index.val ∣ number
  · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_pos selected]
    exact (Cyclotomic.Basic.cyclotomic_stageSpec (number / index.val)
      (Divisor.divisorQuotient_positive positive selected.2)).nonzero
  · rw [Cyclotomic.Basic.properCyclotomicFactor, dif_neg selected]
    exact Dense.Basic.DensePolynomial.isZero_false_of_eval_ne (x := 0) (by
      rw [Dense.Basic.DensePolynomial.eval_constant]
      exact Fraction.Field.zero_ne_one.symm)

/-- The complete proper-divisor product at a positive stage is nonzero. -/
theorem properCyclotomicProduct_nonzero (number : Nat)
    (positive : 0 < number) :
    (Cyclotomic.Basic.properCyclotomicProduct number).isZero = false := by
  rw [Cyclotomic.Basic.properCyclotomicProduct]
  exact Dense.Rational.FiniteProduct.productFin_nonzero (number + 1) (Cyclotomic.Basic.properCyclotomicFactor number)
    (Cyclotomic.Basic.properCyclotomicFactor_nonzero number positive)

open Purelib.Data in
/-- The executable quotient at positive index `n` has exactly the finite
Euler-totient degree. -/
theorem cyclotomic_natDegree : ∀ number : Nat, 0 < number →
    (Cyclotomic.Basic.cyclotomic number).natDegree = Totient.Basic.totient number
  | 0, positive => False.elim ((Nat.not_lt_zero 0) positive)
  | previous + 1, positive => by
      have termSplit (index : Fin (previous + 2)) :
          (if Nat.Decide.divisibilityTest index.val (previous + 1) then
              Totient.Basic.totient ((previous + 1) / index.val) else 0) =
            (Cyclotomic.Basic.properCyclotomicFactor (previous + 1) index).natDegree +
              (if Nat.Decide.natEquals index.val 1 then
                Totient.Basic.totient (previous + 1) else 0) := by
        by_cases divides : index.val ∣ previous + 1
        · rw [show Nat.Decide.divisibilityTest index.val (previous + 1) = true by
              exact (Nat.Decide.divisibilityTest_eq_true _ _).2 divides]
          by_cases large : 2 ≤ index.val
          · have selected : 2 ≤ index.val ∧ index.val ∣ previous + 1 :=
              ⟨large, divides⟩
            have indexNotOne : index.val ≠ 1 := by omega0
            rw [if_pos rfl, Cyclotomic.Basic.properCyclotomicFactor, dif_pos selected,
              Purelib.NumberTheory.Cyclotomic.Basic.cyclotomic_natDegree ((previous + 1) / index.val)
                (Divisor.divisorQuotient_positive positive divides),
              show Nat.Decide.natEquals index.val 1 = false by
                exact Bool.Decide.bool_eq_false_of_not_eq_true _ (fun equal =>
                  indexNotOne
                    ((Nat.Decide.natEquals_eq_true index.val 1).1 equal)),
              if_neg (by decide), Nat.add_zero]
            omega0
          · have indexPositive : 0 < index.val := by
              by_contra notPositive
              have indexZero : index.val = 0 :=
                Nat.eq_zero_of_not_pos notPositive
              have zeroDivides : 0 ∣ previous + 1 := by
                rw [← indexZero]
                exact divides
              have currentZero := Nat.eq_zero_of_zero_dvd zeroDivides
              exact (Nat.ne_of_gt positive currentZero).elim
            have indexOne : index.val = 1 := by omega0
            have notSelected : ¬(2 ≤ index.val ∧
                index.val ∣ previous + 1) := by omega0
            rw [if_pos rfl, Cyclotomic.Basic.properCyclotomicFactor, dif_neg notSelected,
              indexOne, Division.div_one,
              show Nat.Decide.natEquals 1 1 = true by
                exact (Nat.Decide.natEquals_eq_true 1 1).2 rfl,
              if_pos rfl]
            rw [Dense.Rational.Divisibility.natDegree_constant_one, Nat.zero_add]
        · have notSelected : ¬(2 ≤ index.val ∧
              index.val ∣ previous + 1) := fun selected =>
                divides selected.2
          have indexNotOne : index.val ≠ 1 := by
            intro indexOne
            apply divides
            rw [indexOne]
            exact one_dvd _
          rw [show Nat.Decide.divisibilityTest index.val (previous + 1) = false by
                exact Bool.Decide.bool_eq_false_of_not_eq_true _ (fun truth =>
                  divides ((Nat.Decide.divisibilityTest_eq_true _ _).1 truth)),
            if_neg (by decide), Cyclotomic.Basic.properCyclotomicFactor, dif_neg notSelected,
            show Nat.Decide.natEquals index.val 1 = false by
                exact Bool.Decide.bool_eq_false_of_not_eq_true _ (fun equal =>
                  indexNotOne
                    ((Nat.Decide.natEquals_eq_true index.val 1).1 equal)),
            if_neg (by decide)]
          rw [Dense.Rational.Divisibility.natDegree_constant_one, Nat.zero_add]
      have divisorSumSplit :
          Totient.Basic.divisorQuotientTotientSum (previous + 1) =
            Nat.FiniteSum.sumFinNat (previous + 2) (fun index =>
              (Cyclotomic.Basic.properCyclotomicFactor (previous + 1) index).natDegree) +
              Totient.Basic.totient (previous + 1) := by
        unfold Totient.Basic.divisorQuotientTotientSum
        calc
          Nat.FiniteSum.natSum (previous + 2) (fun divisor =>
              if Nat.Decide.divisibilityTest divisor (previous + 1) then
                Totient.Basic.totient ((previous + 1) / divisor) else 0) =
            Nat.FiniteSum.sumFinNat (previous + 2) (fun index =>
                (Cyclotomic.Basic.properCyclotomicFactor (previous + 1) index).natDegree) +
              Nat.FiniteSum.natSum (previous + 2) (fun divisor =>
                if Nat.Decide.natEquals divisor 1 then
                  Totient.Basic.totient (previous + 1) else 0) :=
              Nat.FiniteSum.natSum_eq_sumFinNat_add _ _ _ _ termSplit
          _ = Nat.FiniteSum.sumFinNat (previous + 2) (fun index =>
                (Cyclotomic.Basic.properCyclotomicFactor (previous + 1) index).natDegree) +
              Totient.Basic.totient (previous + 1) := by
                rw [Nat.FiniteSum.natSum_singletonWeight]
                rw [show Nat.Decide.natLess 1 (previous + 2) = true by
                  exact (Nat.Decide.natLess_eq_true 1 (previous + 2)).2
                    (by omega0)]
                rfl
      have properDegree :
          (Cyclotomic.Basic.properCyclotomicProduct (previous + 1)).natDegree =
            Nat.FiniteSum.sumFinNat (previous + 2) (fun index =>
              (Cyclotomic.Basic.properCyclotomicFactor (previous + 1) index).natDegree) := by
        rw [Cyclotomic.Basic.properCyclotomicProduct]
        exact Dense.Rational.FiniteProduct.natDegree_productFin (previous + 2)
          (Cyclotomic.Basic.properCyclotomicFactor (previous + 1))
          (Cyclotomic.Basic.properCyclotomicFactor_nonzero (previous + 1) positive)
      have stage := Cyclotomic.Basic.cyclotomic_stageSpec (previous + 1) positive
      have representedFactorization : Dense.Rational.PowerMinusOne.powerMinusOne (previous + 1) =
          Cyclotomic.Basic.properCyclotomicProduct (previous + 1) *
            Cyclotomic.Basic.cyclotomic (previous + 1) :=
        Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
          (Dense.Rational.PowerMinusOne.powerMinusOne_normalized (previous + 1))
            (Dense.Basic.DensePolynomial.normalize_mul _ _)
          stage.factorization
      have degreeIdentity := congrArg
        (fun polynomial : Polynomial.Dense.Rational.Divisibility.CoefficientPolynomial => polynomial.natDegree)
        representedFactorization
      rw [Dense.Rational.PowerMinusOne.powerMinusOne_natDegree previous,
        Dense.Basic.DensePolynomial.natDegree_mul (Cyclotomic.Basic.properCyclotomicProduct_nonzero (previous + 1)
          positive)
          stage.nonzero,
        properDegree] at degreeIdentity
      have divisorDegreeTotal :=
        Totient.Basic.divisorQuotientTotientSum_eq (previous + 1)
      rw [divisorSumSplit] at divisorDegreeTotal
      omega0
termination_by number => number
decreasing_by all_goals
  exact Division.div_lt_self (by omega0) (by omega0)

end Purelib.NumberTheory.Cyclotomic.Basic

end

section
@[expose] public section

/-!
# The finite Goh--Wildberger spread-cyclotomic factorization

This file completes Exercise 8.13 without roots, completed fields, or an
infinite polynomial family.  Ordinary cyclotomic factors are constructed by
finite monic long division over the constructive rationals.  Their integer
coefficients are reduced through the formal quadratic relation
`a^2 = t*a - 1`, and the resulting norm is evaluated at `t = 2 - 4s`.

The sole exceptional norm is `Phi_1`, whose norm is `4s`; this supplies the
one global factor `4` in the spread--Lucas identity.  Cancellation is done
only over the constructive rationals, after which the resulting integer
coefficient identity is transported to every explicitly supplied field,
including finite characteristic.
-/

namespace Purelib.NumberTheory.Cyclotomic.Basic.ExerciseEightThirteen.IntegerPolynomial

variable {K : Type*} [ExplicitField K]

section ExerciseEightThirteen
section IntegerPolynomial

/-- The first finite ordinary cyclotomic factor is `X-1`. -/
theorem
  cyclotomic_one_eq_powerMinusOne_one
  :
    Cyclotomic.Basic.cyclotomic 1 =
      Dense.Rational.PowerMinusOne.powerMinusOne 1 := by
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (Cyclotomic.Basic.cyclotomic_stageSpec 1 (by omega0)).normalized
    (Dense.Rational.PowerMinusOne.powerMinusOne_normalized 1)
  intro point
  have factorization :=
    (Cyclotomic.Basic.cyclotomic_stageSpec 1 (by omega0)).factorization
      point
  have properValue :
      (Cyclotomic.Basic.properCyclotomicProduct 1).eval point = 1 := by
    unfold Cyclotomic.Basic.properCyclotomicProduct
    rw [Dense.Rational.FiniteProduct.productFin_succ,
      Dense.Rational.FiniteProduct.productFin_succ,
      Dense.Rational.FiniteProduct.productFin_zero]
    simp only [-eq_self, -iff_self, Cyclotomic.Basic.properCyclotomicFactor,
      Fin.val_last, Fin.val_castSucc]
    rw [dif_neg (by omega0), dif_neg (by omega0)]
    simp only [-eq_self, -iff_self, Dense.Basic.DensePolynomial.eval_mul,
      Dense.Basic.DensePolynomial.eval_constant, one_mul]
    rfl
  rw [Dense.Basic.DensePolynomial.eval_mul,
    properValue, one_mul] at factorization
  exact factorization.symm
end IntegerPolynomial
end ExerciseEightThirteen
end Purelib.NumberTheory.Cyclotomic.Basic.ExerciseEightThirteen.IntegerPolynomial

end
