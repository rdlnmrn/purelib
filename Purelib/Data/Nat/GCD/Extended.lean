module
import Purelib.Tactic.Ring

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Nat.Divisibility
import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Int.Divisibility
meta import Purelib.Elab.ConstructiveInjectivity

section
public section

/-!
# Structurally recursive certified greatest common divisors

This module supplies the finite arithmetic certificate needed by the
quotient-free rational carrier.  Its Euclidean algorithm recurses on an
explicit natural-number fuel argument.  In particular, its correctness proof
does not use the well-founded-recursion equation theorem through which the
upstream `Nat.gcd` proof API currently acquires `Quot.sound`.
-/

namespace Purelib.Data.Nat.GCD.Extended

open Purelib.Data Purelib.Data.Int

@[expose] public section

set_option genInjectivity false in
/-- The natural gcd and two integer coefficients computed by extended Euclid.

The scalar field is accompanied by the left and right coefficients. Correctness
theorems certify their Bézout identity and common divisibility for sufficiently
fueled execution. -/
structure Result where
  /-- The computed natural common divisor. -/ gcd : Nat
  /-- The retained integer coefficient of the original left input. -/ left : Int
  /-- The retained integer coefficient of the original right input. -/ right : Int
deriving DecidableEq

constructive_injectivity Result

section

open Purelib.Data.Nat.GCD.Extended

end

end

open Purelib.Data.Nat.GCD

section
open Purelib.Data.Nat.GCD.Extended
/-- One structurally recursive run of the extended Euclidean algorithm.

The correctness theorem below requires `rightInput < fuel`. The otherwise unreachable
zero-fuel branch returns the left input so that the definition is total and
executable on every input. -/
@[expose] def computeAux : Nat → Nat → Nat → Result
  | 0, leftInput, _ => ⟨leftInput, 1, 0⟩
  | _ + 1, leftInput, 0 => ⟨leftInput, 1, 0⟩
  | fuel + 1, leftInput, rightInput + 1 =>
      let previous :=
        computeAux fuel (rightInput + 1) (leftInput % (rightInput + 1))
      ⟨previous.gcd, previous.right,
        previous.left - (leftInput / (rightInput + 1) : Nat) * previous.right⟩

/-- Run extended Euclid with accumulated integer coefficient pairs.

The two coefficient pairs express the current remainders in terms of the original
inputs. Each recursive step updates the retained matrix before continuing, so no
result is rebuilt while recursion unwinds. -/
@[expose] def computeTailAux : Nat -> Nat -> Nat -> Int -> Int -> Int -> Int ->
  Result
  | 0, leftInput, _rightInput, leftLeft, leftRight, _rightLeft, _rightRight =>
      ⟨leftInput, leftLeft, leftRight⟩
  | _fuel + 1, leftInput, 0, leftLeft, leftRight, _rightLeft, _rightRight =>
      ⟨leftInput, leftLeft, leftRight⟩
  | fuel + 1, leftInput, rightInput + 1,
      leftLeft, leftRight, rightLeft, rightRight =>
      let quotient := leftInput / (rightInput + 1)
      computeTailAux fuel (rightInput + 1) (leftInput % (rightInput + 1))
        rightLeft rightRight
        (leftLeft - (quotient : Int) * rightLeft)
        (leftRight - (quotient : Int) * rightRight)

end

section
open Purelib.Data.Nat.GCD
open Purelib.Data.Nat.GCD.Extended in
/-- Compute a natural gcd together with explicit integer Bézout coefficients.

The tail-recursive evaluator starts with the identity coefficient matrix and
rightInput + 1 units of fuel, which suffice for the Euclidean remainder sequence. -/
@[expose] def compute (leftInput rightInput : Nat) : Result :=
  computeTailAux (rightInput + 1) leftInput rightInput 1 0 0 1

/-- The structurally recursive Euclidean result certifies both original inputs.

The retained strict fuel bound supplies enough subtraction steps for its
Bézout identity and the two natural divisibility witnesses. -/
theorem computeAux_spec (fuel leftInput rightInput : Nat)
    (enoughFuel : rightInput < fuel) :
    let result := computeAux fuel leftInput rightInput
    (result.gcd : Int) =
        result.left * (leftInput : Int) +
          result.right * (rightInput : Int) ∧
      result.gcd ∣ leftInput ∧ result.gcd ∣ rightInput := by
  induction fuel generalizing leftInput rightInput with
  | zero => exact (Nat.not_lt_zero _ enoughFuel).elim
  | succ fuel inductionHypothesis =>
      cases rightInput with
      | zero =>
          change
            (leftInput : Int) =
                1 * (leftInput : Int) + 0 * (0 : Int) ∧
              leftInput ∣ leftInput ∧ leftInput ∣ 0
          exact
            ⟨by rw [Int.one_mul, Arithmetic.zero_mul, Int.add_zero],
              Divisibility.refl leftInput, Divisibility.zero leftInput⟩
      | succ rightInput =>
          have rightPositive : 0 < rightInput + 1 := Nat.zero_lt_succ _
          have rightAtMostFuel : rightInput + 1 ≤ fuel :=
            Nat.le_of_lt_succ enoughFuel
          have remainderBelowFuel :
              leftInput % (rightInput + 1) < fuel :=
            Nat.lt_of_lt_of_le (Nat.mod_lt _ rightPositive) rightAtMostFuel
          have previousSpec := inductionHypothesis
            (rightInput + 1) (leftInput % (rightInput + 1))
            remainderBelowFuel
          let previous :=
            computeAux fuel (rightInput + 1) (leftInput % (rightInput + 1))
          have previousIdentity :
              (previous.gcd : Int) =
                previous.left * ((rightInput + 1 : Nat) : Int) +
                  previous.right *
                    ((leftInput % (rightInput + 1) : Nat) : Int) :=
            previousSpec.1
          have divisionIdentity :
              ((leftInput % (rightInput + 1) : Nat) : Int) +
                  ((rightInput + 1 : Nat) : Int) *
                    ((leftInput / (rightInput + 1) : Nat) : Int) =
                (leftInput : Int) := by
            have naturalIdentity :=
              congrArg (fun value : Nat => (value : Int))
                (Division.mod_add_div leftInput (rightInput + 1))
            simpa only [Int.natCast_add, Int.natCast_mul] using naturalIdentity
          have currentIdentity :
              (previous.gcd : Int) =
                previous.right * (leftInput : Int) +
                  (previous.left -
                    ((leftInput / (rightInput + 1) : Nat) : Int) *
                      previous.right) *
                    ((rightInput + 1 : Nat) : Int) := by
            rw [previousIdentity]
            calc
              previous.left * ((rightInput + 1 : Nat) : Int) +
                    previous.right * ((leftInput % (rightInput + 1) : Nat) : Int) =
                  previous.right *
                    (((leftInput % (rightInput + 1) : Nat) : Int) +
                      ((rightInput + 1 : Nat) : Int) *
                        ((leftInput / (rightInput + 1) : Nat) : Int)) +
                    (previous.left -
                      ((leftInput / (rightInput + 1) : Nat) : Int) * previous.right) *
                      ((rightInput + 1 : Nat) : Int) := by ring1
              _ = previous.right * (leftInput : Int) +
                    (previous.left -
                      ((leftInput / (rightInput + 1) : Nat) : Int) * previous.right) *
                      ((rightInput + 1 : Nat) : Int) := by rw [divisionIdentity]
          have dividesLeftInput : previous.gcd ∣ leftInput := by
            have dividesProduct :
                previous.gcd ∣
                  (rightInput + 1) * (leftInput / (rightInput + 1)) :=
              Divisibility.mul_right previousSpec.2.1 _
            have dividesSum :
                previous.gcd ∣
                  leftInput % (rightInput + 1) +
                    (rightInput + 1) * (leftInput / (rightInput + 1)) :=
              Divisibility.add previousSpec.2.2 dividesProduct
            rw [Division.mod_add_div] at dividesSum
            exact dividesSum
          change
            (previous.gcd : Int) =
                previous.right * (leftInput : Int) +
                  (previous.left -
                    ((leftInput / (rightInput + 1) : Nat) : Int) *
                      previous.right) *
                    ((rightInput + 1 : Nat) : Int) ∧
              previous.gcd ∣ leftInput ∧ previous.gcd ∣ rightInput + 1
          exact ⟨currentIdentity, dividesLeftInput, previousSpec.2.1⟩

/-- The tail-recursive coefficient state retains its displayed linear combination of the
two original inputs.

The accumulated integer coefficient pairs express each current remainder in terms
of the fixed original inputs. A strict fuel bound retains this identity through
every Euclidean step. -/
theorem computeTailAux_identity (fuel leftInput rightInput : Nat)
    (leftLeft leftRight rightLeft rightRight : Int)
    (originalLeft originalRight : Nat)
    (enoughFuel : rightInput < fuel)
    (leftIdentity : (leftInput : Int) =
      leftLeft * (originalLeft : Int) +
        leftRight * (originalRight : Int))
    (rightIdentity : (rightInput : Int) =
      rightLeft * (originalLeft : Int) +
        rightRight * (originalRight : Int)) :
    let result := computeTailAux fuel leftInput rightInput leftLeft leftRight
      rightLeft rightRight
    (result.gcd : Int) =
      result.left * (originalLeft : Int) +
        result.right * (originalRight : Int) := by
  induction fuel generalizing leftInput rightInput leftLeft leftRight
      rightLeft rightRight with
  | zero => exact (Nat.not_lt_zero _ enoughFuel).elim
  | succ fuel inductionHypothesis =>
      cases rightInput with
      | zero =>
          change (leftInput : Int) =
            leftLeft * (originalLeft : Int) +
              leftRight * (originalRight : Int)
          exact leftIdentity
      | succ rightInput =>
          have rightPositive : 0 < rightInput + 1 := Nat.zero_lt_succ _
          have rightAtMostFuel : rightInput + 1 <= fuel :=
            Nat.le_of_lt_succ enoughFuel
          have remainderBelowFuel :
              leftInput % (rightInput + 1) < fuel :=
            Nat.lt_of_lt_of_le (Nat.mod_lt _ rightPositive) rightAtMostFuel
          have divisionIdentity :
              ((leftInput % (rightInput + 1) : Nat) : Int) +
                  ((rightInput + 1 : Nat) : Int) *
                    ((leftInput / (rightInput + 1) : Nat) : Int) =
                (leftInput : Int) := by
            have naturalIdentity :=
              congrArg (fun value : Nat => (value : Int))
                (Division.mod_add_div leftInput (rightInput + 1))
            simpa only [Int.natCast_add, Int.natCast_mul] using naturalIdentity
          have remainderIdentity :
              ((leftInput % (rightInput + 1) : Nat) : Int) =
                (leftLeft -
                    ((leftInput / (rightInput + 1) : Nat) : Int) *
                      rightLeft) *
                    (originalLeft : Int) +
                  (leftRight -
                    ((leftInput / (rightInput + 1) : Nat) : Int) *
                      rightRight) *
                    (originalRight : Int) := by
            calc
              ((leftInput % (rightInput + 1) : Nat) : Int) =
                  (leftInput : Int) -
                    ((rightInput + 1 : Nat) : Int) *
                      ((leftInput / (rightInput + 1) : Nat) : Int) := by
                rw [<- divisionIdentity]
                ring1
              _ = (leftLeft -
                      ((leftInput / (rightInput + 1) : Nat) : Int) *
                        rightLeft) *
                      (originalLeft : Int) +
                    (leftRight -
                      ((leftInput / (rightInput + 1) : Nat) : Int) *
                        rightRight) *
                      (originalRight : Int) := by
                rw [leftIdentity, rightIdentity]
                ring1
          exact inductionHypothesis (rightInput + 1)
            (leftInput % (rightInput + 1)) rightLeft rightRight
            (leftLeft -
              ((leftInput / (rightInput + 1) : Nat) : Int) * rightLeft)
            (leftRight -
              ((leftInput / (rightInput + 1) : Nat) : Int) * rightRight)
            remainderBelowFuel rightIdentity remainderIdentity

/-- The gcd returned by the tail-recursive state divides both current remainders,
independently of the accumulated Bézout coefficients.

A strict fuel bound suffices for the Euclidean remainder recursion. The returned
natural divisor divides both current inputs for every retained coefficient state. -/
theorem computeTailAux_dvd (fuel leftInput rightInput : Nat)
    (leftLeft leftRight rightLeft rightRight : Int)
    (enoughFuel : rightInput < fuel) :
    let result := computeTailAux fuel leftInput rightInput leftLeft leftRight
      rightLeft rightRight
    result.gcd ∣ leftInput /\ result.gcd ∣ rightInput := by
  induction fuel generalizing leftInput rightInput leftLeft leftRight
      rightLeft rightRight with
  | zero => exact (Nat.not_lt_zero _ enoughFuel).elim
  | succ fuel inductionHypothesis =>
      cases rightInput with
      | zero =>
          exact ⟨Divisibility.refl leftInput, Divisibility.zero leftInput⟩
      | succ rightInput =>
          have rightPositive : 0 < rightInput + 1 := Nat.zero_lt_succ _
          have rightAtMostFuel : rightInput + 1 <= fuel :=
            Nat.le_of_lt_succ enoughFuel
          have remainderBelowFuel :
              leftInput % (rightInput + 1) < fuel :=
            Nat.lt_of_lt_of_le (Nat.mod_lt _ rightPositive) rightAtMostFuel
          let result := computeTailAux fuel (rightInput + 1)
            (leftInput % (rightInput + 1)) rightLeft rightRight
            (leftLeft -
              ((leftInput / (rightInput + 1) : Nat) : Int) * rightLeft)
            (leftRight -
              ((leftInput / (rightInput + 1) : Nat) : Int) * rightRight)
          have recursive := inductionHypothesis (rightInput + 1)
            (leftInput % (rightInput + 1)) rightLeft rightRight
            (leftLeft -
              ((leftInput / (rightInput + 1) : Nat) : Int) * rightLeft)
            (leftRight -
              ((leftInput / (rightInput + 1) : Nat) : Int) * rightRight)
            remainderBelowFuel
          have dividesProduct : result.gcd ∣
              (rightInput + 1) * (leftInput / (rightInput + 1)) :=
            Divisibility.mul_right recursive.1 _
          have dividesLeft : result.gcd ∣ leftInput := by
            have dividesSum := Divisibility.add recursive.2 dividesProduct
            rw [Division.mod_add_div] at dividesSum
            exact dividesSum
          exact ⟨dividesLeft, recursive.1⟩

/-- The computed extended Euclidean result satisfies its Bézout and divisibility laws.

With the internally supplied fuel, the returned scalar divides both natural inputs
and its integer cast is the linear combination given by the two computed
coefficients. -/
theorem compute_spec (leftInput rightInput : Nat) :
    let result := compute leftInput rightInput
    (result.gcd : Int) =
        result.left * (leftInput : Int) +
          result.right * (rightInput : Int) ∧
      result.gcd ∣ leftInput ∧ result.gcd ∣ rightInput :=
  by
    let result := compute leftInput rightInput
    have identity := computeTailAux_identity (rightInput + 1) leftInput
      rightInput 1 0 0 1 leftInput rightInput
      (Nat.lt_succ_self rightInput) (by ring1) (by ring1)
    have divides := computeTailAux_dvd (rightInput + 1) leftInput rightInput
      1 0 0 1 (Nat.lt_succ_self rightInput)
    exact ⟨identity, divides⟩

/-- A positive right input gives a strictly positive computed gcd. -/
theorem compute_gcd_positive_right (leftInput : Nat) {rightInput : Nat}
    (rightPositive : 0 < rightInput) :
    0 < (compute leftInput rightInput).gcd :=
  Nat.pos_of_dvd_of_pos (compute_spec leftInput rightInput).2.2 rightPositive

/-- Every displayed common divisor divides the computed Euclidean result.

The retained Bézout identity expresses the computed gcd as a signed linear
combination of the original inputs. Their divisibility witnesses transport
through that combination to a natural witness for the computed gcd. -/
theorem commonDivisor_dvd_compute_gcd
    (leftInput rightInput commonDivisor : Nat)
    (dividesLeft : commonDivisor ∣ leftInput)
    (dividesRight : commonDivisor ∣ rightInput) :
    commonDivisor ∣ (compute leftInput rightInput).gcd := by
  let result := compute leftInput rightInput
  have specification := compute_spec leftInput rightInput
  have castDividesLeft : (commonDivisor : Int) ∣ (leftInput : Int) := by
    exact Int.Divisibility.of_nat dividesLeft
  have castDividesRight : (commonDivisor : Int) ∣ (rightInput : Int) := by
    exact Int.Divisibility.of_nat dividesRight
  have dividesIdentity : (commonDivisor : Int) ∣
      result.left * (leftInput : Int) + result.right * (rightInput : Int) :=
    Int.Divisibility.add (Int.Divisibility.mul_left castDividesLeft result.left)
      (Int.Divisibility.mul_left castDividesRight result.right)
  rw [← specification.1] at dividesIdentity
  exact Int.Divisibility.to_nat dividesIdentity

/-- The certified Euclidean result for a zero left input is the right input.

Both inequalities are explicit divisibility certificates. -/
theorem compute_gcd_zero_left (rightInput : Nat) :
    (compute 0 rightInput).gcd = rightInput := by
  have resultDividesRight := (compute_spec 0 rightInput).2.2
  have rightDividesResult := commonDivisor_dvd_compute_gcd
    0 rightInput rightInput (Divisibility.zero rightInput) (Divisibility.refl rightInput)
  exact Divisibility.antisymm resultDividesRight rightDividesResult

/-- The certified Euclidean result for a zero right input is the left input. -/
theorem compute_gcd_zero_right (leftInput : Nat) :
    (compute leftInput 0).gcd = leftInput := by
  have resultDividesLeft := (compute_spec leftInput 0).2.1
  have leftDividesResult := commonDivisor_dvd_compute_gcd
    leftInput 0 leftInput (Divisibility.refl leftInput) (Divisibility.zero leftInput)
  exact Divisibility.antisymm resultDividesLeft leftDividesResult

/-- Subtracting the left input from the larger right input preserves the certified gcd.

When the left input does not exceed the right input, subtracting it leaves the
same greatest common divisor, including the zero-input cases. -/
theorem compute_gcd_sub_right {leftInput rightInput : Nat}
    (ordered : leftInput ≤ rightInput) :
    (compute leftInput (rightInput - leftInput)).gcd =
      (compute leftInput rightInput).gcd := by
  let reduced := compute leftInput (rightInput - leftInput)
  let whole := compute leftInput rightInput
  have reducedSpec := compute_spec leftInput (rightInput - leftInput)
  have wholeSpec := compute_spec leftInput rightInput
  have reducedDividesRight : reduced.gcd ∣ rightInput := by
    have dividesSum := Divisibility.add reducedSpec.2.1 reducedSpec.2.2
    have reconstructed : leftInput + (rightInput - leftInput) = rightInput :=
      Subtraction.add_sub_of_le ordered
    rw [reconstructed] at dividesSum
    exact dividesSum
  have reducedDividesWhole : reduced.gcd ∣ whole.gcd :=
    commonDivisor_dvd_compute_gcd leftInput rightInput reduced.gcd
      reducedSpec.2.1 reducedDividesRight
  have wholeDividesDifference : whole.gcd ∣ rightInput - leftInput :=
    Divisibility.sub wholeSpec.2.2 wholeSpec.2.1
  have wholeDividesReduced : whole.gcd ∣ reduced.gcd :=
    commonDivisor_dvd_compute_gcd leftInput (rightInput - leftInput)
      whole.gcd wholeSpec.2.1 wholeDividesDifference
  exact Divisibility.antisymm reducedDividesWhole wholeDividesReduced

/-- Subtracting the right input from the larger left input preserves the certified gcd.

When the right input does not exceed the left input, subtracting it leaves the
same greatest common divisor, including the zero-input cases. -/
theorem compute_gcd_sub_left {leftInput rightInput : Nat}
    (ordered : rightInput ≤ leftInput) :
    (compute (leftInput - rightInput) rightInput).gcd =
      (compute leftInput rightInput).gcd := by
  let reduced := compute (leftInput - rightInput) rightInput
  let whole := compute leftInput rightInput
  have reducedSpec := compute_spec (leftInput - rightInput) rightInput
  have wholeSpec := compute_spec leftInput rightInput
  have reducedDividesLeft : reduced.gcd ∣ leftInput := by
    have dividesSum := Divisibility.add reducedSpec.2.1 reducedSpec.2.2
    have reconstructed : leftInput - rightInput + rightInput = leftInput :=
      (Nat.add_comm _ _).trans (Subtraction.add_sub_of_le ordered)
    rw [reconstructed] at dividesSum
    exact dividesSum
  have reducedDividesWhole : reduced.gcd ∣ whole.gcd :=
    commonDivisor_dvd_compute_gcd leftInput rightInput reduced.gcd
      reducedDividesLeft reducedSpec.2.2
  have wholeDividesDifference : whole.gcd ∣ leftInput - rightInput :=
    Divisibility.sub wholeSpec.2.1 wholeSpec.2.2
  have wholeDividesReduced : whole.gcd ∣ reduced.gcd :=
    commonDivisor_dvd_compute_gcd (leftInput - rightInput) rightInput
      whole.gcd wholeDividesDifference wholeSpec.2.2
  exact Divisibility.antisymm reducedDividesWhole wholeDividesReduced

end

/-- Scaling both Euclidean inputs scales the computed gcd.

The stored divisibility and Bézout identities give both divisibility
directions for every natural scaling factor, including zero. -/
theorem compute_gcd_mul_left (factor leftInput rightInput : Nat) :
    (compute (factor * leftInput) (factor * rightInput)).gcd =
      factor * (compute leftInput rightInput).gcd := by
  let base := compute leftInput rightInput
  let scaled := compute (factor * leftInput) (factor * rightInput)
  have baseSpec := compute_spec leftInput rightInput
  have scaledSpec := compute_spec
    (factor * leftInput) (factor * rightInput)
  have factorBaseDividesLeft : factor * base.gcd ∣ factor * leftInput := by
    rcases baseSpec.2.1 with ⟨leftQuotient, leftEquation⟩
    refine ⟨leftQuotient, ?_⟩
    rw [leftEquation]
    change factor * (base.gcd * leftQuotient) =
      (factor * base.gcd) * leftQuotient
    exact (Multiplication.mul_assoc factor base.gcd leftQuotient).symm
  have factorBaseDividesRight : factor * base.gcd ∣ factor * rightInput := by
    rcases baseSpec.2.2 with ⟨rightQuotient, rightEquation⟩
    refine ⟨rightQuotient, ?_⟩
    rw [rightEquation]
    change factor * (base.gcd * rightQuotient) =
      (factor * base.gcd) * rightQuotient
    exact (Multiplication.mul_assoc factor base.gcd rightQuotient).symm
  have factorBaseDividesScaled : factor * base.gcd ∣ scaled.gcd :=
    commonDivisor_dvd_compute_gcd
      (factor * leftInput) (factor * rightInput) (factor * base.gcd)
      factorBaseDividesLeft factorBaseDividesRight
  have scaledDividesFactorBase : scaled.gcd ∣ factor * base.gcd := by
    have scaledDividesLeftInt : (scaled.gcd : Int) ∣
        ((factor * leftInput : Nat) : Int) := by
      exact Int.Divisibility.of_nat scaledSpec.2.1
    have scaledDividesRightInt : (scaled.gcd : Int) ∣
        ((factor * rightInput : Nat) : Int) := by
      exact Int.Divisibility.of_nat scaledSpec.2.2
    have dividesCombination : (scaled.gcd : Int) ∣
        base.left * ((factor * leftInput : Nat) : Int) +
          base.right * ((factor * rightInput : Nat) : Int) :=
      Int.Divisibility.add (Int.Divisibility.mul_left scaledDividesLeftInt base.left)
        (Int.Divisibility.mul_left scaledDividesRightInt base.right)
    have combinationEquals :
        base.left * ((factor * leftInput : Nat) : Int) +
            base.right * ((factor * rightInput : Nat) : Int) =
          ((factor * base.gcd : Nat) : Int) := by
      calc
        base.left * ((factor * leftInput : Nat) : Int) +
              base.right * ((factor * rightInput : Nat) : Int) =
            (factor : Int) *
              (base.left * (leftInput : Int) +
                base.right * (rightInput : Int)) := by
                  simp only [Int.natCast_mul]
                  ring1
        _ = (factor : Int) * (base.gcd : Int) := by rw [← baseSpec.1]
        _ = ((factor * base.gcd : Nat) : Int) := by
          rw [Int.natCast_mul]
    rw [combinationEquals] at dividesCombination
    exact Int.Divisibility.to_nat dividesCombination
  exact Divisibility.antisymm scaledDividesFactorBase factorBaseDividesScaled
end Purelib.Data.Nat.GCD.Extended

end
