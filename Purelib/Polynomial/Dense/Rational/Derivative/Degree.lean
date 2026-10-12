module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Addition
import Purelib.Data.List.DropWhile.Basic
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Derivative
public import Purelib.Polynomial.Dense.Leading
import Purelib.Polynomial.Dense.Multiplication
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

public section

/-!
# Characteristic-zero derivative degree over constructive rationals

This is the coordinate-field counterpart of
`ConstructiveDerivativeDegree`.  It follows the finite Horner derivative
scan and proves its leading coefficient directly; no generic
characteristic-zero or infinity theorem is imported.
-/

namespace Purelib.Polynomial.Dense.Rational.Derivative.Degree

open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Data.Nat
open Purelib.Data.List
open Purelib.Algebra
/-- Dense polynomials with canonical rational coefficients. -/
abbrev CoordinatePolynomial :=
  Dense.Basic.DensePolynomial Fraction.Rational

/-- A strictly positive natural number has nonzero rational cast. -/
theorem rational_natCast_ne_zero {n : Nat} (positive : 0 < n) :
    (n : Fraction.Rational) ≠ 0 :=
  ne_of_gt (Fraction.Cast.Order.natCast_pos_direct positive)

/-- Leading-term invariants of the paired finite derivative scan.

After at least two coefficients, the value accumulator has degree one less than the processed count and the derivative
accumulator has the expected scaled leading coefficient. -/
private structure ScanState (leading : Fraction.Rational) (processed : Nat)
    (state : Dense.Rational.Derivative.Degree.CoordinatePolynomial ×
      Dense.Rational.Derivative.Degree.CoordinatePolynomial) : Prop where
  /-- At least two coefficients have been processed. -/ processedAtLeastTwo : 2 ≤ processed
  /-- The value accumulator has the retained leading coefficient and degree `processed - 1`. -/ value :
    Dense.Leading.LeadingTerm state.1 (processed - 1) leading
  /-- The derivative accumulator has degree `processed - 2` and the scaled original leading coefficient. -/ derivative :
    Dense.Leading.LeadingTerm state.2 (processed - 2)
    ((processed - 1 : Nat) * leading)

/-- Transport a derivative scan invariant along equal processed counts and accumulator pairs. -/
private theorem ScanState.of_equal {leading : Fraction.Rational}
    {processed otherProcessed : Nat}
    {state otherState : Dense.Rational.Derivative.Degree.CoordinatePolynomial ×
      Dense.Rational.Derivative.Degree.CoordinatePolynomial}
    (processedEqual : processed = otherProcessed)
    (stateEqual : state = otherState)
    (current : Dense.Rational.Derivative.Degree.ScanState leading otherProcessed otherState) :
    Dense.Rational.Derivative.Degree.ScanState leading processed state := by
  cases processedEqual
  cases stateEqual
  exact current

/-- One derivative Horner step preserves the leading-term scan invariant.

The rational cast of the new positive degree keeps the derivative leading coefficient nonzero. -/
private theorem coefficient_step
    {leading coefficient : Fraction.Rational} {processed : Nat}
    {state : Dense.Rational.Derivative.Degree.CoordinatePolynomial ×
      Dense.Rational.Derivative.Degree.CoordinatePolynomial}
    (current : Dense.Rational.Derivative.Degree.ScanState leading processed state) :
    Dense.Rational.Derivative.Degree.ScanState leading (processed + 1) (Dense.Derivative.derivativeStep state
      coefficient) := by
  have processedAtLeastTwo := current.processedAtLeastTwo
  have oneLeProcessed : 1 ≤ processed :=
    (show 1 ≤ 2 by decide).trans processedAtLeastTwo
  have oneLeProcessedMinusOne : 1 ≤ processed - 1 := by
    cases processed with
    | zero => exact (Nat.not_succ_le_zero 1 processedAtLeastTwo).elim
    | succ remaining =>
        change 1 ≤ remaining
        exact Nat.le_of_succ_le_succ processedAtLeastTwo
  have processedMinusOne : processed - 1 + 1 = processed :=
    (Nat.add_comm _ _).trans (Subtraction.add_sub_of_le oneLeProcessed)
  have processedMinusTwo : processed - 2 + 1 = processed - 1 := by
    have subtractAgain : processed - 2 = processed - 1 - 1 := by
      rw [Subtraction.sub_sub]
    rw [subtractAgain, Nat.add_comm (processed - 1 - 1) 1]
    exact Subtraction.add_sub_of_le oneLeProcessedMinusOne
  have shiftedValue : Dense.Leading.LeadingTerm (Dense.Basic.DensePolynomial.shift 1 state.1) processed leading :=
    Dense.Leading.LeadingTerm.of_equal rfl processedMinusOne.symm rfl
      (current.value.shift 1)
  have nextValue : Dense.Leading.LeadingTerm
      (Dense.Basic.DensePolynomial.shift 1 state.1 + Dense.Basic.DensePolynomial.constant coefficient) processed leading
        := by
    by_cases zero : coefficient = 0
    · subst coefficient
      rw [Dense.Basic.DensePolynomial.add_constant_zero, Dense.Basic.DensePolynomial.normalize_shift]
      exact shiftedValue
    · have constantLeading := Dense.Leading.LeadingTerm.constant zero
      have constantBelow : Dense.Leading.DegreeBelow (Dense.Basic.DensePolynomial.constant coefficient) processed :=
        (constantLeading.atMost.toBelowSucc).mono oneLeProcessed
      exact shiftedValue.addBelow constantBelow
  have shiftedDerivative : Dense.Leading.LeadingTerm (Dense.Basic.DensePolynomial.shift 1 state.2) (processed - 1)
      (((processed - 1 : Nat) : Fraction.Rational) * leading) :=
    Dense.Leading.LeadingTerm.of_equal rfl processedMinusTwo.symm rfl
      (current.derivative.shift 1)
  have castStep :
      ((processed - 1 : Nat) : Fraction.Rational) * leading + leading =
        (processed : Fraction.Rational) * leading := by
    have naturalStep : processed = (processed - 1) + 1 :=
      processedMinusOne.symm
    have castNaturalStep := congrArg (fun n : Nat => (n : Fraction.Rational))
      naturalStep
    rw [NatCast.add, Nat.cast_one] at castNaturalStep
    rw [castNaturalStep]
    ring1
  have coefficientNonzero :
      ((processed - 1 : Nat) : Fraction.Rational) * leading + leading ≠ 0 := by
    rw [castStep]
    exact Fraction.Field.mul_ne_zero_direct
      (Dense.Rational.Derivative.Degree.rational_natCast_ne_zero
        ((show 0 < 2 by decide).trans_le processedAtLeastTwo))
      current.value.coefficient_ne_zero
  have nextDerivative : Dense.Leading.LeadingTerm
      (Dense.Basic.DensePolynomial.shift 1 state.2 + state.1) (processed - 1)
        (processed * leading) := by
    have sameDegree := shiftedDerivative.add current.value coefficientNonzero
    exact Dense.Leading.LeadingTerm.of_equal rfl rfl castStep.symm sameDegree
  exact
    { processedAtLeastTwo :=
        processedAtLeastTwo.trans (Nat.le_succ processed)
      value := by
        dsimp only [Dense.Derivative.derivativeStep]
        exact Dense.Leading.LeadingTerm.of_equal rfl (Subtraction.add_sub_cancel_right processed 1) rfl
          nextValue
      derivative := by
        dsimp only [Dense.Derivative.derivativeStep]
        have nextDegree : processed + 1 - 2 = processed - 1 := by
          change (processed + 1) - (1 + 1) = processed - 1
          rw [← Subtraction.sub_sub, Subtraction.add_sub_cancel_right]
        exact Dense.Leading.LeadingTerm.of_equal rfl nextDegree rfl nextDerivative }

/-- A finite coefficient fold preserves the derivative scan invariant.

The processed count increases by the number of coefficients in the displayed list. -/
private theorem fold_scan
    (leading : Fraction.Rational) :
    ∀ (coefficients : List Fraction.Rational) (processed : Nat)
      (state : Dense.Rational.Derivative.Degree.CoordinatePolynomial ×
        Dense.Rational.Derivative.Degree.CoordinatePolynomial),
      Dense.Rational.Derivative.Degree.ScanState leading processed state →
      Dense.Rational.Derivative.Degree.ScanState leading (processed + coefficients.length)
        (coefficients.foldl Dense.Derivative.derivativeStep state)
  | [], _, _, current => current
  | coefficient :: coefficients, processed, state, current => by
      have next := Dense.Rational.Derivative.Degree.coefficient_step current (coefficient := coefficient)
      have result := Purelib.Polynomial.Dense.Rational.Derivative.Degree.fold_scan leading coefficients (processed + 1)
        (Dense.Derivative.derivativeStep state coefficient) next
      exact Dense.Rational.Derivative.Degree.ScanState.of_equal
        (by
          simp only [List.length_cons]
          calc
            processed + (coefficients.length + 1) =
                processed + (1 + coefficients.length) :=
              congrArg (fun value => processed + value)
                (Nat.add_comm coefficients.length 1)
            _ = processed + 1 + coefficients.length :=
              (Nat.add_assoc processed 1 coefficients.length).symm)
        rfl result

/-- The finite automatic derivative of a positive-degree constructive-
rational polynomial is represented nonzero. -/
theorem derivative_isZero_false
    {p : Dense.Rational.Derivative.Degree.CoordinatePolynomial} (nonzero : p.isZero = false)
    (positive : 0 < p.natDegree) :
    (Dense.Derivative.derivative p).isZero = false := by
  rw [← Dense.Derivative.derivative_normalize p]
  cases coefficients : p.normalize.coeffs with
  | nil =>
      change p.normalize.coeffs.isEmpty = false at nonzero
      rw [coefficients] at nonzero
      exact Bool.noConfusion nonzero
  | cons leading tail =>
      cases tail with
      | nil =>
          have count := Dense.Basic.DensePolynomial.natDegree_add_one_eq_degreeCount nonzero
          have degreeCountOne : p.degreeCount = 1 := by
            rw [Dense.Basic.DensePolynomial.degreeCount, coefficients]
            rfl
          rw [degreeCountOne] at count
          have degreeZero : p.natDegree = 0 :=
            Addition.add_right_cancel count
          rw [degreeZero] at positive
          exact (Nat.not_lt_zero 0 positive).elim
      | cons second remaining =>
          have leadingNonzero : leading ≠ 0 := by
            have canonical := Dense.Basic.DensePolynomial.leadingCoeff_ne_zero nonzero
            change p.normalize.coeffs.headD 0 ≠ 0 at canonical
            rw [coefficients] at canonical
            exact canonical
          let initial := Dense.Derivative.derivativeStep (Dense.Derivative.derivativeStep (0, 0) leading) second
          have firstState : Dense.Derivative.derivativeStep (0, 0) leading =
              (Dense.Basic.DensePolynomial.constant leading, (0 :
                Dense.Rational.Derivative.Degree.CoordinatePolynomial)) := by
            apply Prod.ext
            · dsimp only [Dense.Derivative.derivativeStep]
              rw [Dense.Basic.DensePolynomial.shift_zero, Dense.Basic.DensePolynomial.zero_add_normalize,
                Dense.Basic.DensePolynomial.normalize_constant_of_ne leadingNonzero]
            · dsimp only [Dense.Derivative.derivativeStep]
              rw [Dense.Basic.DensePolynomial.shift_zero, Dense.Basic.DensePolynomial.add_zero_normalize,
                Dense.Basic.DensePolynomial.normalize_zero]
          have initialValue : initial.1 =
              (⟨[leading, second]⟩ : Dense.Rational.Derivative.Degree.CoordinatePolynomial) := by
            dsimp only [initial]
            rw [firstState]
            dsimp only [Dense.Derivative.derivativeStep]
            rw [Dense.Basic.DensePolynomial.shift_one_constant_of_ne leadingNonzero,
              Dense.Basic.DensePolynomial.linear_add_constant 0 second leadingNonzero]
            apply Dense.Basic.DensePolynomial.ext
            simp only [Fraction.Field.zero_add, -eq_self, -iff_self]
            rfl
          have initialDerivative : initial.2 = Dense.Basic.DensePolynomial.constant leading := by
            dsimp only [initial]
            rw [firstState]
            dsimp only [Dense.Derivative.derivativeStep]
            rw [Dense.Basic.DensePolynomial.shift_zero, Dense.Basic.DensePolynomial.zero_add_normalize,
              Dense.Basic.DensePolynomial.normalize_constant_of_ne leadingNonzero]
          have retainedHead : decide (leading = 0) = false := decide_eq_false leadingNonzero
          have valueLeading : Dense.Leading.LeadingTerm initial.1 1 leading := by
            apply Dense.Leading.LeadingTerm.of_equal initialValue rfl rfl
            exact
              { normalized := Dense.Basic.DensePolynomial.normalize_linear_of_leading_ne_zero leadingNonzero
                nonzero := by
                  change ([leading, second].dropWhile (· = 0)).isEmpty = false
                  rw [DropWhile.cons_of_false (fun coefficient => decide (coefficient = 0)) leading [second]
                    retainedHead]
                  rfl
                degree_eq := by
                  change ([leading, second].dropWhile (· = 0)).length - 1 = 1
                  rw [DropWhile.cons_of_false (fun coefficient => decide (coefficient = 0)) leading [second]
                    retainedHead]
                  rfl
                coefficient_eq := by
                  change ([leading, second].dropWhile (· = 0)).headD 0 = leading
                  rw [DropWhile.cons_of_false (fun coefficient => decide (coefficient = 0)) leading [second]
                    retainedHead]
                  rfl }
          have derivativeLeading : Dense.Leading.LeadingTerm initial.2 0 leading := by
            exact Dense.Leading.LeadingTerm.of_equal initialDerivative rfl rfl
              (Dense.Leading.LeadingTerm.constant leadingNonzero)
          have initialState : Dense.Rational.Derivative.Degree.ScanState leading 2 initial :=
            { processedAtLeastTwo := by decide
              value := valueLeading
              derivative := Dense.Leading.LeadingTerm.of_equal rfl rfl
                (by
                  change ((1 : Nat) : Fraction.Rational) * leading = leading
                  rw [Nat.cast_one, one_mul]) derivativeLeading }
          have final := Dense.Rational.Derivative.Degree.fold_scan leading remaining 2 initial initialState
          have finalNonzero := final.derivative.nonzero
          change ((Dense.Derivative.derivativeState p.normalize.coeffs).2).isZero = false
          rw [coefficients]
          simpa only [Dense.Derivative.derivativeState, List.foldl_cons] using finalNonzero

end Purelib.Polynomial.Dense.Rational.Derivative.Degree

end
