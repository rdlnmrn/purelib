module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Addition
import Purelib.Algebra.NatCast
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Polynomial.Dense.Derivative
public import Purelib.Polynomial.Dense.Leading
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Leading (LeadingTerm)

open Purelib.Data

open Purelib.Polynomial

public section

/-!
# Characteristic-zero derivative degree over constructive Scalar rationals

This module proves that the finite automatic derivative of a positive-degree
Scalar-rational polynomial is nonzero.  The proof follows the displayed
coefficient scan and its leading term; no root count or imported
characteristic-zero polynomial theorem is used.
-/

-- Retain exact public scalar/carrier shorthand names after subject placement.

namespace Purelib.Polynomial.Dense.Gaussian.Derivative.Degree

/-- The canonical Gaussian-rational coefficient carrier. -/
abbrev Scalar := Gaussian.Basic.Canonical
/-- Dense polynomials over canonical Gaussian rationals. -/
abbrev CoefficientPolynomial := Basic.CanonicalCoefficients.CoefficientPolynomial

open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Derivative
open _root_.Purelib.Polynomial.Dense.Derivative renaming CoefficientPolynomial -> Dense
open Purelib.Polynomial.Dense.Leading
open _root_.Purelib.Polynomial.Dense.Leading renaming CoefficientPolynomial -> Dense

/-- A positive natural number has nonzero Gaussian-rational cast. -/
theorem gaussian_natCast_ne_zero {n : Nat} (positive : 0 < n) :
    (n : Scalar) ≠ 0 := open Purelib.Data.Rat in by
  intro zero
  have real := congrArg Gaussian.Basic.re zero
  change ((n : Scalar).re) =
    (0 : Scalar).re at real
  rw [Gaussian.Cast.natCast_re,
    Gaussian.Basic.zero_re] at real
  exact (ne_of_gt
    (Fraction.Cast.Order.natCast_pos_direct positive)) real

/-- Leading-term invariants for the paired Gaussian derivative scan.

After at least two coefficients, the value and derivative accumulators retain their exact degrees and the derivative
leading coefficient is the degree-scaled original coefficient. -/
private structure ScanState (leading : Scalar) (processed : Nat)
    (state : CoefficientPolynomial × CoefficientPolynomial) : Prop where
  /-- At least two coefficients have been processed. -/ processedAtLeastTwo : 2 ≤ processed
  /-- The value accumulator retains degree `processed - 1` and the original leading coefficient. -/ value :
    Dense.Leading.LeadingTerm state.1 (processed - 1) leading
  /-- The derivative accumulator retains degree `processed - 2` and the scaled leading coefficient. -/ derivative :
    Dense.Leading.LeadingTerm state.2 (processed - 2)
    ((processed - 1 : Nat) * leading)

namespace ScanState

/-- Transport the scan invariant across equal counts and accumulator pairs. -/
private theorem of_equal {leading : Scalar}
    {processed otherProcessed : Nat}
    {state otherState : CoefficientPolynomial × CoefficientPolynomial}
    (processedEqual : processed = otherProcessed)
    (stateEqual : state = otherState)
    (current : ScanState leading otherProcessed otherState) :
    ScanState leading processed state := by
  cases processedEqual
  cases stateEqual
  exact current

end ScanState

/-- One Gaussian derivative Horner step preserves the leading-term invariant. -/
private theorem coefficient_step
    {leading coefficient : Scalar} {processed : Nat}
    {state : CoefficientPolynomial × CoefficientPolynomial}
    (current : ScanState leading processed state) :
    ScanState leading (processed + 1) (Dense.Derivative.derivativeStep state
      coefficient) := by
  have processedAtLeastTwo := current.processedAtLeastTwo
  have oneLeProcessed : 1 ≤ processed :=
    (show 1 ≤ 2 by decide).trans processedAtLeastTwo
  have oneLeProcessedMinusOne : 1 ≤ processed - 1 :=
    by omega0
  have processedMinusOne : processed - 1 + 1 = processed :=
    Purelib.Data.Nat.Subtraction.sub_add_cancel oneLeProcessed
  have processedMinusTwo : processed - 2 + 1 = processed - 1 := by
    have subtractAgain : processed - 2 = processed - 1 - 1 := by
      rw [Purelib.Data.Nat.Subtraction.sub_sub]
    rw [subtractAgain, Purelib.Data.Nat.Subtraction.sub_add_cancel oneLeProcessedMinusOne]
  have shiftedValue : Dense.Leading.LeadingTerm (DensePolynomial.shift 1 state.1) processed leading :=
    LeadingTerm.of_equal rfl processedMinusOne.symm rfl
      (current.value.shift 1)
  have nextValue : Dense.Leading.LeadingTerm
      (DensePolynomial.shift 1 state.1 + DensePolynomial.constant coefficient) processed leading
        := by
    by_cases zero : coefficient = 0
    · subst coefficient
      rw [DensePolynomial.add_constant_zero, DensePolynomial.normalize_shift]
      exact shiftedValue
    · have constantLeading := LeadingTerm.constant zero
      have constantBelow : Dense.Leading.DegreeBelow (DensePolynomial.constant coefficient) processed :=
        (constantLeading.atMost.toBelowSucc).mono oneLeProcessed
      exact shiftedValue.addBelow constantBelow
  have shiftedDerivative : Dense.Leading.LeadingTerm (DensePolynomial.shift 1 state.2) (processed - 1)
      (((processed - 1 : Nat) : Scalar) * leading) :=
    LeadingTerm.of_equal rfl processedMinusTwo.symm rfl
      (current.derivative.shift 1)
  have castStep :
      ((processed - 1 : Nat) : Scalar) * leading + leading =
        (processed : Scalar) * leading := by
    have naturalStep : processed = (processed - 1) + 1 :=
      processedMinusOne.symm
    have castNaturalStep := congrArg (fun n : Nat => (n : Scalar))
      naturalStep
    rw [Purelib.Algebra.NatCast.add, Nat.cast_one] at castNaturalStep
    rw [castNaturalStep]
    ring1
  have coefficientNonzero :
      ((processed - 1 : Nat) : Scalar) * leading + leading ≠ 0 := by
    rw [castStep]
    exact Gaussian.Field.mul_ne_zero_direct
      (gaussian_natCast_ne_zero
        ((show 0 < 2 by decide).trans_le processedAtLeastTwo))
      current.value.coefficient_ne_zero
  have nextDerivative : Dense.Leading.LeadingTerm
      (DensePolynomial.shift 1 state.2 + state.1) (processed - 1)
        (processed * leading) := by
    have sameDegree := shiftedDerivative.add current.value coefficientNonzero
    exact LeadingTerm.of_equal rfl rfl castStep.symm sameDegree
  exact
    { processedAtLeastTwo :=
        processedAtLeastTwo.trans (Nat.le_succ processed)
      value := by
        dsimp only [Dense.Derivative.derivativeStep]
        exact LeadingTerm.of_equal rfl (Purelib.Data.Nat.Subtraction.add_sub_cancel_right processed 1) rfl
          nextValue
      derivative := by
        dsimp only [Dense.Derivative.derivativeStep]
        have nextDegree : processed + 1 - 2 = processed - 1 := by
          change (processed + 1) - (1 + 1) = processed - 1
          omega0
        exact LeadingTerm.of_equal rfl nextDegree rfl nextDerivative }

/-- A finite coefficient fold preserves the derivative scan invariant and advances the processed count. -/
private theorem fold_scan
    (leading : Scalar) :
    ∀ (coefficients : List Scalar) (processed : Nat)
      (state : CoefficientPolynomial × CoefficientPolynomial),
      ScanState leading processed state →
      ScanState leading (processed + coefficients.length)
        (coefficients.foldl Dense.Derivative.derivativeStep state)
  | [], _, _, current => current
  | coefficient :: coefficients, processed, state, current => by
      have next := coefficient_step current (coefficient := coefficient)
      have result := fold_scan leading coefficients (processed + 1)
        (Dense.Derivative.derivativeStep state coefficient) next
      exact Dense.Gaussian.Derivative.Degree.ScanState.of_equal
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

/-- The automatic derivative of a positive-degree Scalar-rational
polynomial is represented nonzero. -/
theorem derivative_isZero_false
    {p : CoefficientPolynomial} (nonzero : p.isZero = false)
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
          have count := DensePolynomial.natDegree_add_one_eq_degreeCount nonzero
          have degreeCountOne : p.degreeCount = 1 := by
            rw [DensePolynomial.degreeCount, coefficients]
            rfl
          rw [degreeCountOne] at count
          have degreeZero : p.natDegree = 0 :=
            Purelib.Data.Nat.Addition.add_right_cancel count
          rw [degreeZero] at positive
          exact (Nat.not_lt_zero 0 positive).elim
      | cons second remaining =>
          have leadingNonzero : leading ≠ 0 := by
            have canonical := DensePolynomial.leadingCoeff_ne_zero nonzero
            change p.normalize.coeffs.headD 0 ≠ 0 at canonical
            rw [coefficients] at canonical
            simpa only [List.headD_cons] using canonical
          let initial := Dense.Derivative.derivativeStep (Dense.Derivative.derivativeStep (0, 0) leading) second
          have firstState : Dense.Derivative.derivativeStep (0, 0) leading =
              (DensePolynomial.constant leading, (0 : CoefficientPolynomial)) := by
            apply Prod.ext
            · dsimp only [Dense.Derivative.derivativeStep]
              rw [DensePolynomial.shift_zero, DensePolynomial.zero_add_normalize,
                DensePolynomial.normalize_constant_of_ne leadingNonzero]
            · dsimp only [Dense.Derivative.derivativeStep]
              rw [DensePolynomial.shift_zero, DensePolynomial.add_zero_normalize,
                DensePolynomial.normalize_zero]
          have initialValue : initial.1 =
              (⟨[leading, second]⟩ : CoefficientPolynomial) := by
            dsimp only [initial]
            rw [firstState]
            dsimp only [Dense.Derivative.derivativeStep]
            rw [
              DensePolynomial.shift_one_constant_of_ne leadingNonzero,
              DensePolynomial.linear_add_constant 0 second leadingNonzero]
            apply DensePolynomial.ext
            simp only [Gaussian.Basic.zero_add, -eq_self]
            rfl
          have initialDerivative : initial.2 = DensePolynomial.constant leading := by
            dsimp only [initial]
            rw [firstState]
            dsimp only [Dense.Derivative.derivativeStep]
            rw [DensePolynomial.shift_zero, DensePolynomial.zero_add_normalize,
              DensePolynomial.normalize_constant_of_ne leadingNonzero]
          have valueLeading : Dense.Leading.LeadingTerm initial.1 1 leading := by
            apply LeadingTerm.of_equal initialValue rfl rfl
            exact
              { normalized := DensePolynomial.normalize_linear_of_leading_ne_zero leadingNonzero
                nonzero := by
                  change (⟨[leading, second]⟩ : CoefficientPolynomial).normalize.coeffs.isEmpty = false
                  rw [DensePolynomial.normalize_linear_of_leading_ne_zero leadingNonzero]
                  rfl
                degree_eq := by
                  change (⟨[leading, second]⟩ : CoefficientPolynomial).normalize.coeffs.length - 1 = 1
                  rw [DensePolynomial.normalize_linear_of_leading_ne_zero leadingNonzero]
                  rfl
                coefficient_eq := by
                  change (⟨[leading, second]⟩ : CoefficientPolynomial).normalize.coeffs.headD 0 =
                    leading
                  rw [DensePolynomial.normalize_linear_of_leading_ne_zero leadingNonzero]
                  rfl }
          have derivativeLeading : Dense.Leading.LeadingTerm initial.2 0 leading := by
            exact LeadingTerm.of_equal initialDerivative rfl rfl
              (LeadingTerm.constant leadingNonzero)
          have initialState : ScanState leading 2 initial :=
            { processedAtLeastTwo := by decide
              value := valueLeading
              derivative := LeadingTerm.of_equal rfl rfl
                (by
                  change ((1 : Nat) : Scalar) * leading = leading
                  rw [Nat.cast_one, one_mul]) derivativeLeading }
          have final := fold_scan leading remaining 2 initial initialState
          have finalNonzero := final.derivative.nonzero
          change ((Dense.Derivative.derivativeState p.normalize.coeffs).2).isZero = false
          rw [coefficients]
          simpa only [Dense.Derivative.derivativeState, List.foldl_cons] using finalNonzero

end Purelib.Polynomial.Dense.Gaussian.Derivative.Degree

end
