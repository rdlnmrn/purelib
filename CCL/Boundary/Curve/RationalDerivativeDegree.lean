import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ComputableDerivative
import mathlib.RFAP.ConstructivePolynomialLeading

/-!
# Characteristic-zero derivative degree over constructive rationals

This is the coordinate-field counterpart of
`ConstructiveDerivativeDegree`.  It follows the finite Horner derivative
scan and proves its leading coefficient directly; no generic
characteristic-zero or infinity theorem is imported.
-/

namespace CCL.RationalDerivativeDegree

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev CoordinatePolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Coordinate

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.ComputableDerivative
open RFAP.ConstructivePolynomialLeading

theorem rational_natCast_ne_zero {n : Nat} (positive : 0 < n) :
    (n : Coordinate) ≠ 0 :=
  ne_of_gt (RFAP.ConstructiveFraction.natCast_pos_direct positive)

private structure ScanState (leading : Coordinate) (processed : Nat)
    (state : CoordinatePolynomial × CoordinatePolynomial) : Prop where
  processedAtLeastTwo : 2 ≤ processed
  value : LeadingTerm state.1 (processed - 1) leading
  derivative : LeadingTerm state.2 (processed - 2)
    ((processed - 1 : Nat) * leading)

private theorem ScanState.of_equal {leading : Coordinate}
    {processed otherProcessed : Nat}
    {state otherState : CoordinatePolynomial × CoordinatePolynomial}
    (processedEqual : processed = otherProcessed)
    (stateEqual : state = otherState)
    (current : ScanState leading otherProcessed otherState) :
    ScanState leading processed state := by
  cases processedEqual
  cases stateEqual
  exact current

private theorem coefficient_step
    {leading coefficient : Coordinate} {processed : Nat}
    {state : CoordinatePolynomial × CoordinatePolynomial}
    (current : ScanState leading processed state) :
    ScanState leading (processed + 1) (derivativeStep state coefficient) := by
  have processedAtLeastTwo := current.processedAtLeastTwo
  have oneLeProcessed : 1 ≤ processed :=
    (show 1 ≤ 2 by decide).trans processedAtLeastTwo
  have oneLeProcessedMinusOne : 1 ≤ processed - 1 :=
    Nat.le_sub_of_add_le processedAtLeastTwo
  have processedMinusOne : processed - 1 + 1 = processed :=
    Nat.sub_add_cancel oneLeProcessed
  have processedMinusTwo : processed - 2 + 1 = processed - 1 := by
    have subtractAgain : processed - 2 = processed - 1 - 1 := by
      rw [Nat.sub_sub]
    rw [subtractAgain, Nat.sub_add_cancel oneLeProcessedMinusOne]
  have shiftedValue : LeadingTerm (shift 1 state.1) processed leading :=
    LeadingTerm.of_equal rfl processedMinusOne.symm rfl
      (current.value.shift 1)
  have nextValue : LeadingTerm
      (shift 1 state.1 + constant coefficient) processed leading := by
    by_cases zero : coefficient = 0
    · subst coefficient
      rw [add_constant_zero, normalize_shift]
      exact shiftedValue
    · have constantLeading := LeadingTerm.constant zero
      have constantBelow : DegreeBelow (constant coefficient) processed :=
        (constantLeading.atMost.toBelowSucc).mono oneLeProcessed
      exact shiftedValue.addBelow constantBelow
  have shiftedDerivative : LeadingTerm (shift 1 state.2) (processed - 1)
      (((processed - 1 : Nat) : Coordinate) * leading) :=
    LeadingTerm.of_equal rfl processedMinusTwo.symm rfl
      (current.derivative.shift 1)
  have castStep :
      ((processed - 1 : Nat) : Coordinate) * leading + leading =
        (processed : Coordinate) * leading := by
    have naturalStep : processed = (processed - 1) + 1 :=
      processedMinusOne.symm
    have castNaturalStep := congrArg (fun n : Nat => (n : Coordinate))
      naturalStep
    rw [Nat.cast_add, Nat.cast_one] at castNaturalStep
    rw [castNaturalStep]
    ring1
  have coefficientNonzero :
      ((processed - 1 : Nat) : Coordinate) * leading + leading ≠ 0 := by
    rw [castStep]
    exact RFAP.ConstructiveFraction.mul_ne_zero_direct
      (rational_natCast_ne_zero
        ((show 0 < 2 by decide).trans_le processedAtLeastTwo))
      current.value.coefficient_ne_zero
  have nextDerivative : LeadingTerm
      (shift 1 state.2 + state.1) (processed - 1)
        (processed * leading) := by
    have sameDegree := shiftedDerivative.add current.value coefficientNonzero
    exact LeadingTerm.of_equal rfl rfl castStep.symm sameDegree
  exact
    { processedAtLeastTwo :=
        processedAtLeastTwo.trans (Nat.le_succ processed)
      value := by
        dsimp only [derivativeStep]
        exact LeadingTerm.of_equal rfl (Nat.add_sub_cancel processed 1) rfl
          nextValue
      derivative := by
        dsimp only [derivativeStep]
        have nextDegree : processed + 1 - 2 = processed - 1 := by
          change (processed + 1) - (1 + 1) = processed - 1
          exact Nat.add_sub_add_right processed 1 1
        exact LeadingTerm.of_equal rfl nextDegree rfl nextDerivative }

private theorem fold_scan
    (leading : Coordinate) :
    ∀ (coefficients : List Coordinate) (processed : Nat)
      (state : CoordinatePolynomial × CoordinatePolynomial),
      ScanState leading processed state →
      ScanState leading (processed + coefficients.length)
        (coefficients.foldl derivativeStep state)
  | [], _, _, current => current
  | coefficient :: coefficients, processed, state, current => by
      have next := coefficient_step current (coefficient := coefficient)
      have result := fold_scan leading coefficients (processed + 1)
        (derivativeStep state coefficient) next
      exact ScanState.of_equal
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
    {p : CoordinatePolynomial} (nonzero : p.isZero = false)
    (positive : 0 < p.natDegree) :
    (derivative p).isZero = false := by
  rw [← derivative_normalize p]
  cases coefficients : p.normalize.coeffs with
  | nil =>
      change p.normalize.coeffs.isEmpty = false at nonzero
      rw [coefficients] at nonzero
      exact Bool.noConfusion nonzero
  | cons leading tail =>
      cases tail with
      | nil =>
          have count := natDegree_add_one_eq_degreeCount nonzero
          have degreeCountOne : p.degreeCount = 1 := by
            rw [degreeCount, coefficients]
            rfl
          rw [degreeCountOne] at count
          have degreeZero : p.natDegree = 0 :=
            Nat.add_right_cancel count
          rw [degreeZero] at positive
          exact (Nat.not_lt_zero 0 positive).elim
      | cons second remaining =>
          have leadingNonzero : leading ≠ 0 := by
            have canonical := leadingCoeff_ne_zero nonzero
            change p.normalize.coeffs.headD 0 ≠ 0 at canonical
            rw [coefficients] at canonical
            simpa only [List.headD_cons] using canonical
          let initial := derivativeStep (derivativeStep (0, 0) leading) second
          have firstState : derivativeStep (0, 0) leading =
              (constant leading, (0 : CoordinatePolynomial)) := by
            apply Prod.ext
            · dsimp only [derivativeStep]
              rw [shift_zero, zero_add_normalize,
                normalize_constant_of_ne leadingNonzero]
            · dsimp only [derivativeStep]
              rw [shift_zero, add_zero_normalize, normalize_zero]
          have initialValue : initial.1 =
              (⟨[leading, second]⟩ : CoordinatePolynomial) := by
            dsimp only [initial]
            rw [firstState]
            dsimp only [derivativeStep]
            rw [shift_one_constant_of_ne leadingNonzero,
              linear_add_constant 0 second leadingNonzero]
            apply ext
            simp only [RFAP.ConstructiveFraction.zero_add]
          have initialDerivative : initial.2 = constant leading := by
            dsimp only [initial]
            rw [firstState]
            dsimp only [derivativeStep]
            rw [shift_zero, zero_add_normalize,
              normalize_constant_of_ne leadingNonzero]
          have valueLeading : LeadingTerm initial.1 1 leading := by
            apply LeadingTerm.of_equal initialValue rfl rfl
            exact
              { normalized := normalize_linear_of_leading_ne_zero leadingNonzero
                nonzero := by
                  change ([leading, second].dropWhile (· = 0)).isEmpty = false
                  rw [List.dropWhile_cons_of_neg (by simp [leadingNonzero])]
                  rfl
                degree_eq := by
                  change ([leading, second].dropWhile (· = 0)).length - 1 = 1
                  rw [List.dropWhile_cons_of_neg (by simp [leadingNonzero])]
                  rfl
                coefficient_eq := by
                  change ([leading, second].dropWhile (· = 0)).headD 0 = leading
                  rw [List.dropWhile_cons_of_neg (by simp [leadingNonzero])]
                  rfl }
          have derivativeLeading : LeadingTerm initial.2 0 leading := by
            exact LeadingTerm.of_equal initialDerivative rfl rfl
              (LeadingTerm.constant leadingNonzero)
          have initialState : ScanState leading 2 initial :=
            { processedAtLeastTwo := by decide
              value := valueLeading
              derivative := LeadingTerm.of_equal rfl rfl
                (by
                  change ((1 : Nat) : Coordinate) * leading = leading
                  rw [Nat.cast_one, one_mul]) derivativeLeading }
          have final := fold_scan leading remaining 2 initial initialState
          have finalNonzero := final.derivative.nonzero
          change ((derivativeState p.normalize.coeffs).2).isZero = false
          rw [coefficients]
          simpa only [derivativeState, List.foldl_cons] using finalNonzero

end CCL.RationalDerivativeDegree
