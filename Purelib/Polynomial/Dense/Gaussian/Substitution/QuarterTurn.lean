module
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coefficients.Constants
import Purelib.Polynomial.Dense.Leading

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Nat.Addition
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

/-!
# Quarter-turn substitution of Gaussian polynomials

The normalized Gaussian coefficient table is folded after multiplication
by the imaginary unit. Its readback, leading coefficient and natural degree
are certified without changing that finite fold.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn

open Purelib.Data
open Purelib.Data.Nat
open Purelib.Polynomial

/-- One coefficient step of Horner substitution by the imaginary-unit multiple of the coordinate.

The state is scaled by the imaginary unit and shifted once, then the
retained coefficient is added as a constant polynomial. -/
@[expose] def quarterTurnStep (state : Basic.CanonicalCoefficients.CoefficientPolynomial) (coefficient :
  Gaussian.Basic.Canonical) :
    (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Dense.Basic.DensePolynomial.shift 1 (Dense.Basic.DensePolynomial.scale Gaussian.Constants.imaginaryUnit state) +
    Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant coefficient

/-- Substitute the imaginary-unit multiple of the coordinate using a finite fold over normalized coefficients.

The empty coefficient table remains zero; a nonempty table starts from its leading constant and applies the retained
quarter-turn step. -/
@[expose] def quarterTurn (p : Basic.CanonicalCoefficients.CoefficientPolynomial) : (Dense.Basic.DensePolynomial
  Gaussian.Basic.Canonical) :=
  match p.normalize.coeffs with
  | [] => 0
  | leading :: remaining =>
      remaining.foldl Dense.Gaussian.Substitution.QuarterTurn.quarterTurnStep
        (Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant leading)

section
/-- The quarter-turn coefficient fold evaluates as the scalar Horner fold at the rotated argument.

The supplied state equality initializes the polynomial and scalar folds
at the same value. Both consume the retained coefficient list in order. -/
private theorem eval_foldl_quarterTurnStep (z : Gaussian.Basic.Canonical) :
    ∀ (coefficients : List Gaussian.Basic.Canonical) (state : Basic.CanonicalCoefficients.CoefficientPolynomial)
      (value : Gaussian.Basic.Canonical),
      state.eval z = value →
      (coefficients.foldl Dense.Gaussian.Substitution.QuarterTurn.quarterTurnStep state).eval z =
        coefficients.foldl
          (fun accumulator coefficient =>
            accumulator * (z * Gaussian.Constants.imaginaryUnit) + coefficient) value
  | [], _, _, stateEvaluation => stateEvaluation
  | coefficient :: remaining, state, value, stateEvaluation => by
      simp only [List.foldl_cons]
      apply Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn.eval_foldl_quarterTurnStep z
        remaining
      rw [Dense.Gaussian.Substitution.QuarterTurn.quarterTurnStep, Dense.Basic.DensePolynomial.eval_add,
        Dense.Basic.DensePolynomial.eval_shift, Dense.Basic.DensePolynomial.eval_scale,
        Dense.Gaussian.Coefficients.Constants.eval_parameterConstant, stateEvaluation]
      change Gaussian.Constants.imaginaryUnit * value * z ^ 1 + coefficient =
        value * (z * Gaussian.Constants.imaginaryUnit) + coefficient
      ring1
end

/-- The quarter-turn polynomial evaluates as the original polynomial at the argument multiplied by the imaginary unit.

The normalized finite table is evaluated after the same imaginary-unit
substitution, so its scalar readback uses the rotated argument. -/
@[simp] theorem eval_quarterTurn (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (z :
  Gaussian.Basic.Canonical) :
    (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p).eval z = p.eval (z * Gaussian.Constants.imaginaryUnit) := by
  rw [← Dense.Basic.DensePolynomial.eval_normalize p (z * Gaussian.Constants.imaginaryUnit)]
  change (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p).eval z =
    p.normalize.coeffs.foldl
      (fun value coefficient =>
        value * (z * Gaussian.Constants.imaginaryUnit) + coefficient) 0
  cases coefficients : p.normalize.coeffs with
  | nil =>
      rw [Dense.Gaussian.Substitution.QuarterTurn.quarterTurn, coefficients, Dense.Basic.DensePolynomial.eval_zero]
      change 0 = [].foldl
        (fun value coefficient =>
          value * (z * Gaussian.Constants.imaginaryUnit) + coefficient) 0
      rfl
  | cons leading remaining =>
      rw [Dense.Gaussian.Substitution.QuarterTurn.quarterTurn, coefficients]
      have initial : (Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant leading).eval z =
        leading :=
        Dense.Gaussian.Coefficients.Constants.eval_parameterConstant leading z
      rw [Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn.eval_foldl_quarterTurnStep z remaining
        (Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant leading) leading initial]
      simp only [List.foldl_cons]
      change remaining.foldl
          (fun value coefficient =>
            value * (z * Gaussian.Constants.imaginaryUnit) + coefficient) leading =
        remaining.foldl
          (fun value coefficient =>
            value * (z * Gaussian.Constants.imaginaryUnit) + coefficient)
          (0 * (z * Gaussian.Constants.imaginaryUnit) + leading)
      rw [zero_mul, zero_add]

/-- Multiply a retained leading coefficient by the imaginary unit at each coefficient step. -/
@[expose] def quarterTurnLeadingStep (leading : Gaussian.Basic.Canonical) (_ : Gaussian.Basic.Canonical) :
  Gaussian.Basic.Canonical :=
  Gaussian.Constants.imaginaryUnit * leading

section
/-- Each quarter-turn fold step raises degree by one and multiplies the leading coefficient by the imaginary unit.

A retained nonzero leading term is scaled and shifted at each step. The
constant coefficient stays below the next degree and does not alter its
computed leading coefficient. -/
private theorem foldl_quarterTurnLeading :
    ∀ (coefficients : List Gaussian.Basic.Canonical) (state : Basic.CanonicalCoefficients.CoefficientPolynomial)
      (degree : Nat) (leading : Gaussian.Basic.Canonical),
      Dense.Leading.LeadingTerm state degree leading →
      Dense.Leading.LeadingTerm
        (coefficients.foldl Dense.Gaussian.Substitution.QuarterTurn.quarterTurnStep state)
        (degree + coefficients.length)
        (coefficients.foldl Dense.Gaussian.Substitution.QuarterTurn.quarterTurnLeadingStep leading)
  | [], _, _, _, shape => shape
  | coefficient :: remaining, state, degree, leading, shape => by
      simp only [List.foldl_cons, List.length_cons]
      have imaginaryNonzero : Gaussian.Constants.imaginaryUnit ≠ 0 := by decide
      have scaled := Dense.Leading.LeadingTerm.scale
        imaginaryNonzero shape
      have shifted := Dense.Leading.LeadingTerm.shift 1 scaled
      have coefficientBelow :
        Dense.Leading.DegreeBelow
            (Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant coefficient) (degree + 1) :=
        Dense.Leading.DegreeBelow.mono
          (Dense.Gaussian.Coefficients.Constants.parameterConstant_atMost coefficient).toBelowSucc
          (Nat.succ_le_succ (Nat.zero_le degree))
      have next : Dense.Leading.LeadingTerm
          (Dense.Gaussian.Substitution.QuarterTurn.quarterTurnStep state coefficient) (degree + 1)
          (Gaussian.Constants.imaginaryUnit * leading) := by
        unfold Dense.Gaussian.Substitution.QuarterTurn.quarterTurnStep
        exact Dense.Leading.LeadingTerm.addBelow shifted
          coefficientBelow
      have final := Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn.foldl_quarterTurnLeading
        remaining
        (Dense.Gaussian.Substitution.QuarterTurn.quarterTurnStep state coefficient) (degree + 1)
        (Gaussian.Constants.imaginaryUnit * leading) next
      exact Dense.Leading.LeadingTerm.of_equal
        rfl
        (by
          calc
            degree + (remaining.length + 1) =
                degree + (1 + remaining.length) :=
              congrArg (fun value => degree + value)
                (Nat.add_comm remaining.length 1)
            _ = degree + 1 + remaining.length :=
              (Nat.add_assoc degree 1 remaining.length).symm)
        rfl final
end

/-- Compute the quarter-turn leading coefficient from the normalized coefficient table.

The normalized leading coefficient initializes the fold. Each remaining
coefficient causes one multiplication by the same imaginary unit. -/
@[expose] def quarterTurnLeading (p : Basic.CanonicalCoefficients.CoefficientPolynomial) :
  Gaussian.Basic.Canonical :=
  match p.normalize.coeffs with
  | [] => 0
  | leading :: remaining =>
      remaining.foldl Dense.Gaussian.Substitution.QuarterTurn.quarterTurnLeadingStep leading

/-- A nonzero polynomial's quarter turn retains its degree and the computed rotated leading coefficient.

The nonzero normalized table has a retained leading coefficient. Its
finite tail determines the same degree and the computed rotated leader. -/
theorem quarterTurn_shape (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) :
    Dense.Leading.LeadingTerm (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p)
      p.natDegree (Dense.Gaussian.Substitution.QuarterTurn.quarterTurnLeading p) := by
  cases coefficients : p.normalize.coeffs with
  | nil =>
      have contradiction := nonzero
      change p.normalize.coeffs.isEmpty = false at contradiction
      rw [coefficients] at contradiction
      exact Bool.noConfusion contradiction
  | cons leading remaining =>
      have leadingNonzero : leading ≠ 0 := by
        have := Dense.Basic.DensePolynomial.leadingCoeff_ne_zero nonzero
        change p.normalize.coeffs.headD 0 ≠ 0 at this
        simpa only [coefficients, List.headD_cons] using this
      have initial := Dense.Gaussian.Coefficients.Constants.parameterConstant_leading leadingNonzero
      have folded := Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn.foldl_quarterTurnLeading remaining
        (Dense.Gaussian.Coefficients.Constants.SeparatedVariables.parameterConstant leading) 0 leading initial
      have degreeIdentity : p.natDegree = remaining.length := by
        have count := Dense.Basic.DensePolynomial.natDegree_add_one_eq_degreeCount nonzero
        rw [Dense.Basic.DensePolynomial.degreeCount, coefficients] at count
        simp only [List.length_cons] at count
        exact Addition.add_right_cancel count
      exact Dense.Leading.LeadingTerm.of_equal
        (by rw [Dense.Gaussian.Substitution.QuarterTurn.quarterTurn, coefficients])
        (by rw [degreeIdentity, Nat.zero_add])
        (by rw [Dense.Gaussian.Substitution.QuarterTurn.quarterTurnLeading, coefficients]) folded

/-- Quarter-turn substitution preserves polynomial nonzeroness.

The retained quarter-turn leading-term certificate supplies a nonzero
leader for the same substituted polynomial. -/
theorem quarterTurn_nonzero (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) : (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p).isZero = false :=
  (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn_shape p nonzero).nonzero

/-- Quarter-turn substitution preserves the natural degree of every nonzero polynomial.

The retained leading-term certificate identifies the natural degree of
the substituted polynomial with the supplied nonzero source degree. -/
theorem quarterTurn_natDegree (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) :
    (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p).natDegree = p.natDegree :=
  (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn_shape p nonzero).degree_eq

end Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn

end
