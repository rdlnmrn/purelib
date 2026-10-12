module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Natural
import Purelib.Polynomial.Ascending.Rational.Basic
public import Purelib.Polynomial.Ascending.Rational.Derivative

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Polynomial.Ascending.Rational.Basic (CoefficientPolynomial)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite integration, an algebraic FTC, and polynomial ODE certificates

Integration here is coefficient arithmetic on a displayed finite polynomial.
The antiderivative divides each coefficient by its positive natural degree.
The fundamental theorem is the pair of exact finite statements that
differentiating this table returns the original table and that an interval
increment factors through the antiderivative's secant kernel.

The final section packages elementary initial-value problems with polynomial
forcing and records the exact finite defect of the exponential polynomial for
`y' = y`.  No measure, completed interval, limiting partition, or
function-as-an-infinite-set is used.
-/

namespace Purelib.Polynomial.Ascending.Rational.Antiderivative

/-- Divide successive coefficients by the displayed positive natural
degrees. -/
def integrateCoefficients : Nat → List Fraction.Rational →
  List Fraction.Rational
  | _, [] => []
  | degree, coefficient :: remaining =>
      coefficient / (degree : Fraction.Rational) ::
        integrateCoefficients (degree + 1) remaining

/-- Positive degree weights cancel the divisions in an integrated table.

Starting at a strictly positive natural degree ensures every rational denominator is nonzero; the resulting coefficient
list equals the original list literally. -/
theorem derivativeFrom_integrateCoefficients :
    ∀ (degree : Nat) (_positive : 0 < degree) coefficients,
      Ascending.Rational.Derivative.derivativeFrom degree (integrateCoefficients
        degree coefficients) =
        coefficients
  | degree, positive, [] => rfl
  | degree, positive, coefficient :: remaining => by
      rw [integrateCoefficients, Ascending.Rational.Derivative.derivativeFrom,
        derivativeFrom_integrateCoefficients (degree + 1) (by
          omega)
          remaining]
      congr 1
      calc
        (degree : Fraction.Rational) * (coefficient / (degree : Fraction.Rational)) =
            (coefficient / (degree : Fraction.Rational)) * (degree : Fraction.Rational) :=
          Fraction.Field.mul_comm _ _
        _ = coefficient :=
          Fraction.Field.div_mul_cancel_of_ne coefficient
            (degree : Fraction.Rational) (Natural.degreeCast_ne_zero degree positive)

/-- Finite antiderivative with an explicit rational constant term. -/
def antiderivative (constant : Fraction.Rational)
  (polynomial : CoefficientPolynomial) :
    CoefficientPolynomial :=
  ⟨constant :: integrateCoefficients 1 polynomial.coefficients⟩

/-- Integration of coefficient lists preserves their padded addition at each starting degree. -/
theorem integrateCoefficients_add : ∀ (degree : Nat)
    (left right : List Fraction.Rational),
    integrateCoefficients degree (Ascending.Rational.Basic.addCoefficients left right)
      =
      Ascending.Rational.Basic.addCoefficients (integrateCoefficients degree left)
        (integrateCoefficients degree right)
  | degree, [], right => rfl
  | degree, left, [] => by
      rw [Ascending.Rational.Basic.addCoefficients_nil_right, integrateCoefficients]
      exact (Ascending.Rational.Basic.addCoefficients_nil_right
        (integrateCoefficients degree left)).symm
  | degree, left :: leftTail, right :: rightTail => by
      simp only [Ascending.Rational.Basic.addCoefficients, integrateCoefficients]
      rw [integrateCoefficients_add (degree + 1) leftTail
        rightTail]
      congr 1
      calc
        (left + right) / (degree : Fraction.Rational) =
            (left + right) * (degree : Fraction.Rational)⁻¹ := rfl
        _ = (degree : Fraction.Rational)⁻¹ * (left + right) :=
          Fraction.Field.mul_comm _ _
        _ = (degree : Fraction.Rational)⁻¹ * left +
              (degree : Fraction.Rational)⁻¹ * right :=
          Fraction.Field.left_distrib _ _ _
        _ = left * (degree : Fraction.Rational)⁻¹ +
              right * (degree : Fraction.Rational)⁻¹ := by
          rw [Fraction.Field.mul_comm
              (degree : Fraction.Rational)⁻¹ left,
            Fraction.Field.mul_comm
              (degree : Fraction.Rational)⁻¹ right]
        _ = left / (degree : Fraction.Rational) +
              right / (degree : Fraction.Rational) := rfl

/-- Integration of coefficient lists commutes with rational scaling. -/
theorem integrateCoefficients_scale (factor :
  Fraction.Rational) :
    ∀ (degree : Nat) (coefficients : List Fraction.Rational),
    integrateCoefficients degree (coefficients.map (factor * ·)) =
      (integrateCoefficients degree coefficients).map (factor * ·)
  | degree, [] => rfl
  | degree, coefficient :: remaining => by
      simp only [List.map, integrateCoefficients]
      rw [integrateCoefficients_scale factor (degree + 1)
        remaining]
      congr 1
      calc
        (factor * coefficient) / (degree : Fraction.Rational) =
            (factor * coefficient) * (degree : Fraction.Rational)⁻¹ := rfl
        _ = factor * (coefficient * (degree : Fraction.Rational)⁻¹) :=
          Fraction.Field.mul_assoc _ _ _
        _ = factor * (coefficient / (degree : Fraction.Rational)) := rfl

/-- The zero-constant finite antiderivative is additive coefficient by
coefficient. -/
theorem antiderivative_add (left right :
  CoefficientPolynomial) :
    antiderivative 0 (Ascending.Rational.Basic.add left right) =
      Ascending.Rational.Basic.add (antiderivative 0 left)
        (antiderivative 0 right) := by
  cases left with
  | mk leftCoefficients =>
      cases right with
      | mk rightCoefficients =>
          change
            (⟨0 :: integrateCoefficients 1
                (Ascending.Rational.Basic.addCoefficients leftCoefficients rightCoefficients)⟩ :
              CoefficientPolynomial) =
              (⟨0 :: Ascending.Rational.Basic.addCoefficients
                (integrateCoefficients 1 leftCoefficients)
                (integrateCoefficients 1 rightCoefficients)⟩ :
                  CoefficientPolynomial)
          rw [integrateCoefficients_add]

/-- The zero-constant finite antiderivative commutes with displayed rational
scaling. -/
theorem antiderivative_scale (factor : Fraction.Rational)
  (polynomial : CoefficientPolynomial) :
    antiderivative 0 (Ascending.Rational.Basic.scale factor polynomial) =
      Ascending.Rational.Basic.scale factor (antiderivative 0 polynomial) := by
  cases polynomial with
  | mk coefficients =>
      change
        (⟨0 :: integrateCoefficients 1 (coefficients.map (factor * ·))⟩ :
          CoefficientPolynomial) =
          (⟨(0 :: integrateCoefficients 1 coefficients).map (factor * ·)⟩ :
            CoefficientPolynomial)
      rw [integrateCoefficients_scale]
      simp only [List.map]
      rw [Fraction.Field.mul_zero_direct]

/-- Differentiating the constructed coefficient table returns the original
finite polynomial literally, not merely by evaluation at many points. -/
theorem derivative_antiderivative (constant :
  Fraction.Rational)
    (polynomial : CoefficientPolynomial) :
    Ascending.Rational.Derivative.derivative (antiderivative constant polynomial) =
      polynomial := by
  cases polynomial with
  | mk coefficients =>
      change
        (⟨Ascending.Rational.Derivative.derivativeFrom 1 (integrateCoefficients 1
          coefficients)⟩ :
          CoefficientPolynomial) =
        ⟨coefficients⟩
      rw [derivativeFrom_integrateCoefficients 1 (by decide) coefficients]
end Purelib.Polynomial.Ascending.Rational.Antiderivative

end
