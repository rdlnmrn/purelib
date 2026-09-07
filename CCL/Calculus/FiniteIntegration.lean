import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Calculus.DividedDifference

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

namespace CCL.FiniteIntegration

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Polynomial := CCL.FinitePolynomial.Polynomial

open RFAP.ConstructiveGaussian.Gaussian
open CCL.FinitePolynomial

/-- Divide successive coefficients by the displayed positive natural
degrees. -/
def integrateCoefficients : Nat → List Coordinate → List Coordinate
  | _, [] => []
  | degree, coefficient :: remaining =>
      coefficient / (degree : Coordinate) ::
        integrateCoefficients (degree + 1) remaining

private theorem degreeCast_ne_zero (degree : Nat) (positive : 0 < degree) :
    (degree : Coordinate) ≠ 0 :=
  (RFAP.ConstructiveFraction.natCast_pos_direct positive).ne'

theorem derivativeFrom_integrateCoefficients :
    ∀ (degree : Nat) (_positive : 0 < degree) coefficients,
      derivativeFrom degree (integrateCoefficients degree coefficients) =
        coefficients
  | degree, positive, [] => rfl
  | degree, positive, coefficient :: remaining => by
      rw [integrateCoefficients, derivativeFrom,
        derivativeFrom_integrateCoefficients (degree + 1) (by omega)
          remaining]
      congr 1
      calc
        (degree : Coordinate) * (coefficient / (degree : Coordinate)) =
            (coefficient / (degree : Coordinate)) * (degree : Coordinate) :=
          RFAP.ConstructiveFraction.mul_comm _ _
        _ = coefficient :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne coefficient
            (degree : Coordinate) (degreeCast_ne_zero degree positive)

/-- Finite antiderivative with an explicit rational constant term. -/
def antiderivative (constant : Coordinate) (polynomial : Polynomial) :
    Polynomial :=
  ⟨constant :: integrateCoefficients 1 polynomial.coefficients⟩

theorem integrateCoefficients_add : ∀ (degree : Nat)
    (left right : List Coordinate),
    integrateCoefficients degree (addCoefficients left right) =
      addCoefficients (integrateCoefficients degree left)
        (integrateCoefficients degree right)
  | degree, [], right => rfl
  | degree, left, [] => by
      rw [addCoefficients_nil_right, integrateCoefficients]
      exact (addCoefficients_nil_right
        (integrateCoefficients degree left)).symm
  | degree, left :: leftTail, right :: rightTail => by
      simp only [addCoefficients, integrateCoefficients]
      rw [integrateCoefficients_add (degree + 1) leftTail rightTail]
      congr 1
      calc
        (left + right) / (degree : Coordinate) =
            (left + right) * (degree : Coordinate)⁻¹ := rfl
        _ = (degree : Coordinate)⁻¹ * (left + right) :=
          RFAP.ConstructiveFraction.mul_comm _ _
        _ = (degree : Coordinate)⁻¹ * left +
              (degree : Coordinate)⁻¹ * right :=
          RFAP.ConstructiveFraction.left_distrib _ _ _
        _ = left * (degree : Coordinate)⁻¹ +
              right * (degree : Coordinate)⁻¹ := by
          rw [RFAP.ConstructiveFraction.mul_comm
              (degree : Coordinate)⁻¹ left,
            RFAP.ConstructiveFraction.mul_comm
              (degree : Coordinate)⁻¹ right]
        _ = left / (degree : Coordinate) +
              right / (degree : Coordinate) := rfl

theorem integrateCoefficients_scale (factor : Coordinate) :
    ∀ (degree : Nat) (coefficients : List Coordinate),
    integrateCoefficients degree (coefficients.map (factor * ·)) =
      (integrateCoefficients degree coefficients).map (factor * ·)
  | degree, [] => rfl
  | degree, coefficient :: remaining => by
      simp only [List.map, integrateCoefficients]
      rw [integrateCoefficients_scale factor (degree + 1) remaining]
      congr 1
      calc
        (factor * coefficient) / (degree : Coordinate) =
            (factor * coefficient) * (degree : Coordinate)⁻¹ := rfl
        _ = factor * (coefficient * (degree : Coordinate)⁻¹) :=
          RFAP.ConstructiveFraction.mul_assoc _ _ _
        _ = factor * (coefficient / (degree : Coordinate)) := rfl

/-- The zero-constant finite antiderivative is additive coefficient by
coefficient. -/
theorem antiderivative_add (left right : Polynomial) :
    antiderivative 0 (add left right) =
      add (antiderivative 0 left) (antiderivative 0 right) := by
  cases left with
  | mk leftCoefficients =>
      cases right with
      | mk rightCoefficients =>
          change
            (⟨0 :: integrateCoefficients 1
                (addCoefficients leftCoefficients rightCoefficients)⟩ :
              Polynomial) =
              (⟨0 :: addCoefficients
                (integrateCoefficients 1 leftCoefficients)
                (integrateCoefficients 1 rightCoefficients)⟩ : Polynomial)
          rw [integrateCoefficients_add]

/-- The zero-constant finite antiderivative commutes with displayed rational
scaling. -/
theorem antiderivative_scale (factor : Coordinate) (polynomial : Polynomial) :
    antiderivative 0 (scale factor polynomial) =
      scale factor (antiderivative 0 polynomial) := by
  cases polynomial with
  | mk coefficients =>
      change
        (⟨0 :: integrateCoefficients 1 (coefficients.map (factor * ·))⟩ :
          Polynomial) =
          (⟨(0 :: integrateCoefficients 1 coefficients).map (factor * ·)⟩ :
            Polynomial)
      rw [integrateCoefficients_scale]
      simp only [List.map]
      rw [RFAP.ConstructiveFraction.mul_zero_direct]

/-- Differentiating the constructed coefficient table returns the original
finite polynomial literally, not merely by evaluation at many points. -/
theorem derivative_antiderivative (constant : Coordinate)
    (polynomial : Polynomial) :
    derivative (antiderivative constant polynomial) = polynomial := by
  cases polynomial with
  | mk coefficients =>
      change
        (⟨derivativeFrom 1 (integrateCoefficients 1 coefficients)⟩ :
          Polynomial) =
        ⟨coefficients⟩
      rw [derivativeFrom_integrateCoefficients 1 (by decide) coefficients]

/-- Exact finite interval evaluation of the constructed antiderivative. -/
def definiteIntegral (polynomial : Polynomial) (left right : Gaussian) :
    Gaussian :=
  eval (antiderivative 0 polynomial) right -
    eval (antiderivative 0 polynomial) left

/-- Reversing the displayed interval negates the exact finite integral. -/
theorem definiteIntegral_reverse (polynomial : Polynomial)
    (left right : Gaussian) :
    definiteIntegral polynomial right left =
      -(definiteIntegral polynomial left right) := by
  unfold definiteIntegral
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1

/-- Adjacent displayed intervals concatenate exactly. -/
theorem definiteIntegral_concat (polynomial : Polynomial)
    (left middle right : Gaussian) :
    definiteIntegral polynomial left right =
      definiteIntegral polynomial left middle +
        definiteIntegral polynomial middle right := by
  unfold definiteIntegral
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, add_re, add_im] <;> ring1

/-- Linearity for addition of finite polynomial integrands. -/
theorem definiteIntegral_add (left right : Polynomial)
    (start finish : Gaussian) :
    definiteIntegral (add left right) start finish =
      definiteIntegral left start finish +
        definiteIntegral right start finish := by
  unfold definiteIntegral
  rw [antiderivative_add,
    CCL.FinitePolynomial.eval_add,
    CCL.FinitePolynomial.eval_add]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, add_re, add_im] <;> ring1

/-- Linearity for a displayed rational scalar. -/
theorem definiteIntegral_scale (factor : Coordinate) (polynomial : Polynomial)
    (start finish : Gaussian) :
    definiteIntegral (scale factor polynomial) start finish =
      CCL.FiniteExp.scale factor
        (definiteIntegral polynomial start finish) := by
  unfold definiteIntegral
  rw [antiderivative_scale,
    CCL.FinitePolynomial.eval_scale,
    CCL.FinitePolynomial.eval_scale]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, sub_re, sub_im] <;> ring1

/-- The finite average-change kernel of the antiderivative. -/
def integralKernel (polynomial : Polynomial) (left right : Gaussian) :
    Gaussian :=
  CCL.DividedDifference.polynomialKernel
    (antiderivative 0 polynomial) right left

/-- Infinitesimal-free interval form of the fundamental theorem: the
constructed integral is exactly displacement times one displayed finite
secant kernel. -/
theorem definiteIntegral_factor (polynomial : Polynomial)
    (left right : Gaussian) :
    definiteIntegral polynomial left right =
      (right - left) * integralKernel polynomial left right :=
  CCL.DividedDifference.eval_sub_factor
    (antiderivative 0 polynomial) right left

/-- Diagonal substitution in the already-expanded interval kernel returns
the integrand value. -/
theorem integralKernel_diagonal (polynomial : Polynomial) (point : Gaussian) :
    integralKernel polynomial point point = eval polynomial point := by
  rw [integralKernel,
    CCL.DividedDifference.polynomialKernel_diagonal]
  rw [derivative_antiderivative]

/-! ## Elementary polynomial initial-value problems -/

/-- Exact finite solution table for `y' = forcing`, with displayed rational
initial time and value. -/
def polynomialIVPSolution (forcing : Polynomial)
    (initialTime initialValue : Coordinate) : Polynomial :=
  let primitive := antiderivative 0 forcing
  add
    (constant (initialValue - scalarEval initialTime primitive))
    primitive

theorem polynomialIVPSolution_initial (forcing : Polynomial)
    (initialTime initialValue : Coordinate) :
    scalarEval initialTime
      (polynomialIVPSolution forcing initialTime initialValue) =
        initialValue := by
  simp only [polynomialIVPSolution, scalarEval_add,
    scalarEval_constant]
  ring1

/-- The returned finite table satisfies its polynomial forcing equation
coefficient by coefficient. -/
theorem polynomialIVPSolution_derivative (forcing : Polynomial)
    (initialTime initialValue : Coordinate) :
    CoefficientwiseEqual
      (derivative
        (polynomialIVPSolution forcing initialTime initialValue))
      forcing := by
  let primitive := antiderivative 0 forcing
  let offset := initialValue - scalarEval initialTime primitive
  exact coefficientwise_trans
    (derivative_add (constant offset) primitive)
    (coefficientwise_trans
      (coefficientwise_add (derivative_constant offset)
        (by
          rw [show derivative primitive = forcing by
            exact derivative_antiderivative 0 forcing]
          exact coefficientwise_refl forcing))
      (coefficientwise_zero_add forcing))

/-- The finite exponential polynomial satisfies `y' = y` up to precisely its
last displayed Taylor term: its derivative is the preceding polynomial. -/
theorem exponentialODE_derivative (degree : Nat) :
    CoefficientwiseEqual
      (derivative (exponential (degree + 1)))
      (exponential degree) :=
  derivative_exponential_succ degree

/-- Pointwise form of the exact finite ODE defect. -/
theorem exponentialODE_defect (degree : Nat) (point : Gaussian) :
    eval (exponential (degree + 1)) point -
        eval (derivative (exponential (degree + 1))) point =
      CCL.TranscendentalLaws.taylorTerm point (degree + 1) := by
  rw [eval_eq_of_coefficientwise (derivative_exponential_succ degree)]
  rw [eval_exponential, eval_exponential,
    CCL.TranscendentalLaws.truncatedExp_succ]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, add_re, add_im] <;> ring1

end CCL.FiniteIntegration
