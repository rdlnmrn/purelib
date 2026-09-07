import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ConstructiveGaussian
import CCL.Geometry.FiniteGeometric

/-!
# Finite Gaussian-coefficient polynomials

The general transcendental Taylor kernel deliberately uses rational-real
coefficients.  Period integration needs a separate, equally finite kernel:
the coefficient of `dx` along a complex path is Gaussian-valued even when the
path parameter is rational.  Coefficients here are therefore displayed
Gaussian rationals, stored from constant term upward.
-/

namespace CCL.FiniteGaussianPolynomial

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian

open RFAP.ConstructiveGaussian.Gaussian

structure Polynomial where
  coefficients : List Gaussian
deriving DecidableEq

def zero : Polynomial := ⟨[]⟩

def constant (value : Gaussian) : Polynomial := ⟨[value]⟩

/-- Low-to-high Horner evaluation. -/
def evalCoeffs (coefficients : List Gaussian) (input : Gaussian) : Gaussian :=
  coefficients.foldr (fun coefficient total => coefficient + input * total) 0

def eval (polynomial : Polynomial) (input : Gaussian) : Gaussian :=
  evalCoeffs polynomial.coefficients input

@[simp] theorem eval_zero (input : Gaussian) : eval zero input = 0 := rfl

@[simp] theorem eval_constant (value input : Gaussian) :
    eval (constant value) input = value := by
  unfold eval constant evalCoeffs
  simp only [List.foldr_cons, List.foldr_nil, mul_zero, add_zero]

/-- Coefficient list of the zero-constant antiderivative. -/
def antiderivativeCoefficients : Nat -> List Gaussian -> List Gaussian
  | _, [] => []
  | degree, coefficient :: remaining =>
      (coefficient / ((degree + 1 : Nat) : Gaussian)) ::
        antiderivativeCoefficients (degree + 1) remaining

def antiderivative (polynomial : Polynomial) : Polynomial :=
  ⟨0 :: antiderivativeCoefficients 0 polynomial.coefficients⟩

/-- Exact finite integral of a displayed Gaussian polynomial. -/
def definiteIntegral (polynomial : Polynomial)
    (start finish : Gaussian) : Gaussian :=
  eval (antiderivative polynomial) finish -
    eval (antiderivative polynomial) start

@[simp] theorem definiteIntegral_zero (start finish : Gaussian) :
    definiteIntegral zero start finish = 0 := by
  unfold definiteIntegral antiderivative zero eval evalCoeffs
  simp only [antiderivativeCoefficients, List.foldr_cons, List.foldr_nil,
    mul_zero, add_zero, sub_self]

@[simp] theorem definiteIntegral_constant (value start finish : Gaussian) :
    definiteIntegral (constant value) start finish =
      value * (finish - start) := by
  unfold definiteIntegral antiderivative constant
  change (0 + finish * (value / (1 : Gaussian) + finish * 0)) -
      (0 + start * (value / (1 : Gaussian) + start * 0)) =
    value * (finish - start)
  have divOne : value / (1 : Gaussian) = value := by
    change value * (1 : Gaussian)⁻¹ = value
    rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq,
      RFAP.ConstructiveGaussian.Gaussian.inv_one_direct,
      RFAP.ConstructiveGaussian.Gaussian.mul_one]
  rw [divOne]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.zero_add,
      RFAP.ConstructiveGaussian.Gaussian.mul_zero,
      RFAP.ConstructiveGaussian.Gaussian.add_zero,
      sub_re, sub_im, mul_re, mul_im] <;>
    ring1

theorem definiteIntegral_reverse (polynomial : Polynomial)
    (start finish : Gaussian) :
    definiteIntegral polynomial finish start =
      -definiteIntegral polynomial start finish := by
  unfold definiteIntegral
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1

end CCL.FiniteGaussianPolynomial
