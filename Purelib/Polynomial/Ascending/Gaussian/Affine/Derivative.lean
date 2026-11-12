module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Gaussian.Arithmetic
import Purelib.Polynomial.Ascending.Gaussian.Arithmetic
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Coefficient
public import Purelib.Polynomial.Ascending.Gaussian.Derivative

public import Purelib.Polynomial.Ascending.Gaussian.Affine
import Purelib.Tactic.Ring

import Purelib.Algebra.NatCast

/-!
# Coefficientwise differentiation of affine substitutions

The exact finite coefficient product rule and degree-weight recursion prove
the affine Horner chain rule. The retained offset, slope and original coefficient
table determine every scalar identity, including zero slope and empty tables.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Affine.Derivative

open Purelib.Data
open Purelib.Polynomial
open Purelib.Algebra

public section
open Purelib.Data.Gaussian.Basic.Canonical

/-- Differentiate the product of an affine factor and a Gaussian polynomial.

The coefficientwise product rule gives slope times the polynomial plus the affine factor times its derivative. -/
theorem derivative_affineMul (offset slope : Gaussian.Basic.Canonical) (polynomial :
  CoefficientPolynomial) :
    Coefficient.CoefficientwiseEqual (Derivative.derivative
      (affineMul offset slope polynomial))
      (Arithmetic.add (Arithmetic.scale slope polynomial)
        (affineMul offset slope (Derivative.derivative polynomial))) := by
  intro degree
  rw [Derivative.coefficient_derivative, coefficient_affineMul_succ,
    Arithmetic.coefficient_add, Arithmetic.coefficient_scale]
  cases degree with
  | zero =>
      simp only [coefficient_affineMul_zero,
        Derivative.coefficient_derivative, Nat.zero_add, Nat.cast_one]
      ring1
  | succ degree =>
      simp only [coefficient_affineMul_succ,
        Derivative.coefficient_derivative, NatCast.add, Nat.cast_one]
      ring1

/-- Increasing every natural degree weight adds the same original coefficient table.

A successor weight splits into its preceding weight and one at each retained
entry. The recursive list identity preserves the original head and tail order. -/
theorem derivativeFrom_succ (factor : Nat) : ∀ coefficients,
    Derivative.derivativeFrom (factor + 1) coefficients =
      Data.List.Gaussian.Arithmetic.addCoefficients (Derivative.derivativeFrom factor coefficients)
        coefficients
  | [] => rfl
  | head :: tail => by
      rw [Derivative.derivativeFrom, Derivative.derivativeFrom,
        Data.List.Gaussian.Arithmetic.addCoefficients,
        Derivative.derivativeFrom_succ (factor + 1) tail]
      congr 1
      rw [NatCast.add, Nat.cast_one]
      ring1

/-- Decompose the weighted derivative tail before affine substitution.

The coefficientwise identity separates the retained table from the affine factor
multiplying its derivative. It includes the empty table and uses exact successor weights. -/
theorem affine_derivativeTail (offset slope : Gaussian.Basic.Canonical) : ∀ tail,
    Coefficient.CoefficientwiseEqual (affineCoefficients offset slope
      (Derivative.derivativeFrom 1 tail))
      (Arithmetic.add (affineCoefficients offset slope tail)
        (affineMul offset slope (affine
          (Derivative.derivative ⟨tail⟩) offset slope)))
  | [] => by
      intro degree
      change Coefficient.coefficient Basic.zero degree =
        Coefficient.coefficient (Arithmetic.add Basic.zero
          (affineMul offset slope Basic.zero)) degree
      rw [Arithmetic.coefficient_add]
      change (0 : Gaussian.Basic.Canonical) = 0 +
        Coefficient.coefficient (affineMul offset slope
          Basic.zero) degree
      cases degree with
      | zero =>
          rw [coefficient_affineMul_zero]
          change (0 : Gaussian.Basic.Canonical) = 0 + offset * 0
          ring1
      | succ degree =>
          rw [coefficient_affineMul_succ]
          change (0 : Gaussian.Basic.Canonical) = 0 + (offset * 0 + slope * 0)
          ring1
  | head :: tail => by
      change Coefficient.CoefficientwiseEqual
        (Arithmetic.add (Basic.constant ((1 : Gaussian.Basic.Canonical) * head))
          (affineMul offset slope (affineCoefficients offset slope
            (Derivative.derivativeFrom 2 tail))))
        (Arithmetic.add (Arithmetic.add (Basic.constant head)
          (affineMul offset slope (affineCoefficients offset slope
          tail)))
          (affineMul offset slope (affineCoefficients offset slope
            (Derivative.derivativeFrom 1 tail))))
      rw [Gaussian.Basic.one_mul, show 2 = 1 + 1 from rfl, derivativeFrom_succ]
      have transported := coefficientwise_affineMul offset slope
        (affineCoefficients_add offset slope (Derivative.derivativeFrom 1
          tail) tail)
      have distributed := affineMul_add offset slope
        (affineCoefficients offset slope (Derivative.derivativeFrom 1
          tail))
        (affineCoefficients offset slope tail)
      intro degree
      rw [Arithmetic.coefficient_add, transported degree, distributed degree]
      simp only [Arithmetic.coefficient_add]
      ring1

/-- Affine Horner substitution satisfies the coefficientwise chain rule.

The derivative of the substituted table equals the slope times the affine substitution of the original derivative. -/
theorem derivative_affineCoefficients (offset slope : Gaussian.Basic.Canonical) : ∀ coefficients,
    Coefficient.CoefficientwiseEqual (Derivative.derivative
      (affineCoefficients offset slope coefficients))
      (Arithmetic.scale slope (affine
        (Derivative.derivative ⟨coefficients⟩) offset slope))
  | [] => by
      intro degree
      change Coefficient.coefficient (Derivative.derivative
        Basic.zero) degree = Coefficient.coefficient
        (Arithmetic.scale slope Basic.zero) degree
      rw [Derivative.derivative_zero, Arithmetic.coefficient_scale,
        Coefficient.coefficient_zero, Gaussian.Basic.mul_zero]
  | head :: tail => by
      have transported := coefficientwise_affineMul offset slope
        (Derivative.derivative_affineCoefficients offset slope tail)
      have scaled := affineMul_scale offset slope slope
        (affine (Derivative.derivative ⟨tail⟩) offset slope)
      intro degree
      change Coefficient.coefficient (Derivative.derivative
          (Arithmetic.add (Basic.constant head)
            (affineMul offset slope (affineCoefficients offset slope
            tail))))
          degree =
        Coefficient.coefficient (Arithmetic.scale slope
          (affineCoefficients offset slope (Derivative.derivativeFrom 1
          tail))) degree
      rw [Derivative.derivative_add _ _ degree, Arithmetic.coefficient_add,
        Derivative.derivative_constant,
        Coefficient.coefficient_zero, Gaussian.Basic.zero_add, derivative_affineMul _ _ _ degree,
        Arithmetic.coefficient_add, transported degree, scaled degree]
      simp only [Arithmetic.coefficient_scale]
      rw [affine_derivativeTail offset slope tail degree, Arithmetic.coefficient_add]
      ring1

/-- The chain rule is an identity of finite coefficient tables. -/
theorem derivative_affine (polynomial : CoefficientPolynomial) (offset slope : Gaussian.Basic.Canonical) :
    Coefficient.CoefficientwiseEqual (Derivative.derivative
      (affine polynomial offset slope))
      (Arithmetic.scale slope (affine
        (Derivative.derivative polynomial) offset slope)) :=
  derivative_affineCoefficients offset slope polynomial.coefficients

end

end Purelib.Polynomial.Ascending.Gaussian.Affine.Derivative
