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
    Ascending.Gaussian.Coefficient.CoefficientwiseEqual (Ascending.Gaussian.Derivative.derivative
      (Ascending.Gaussian.Affine.affineMul offset slope polynomial))
      (Ascending.Gaussian.Arithmetic.add (Ascending.Gaussian.Arithmetic.scale slope polynomial)
        (Ascending.Gaussian.Affine.affineMul offset slope (Ascending.Gaussian.Derivative.derivative polynomial))) := by
  intro degree
  rw [Ascending.Gaussian.Derivative.coefficient_derivative, Ascending.Gaussian.Affine.coefficient_affineMul_succ,
    Ascending.Gaussian.Arithmetic.coefficient_add, Ascending.Gaussian.Arithmetic.coefficient_scale]
  cases degree with
  | zero =>
      simp only [Ascending.Gaussian.Affine.coefficient_affineMul_zero,
        Ascending.Gaussian.Derivative.coefficient_derivative, Nat.zero_add, Nat.cast_one]
      ring1
  | succ degree =>
      simp only [Ascending.Gaussian.Affine.coefficient_affineMul_succ,
        Ascending.Gaussian.Derivative.coefficient_derivative, NatCast.add, Nat.cast_one]
      ring1

/-- Increasing every natural degree weight adds the same original coefficient table.

A successor weight splits into its preceding weight and one at each retained
entry. The recursive list identity preserves the original head and tail order. -/
theorem derivativeFrom_succ (factor : Nat) : ∀ coefficients,
    Ascending.Gaussian.Derivative.derivativeFrom (factor + 1) coefficients =
      Data.List.Gaussian.Arithmetic.addCoefficients (Ascending.Gaussian.Derivative.derivativeFrom factor coefficients)
        coefficients
  | [] => rfl
  | head :: tail => by
      rw [Ascending.Gaussian.Derivative.derivativeFrom, Ascending.Gaussian.Derivative.derivativeFrom,
        Data.List.Gaussian.Arithmetic.addCoefficients,
        Purelib.Polynomial.Ascending.Gaussian.Affine.Derivative.derivativeFrom_succ (factor + 1) tail]
      congr 1
      rw [NatCast.add, Nat.cast_one]
      ring1

/-- Decompose the weighted derivative tail before affine substitution.

The coefficientwise identity separates the retained table from the affine factor
multiplying its derivative. It includes the empty table and uses exact successor weights. -/
theorem affine_derivativeTail (offset slope : Gaussian.Basic.Canonical) : ∀ tail,
    Ascending.Gaussian.Coefficient.CoefficientwiseEqual (Ascending.Gaussian.Affine.affineCoefficients offset slope
      (Ascending.Gaussian.Derivative.derivativeFrom 1 tail))
      (Ascending.Gaussian.Arithmetic.add (Ascending.Gaussian.Affine.affineCoefficients offset slope tail)
        (Ascending.Gaussian.Affine.affineMul offset slope (Ascending.Gaussian.Affine.affine
          (Ascending.Gaussian.Derivative.derivative ⟨tail⟩) offset slope)))
  | [] => by
      intro degree
      change Ascending.Gaussian.Coefficient.coefficient Ascending.Gaussian.Basic.zero degree =
        Ascending.Gaussian.Coefficient.coefficient (Ascending.Gaussian.Arithmetic.add Ascending.Gaussian.Basic.zero
          (Ascending.Gaussian.Affine.affineMul offset slope Ascending.Gaussian.Basic.zero)) degree
      rw [Ascending.Gaussian.Arithmetic.coefficient_add]
      change (0 : Gaussian.Basic.Canonical) = 0 +
        Ascending.Gaussian.Coefficient.coefficient (Ascending.Gaussian.Affine.affineMul offset slope
          Ascending.Gaussian.Basic.zero) degree
      cases degree with
      | zero =>
          rw [Ascending.Gaussian.Affine.coefficient_affineMul_zero]
          change (0 : Gaussian.Basic.Canonical) = 0 + offset * 0
          ring1
      | succ degree =>
          rw [Ascending.Gaussian.Affine.coefficient_affineMul_succ]
          change (0 : Gaussian.Basic.Canonical) = 0 + (offset * 0 + slope * 0)
          ring1
  | head :: tail => by
      change Ascending.Gaussian.Coefficient.CoefficientwiseEqual
        (Ascending.Gaussian.Arithmetic.add (Ascending.Gaussian.Basic.constant ((1 : Gaussian.Basic.Canonical) * head))
          (Ascending.Gaussian.Affine.affineMul offset slope (Ascending.Gaussian.Affine.affineCoefficients offset slope
            (Ascending.Gaussian.Derivative.derivativeFrom 2 tail))))
        (Ascending.Gaussian.Arithmetic.add (Ascending.Gaussian.Arithmetic.add (Ascending.Gaussian.Basic.constant head)
          (Ascending.Gaussian.Affine.affineMul offset slope (Ascending.Gaussian.Affine.affineCoefficients offset slope
          tail)))
          (Ascending.Gaussian.Affine.affineMul offset slope (Ascending.Gaussian.Affine.affineCoefficients offset slope
            (Ascending.Gaussian.Derivative.derivativeFrom 1 tail))))
      rw [Gaussian.Basic.one_mul, show 2 = 1 + 1 from rfl, derivativeFrom_succ]
      have transported := Ascending.Gaussian.Affine.coefficientwise_affineMul offset slope
        (Ascending.Gaussian.Affine.affineCoefficients_add offset slope (Ascending.Gaussian.Derivative.derivativeFrom 1
          tail) tail)
      have distributed := Ascending.Gaussian.Affine.affineMul_add offset slope
        (Ascending.Gaussian.Affine.affineCoefficients offset slope (Ascending.Gaussian.Derivative.derivativeFrom 1
          tail))
        (Ascending.Gaussian.Affine.affineCoefficients offset slope tail)
      intro degree
      rw [Ascending.Gaussian.Arithmetic.coefficient_add, transported degree, distributed degree]
      simp only [Ascending.Gaussian.Arithmetic.coefficient_add]
      ring1

/-- Affine Horner substitution satisfies the coefficientwise chain rule.

The derivative of the substituted table equals the slope times the affine substitution of the original derivative. -/
theorem derivative_affineCoefficients (offset slope : Gaussian.Basic.Canonical) : ∀ coefficients,
    Ascending.Gaussian.Coefficient.CoefficientwiseEqual (Ascending.Gaussian.Derivative.derivative
      (Ascending.Gaussian.Affine.affineCoefficients offset slope coefficients))
      (Ascending.Gaussian.Arithmetic.scale slope (Ascending.Gaussian.Affine.affine
        (Ascending.Gaussian.Derivative.derivative ⟨coefficients⟩) offset slope))
  | [] => by
      intro degree
      change Ascending.Gaussian.Coefficient.coefficient (Ascending.Gaussian.Derivative.derivative
        Ascending.Gaussian.Basic.zero) degree = Ascending.Gaussian.Coefficient.coefficient
        (Ascending.Gaussian.Arithmetic.scale slope Ascending.Gaussian.Basic.zero) degree
      rw [Ascending.Gaussian.Derivative.derivative_zero, Ascending.Gaussian.Arithmetic.coefficient_scale,
        Ascending.Gaussian.Coefficient.coefficient_zero, Gaussian.Basic.mul_zero]
  | head :: tail => by
      have transported := Ascending.Gaussian.Affine.coefficientwise_affineMul offset slope
        (Purelib.Polynomial.Ascending.Gaussian.Affine.Derivative.derivative_affineCoefficients offset slope tail)
      have scaled := Ascending.Gaussian.Affine.affineMul_scale offset slope slope
        (Ascending.Gaussian.Affine.affine (Ascending.Gaussian.Derivative.derivative ⟨tail⟩) offset slope)
      intro degree
      change Ascending.Gaussian.Coefficient.coefficient (Ascending.Gaussian.Derivative.derivative
          (Ascending.Gaussian.Arithmetic.add (Ascending.Gaussian.Basic.constant head)
            (Ascending.Gaussian.Affine.affineMul offset slope (Ascending.Gaussian.Affine.affineCoefficients offset slope
            tail))))
          degree =
        Ascending.Gaussian.Coefficient.coefficient (Ascending.Gaussian.Arithmetic.scale slope
          (Ascending.Gaussian.Affine.affineCoefficients offset slope (Ascending.Gaussian.Derivative.derivativeFrom 1
          tail))) degree
      rw [Ascending.Gaussian.Derivative.derivative_add _ _ degree, Ascending.Gaussian.Arithmetic.coefficient_add,
        Ascending.Gaussian.Derivative.derivative_constant,
        Ascending.Gaussian.Coefficient.coefficient_zero, Gaussian.Basic.zero_add, derivative_affineMul _ _ _ degree,
        Ascending.Gaussian.Arithmetic.coefficient_add, transported degree, scaled degree]
      simp only [Ascending.Gaussian.Arithmetic.coefficient_scale]
      rw [affine_derivativeTail offset slope tail degree, Ascending.Gaussian.Arithmetic.coefficient_add]
      ring1

/-- The chain rule is an identity of finite coefficient tables. -/
theorem derivative_affine (polynomial : CoefficientPolynomial) (offset slope : Gaussian.Basic.Canonical) :
    Ascending.Gaussian.Coefficient.CoefficientwiseEqual (Ascending.Gaussian.Derivative.derivative
      (Ascending.Gaussian.Affine.affine polynomial offset slope))
      (Ascending.Gaussian.Arithmetic.scale slope (Ascending.Gaussian.Affine.affine
        (Ascending.Gaussian.Derivative.derivative polynomial) offset slope)) :=
  derivative_affineCoefficients offset slope polynomial.coefficients

end

end Purelib.Polynomial.Ascending.Gaussian.Affine.Derivative
