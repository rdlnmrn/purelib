module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Coefficientwise
public import Purelib.Polynomial.Ascending.Rational.Composition
import Purelib.Polynomial.Ascending.Rational.Derivative

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Polynomial.Ascending.Rational.Basic (CoefficientPolynomial)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Low-to-high finite polynomials for transcendental identities

This is a deliberately small, executable polynomial kernel.  A polynomial is
only a displayed finite list of rational coefficients, stored from constant
term upward.  It exists to prove finite Taylor identities without importing a
sparse-polynomial or formal-power-series API.
-/

namespace Purelib.Polynomial.Ascending.Rational.Composition.Derivative

/-- Split a substituted degree-weighted tail into its unweighted part and inner times its derivative.

The table weights start at one, so the decomposition is the finite identity for differentiating an indeterminate times
the tail. -/
theorem composeDerivativeTail (inner :
  CoefficientPolynomial) : ∀ tail,
    Coefficientwise.CoefficientwiseEqual
      (composeCoefficients (Derivative.derivativeFrom 1 tail) inner)
      (Basic.add (composeCoefficients tail inner)
        (Basic.mul inner (compose
          (Derivative.derivative ⟨tail⟩) inner)))
  | [] =>
      Coefficientwise.coefficientwise_trans
        (Coefficientwise.coefficientwise_symm
          (Coefficientwise.coefficientwise_add_zero Basic.zero))
        (Coefficientwise.coefficientwise_add (Coefficientwise.coefficientwise_refl
          Basic.zero)
          (Coefficientwise.coefficientwise_symm
            (Coefficientwise.coefficientwise_mul_zero inner)))
  | coefficient :: remaining => by
      change Coefficientwise.CoefficientwiseEqual
        (Basic.add (Basic.constant (((1 : Nat) : Fraction.Rational) *
          coefficient))
          (Basic.mul inner
            (composeCoefficients (Derivative.derivativeFrom 2
              remaining) inner)))
        (Basic.add
          (Basic.add (Basic.constant coefficient)
            (Basic.mul inner (composeCoefficients remaining inner)))
          (Basic.mul inner
            (composeCoefficients (Derivative.derivativeFrom 1
              remaining) inner)))
      exact Coefficientwise.coefficientwise_trans
        (Coefficientwise.coefficientwise_add
          (Coefficientwise.coefficientwise_constant_one_mul coefficient)
          (Coefficientwise.coefficientwise_refl _))
        (Coefficientwise.coefficientwise_trans
          (Coefficientwise.coefficientwise_add
            (Coefficientwise.coefficientwise_refl _)
            (Coefficientwise.coefficientwise_mul
              (Coefficientwise.coefficientwise_refl inner)
              (composeCoefficients_derivativeFrom_succ 1 remaining inner)))
          (Coefficientwise.coefficientwise_trans
            (Coefficientwise.coefficientwise_add
              (Coefficientwise.coefficientwise_refl _)
              (Coefficientwise.coefficientwise_mul_add inner
                (composeCoefficients (Derivative.derivativeFrom 1
                  remaining) inner)
                (composeCoefficients remaining inner)))
            (Coefficientwise.coefficientwise_trans
              (Coefficientwise.coefficientwise_add
                (Coefficientwise.coefficientwise_refl _)
                (Coefficientwise.coefficientwise_add_comm
                  (Basic.mul inner
                    (composeCoefficients (Derivative.derivativeFrom 1
                      remaining) inner))
                  (Basic.mul inner (composeCoefficients remaining
                    inner))))
              (Coefficientwise.coefficientwise_symm
                (Coefficientwise.coefficientwise_add_assoc
                  (Basic.constant coefficient)
                  (Basic.mul inner (composeCoefficients remaining
                    inner))
                  (Basic.mul inner
                    (composeCoefficients
                      (Derivative.derivativeFrom 1 remaining) inner)))))))

/-- The chain rule holds coefficientwise for Horner substitution of a finite table.

Differentiate the inner polynomial and multiply it by the outer derivative substituted at the same inner polynomial. -/
theorem derivative_composeCoefficients (inner :
  CoefficientPolynomial) : ∀ outer,
    Coefficientwise.CoefficientwiseEqual
      (Derivative.derivative (composeCoefficients outer inner))
      (Basic.mul (Derivative.derivative inner)
        (compose (Derivative.derivative ⟨outer⟩) inner))
  | [] =>
      Coefficientwise.coefficientwise_trans Derivative.derivative_zero
        (Coefficientwise.coefficientwise_symm
          (Coefficientwise.coefficientwise_mul_zero (Derivative.derivative
            inner)))
  | head :: tail => by
      let tailComposition := composeCoefficients tail inner
      let outerDerivativeComposition :=
        composeCoefficients (Derivative.derivativeFrom 1 tail) inner
      have reordered :
          Coefficientwise.CoefficientwiseEqual
            (Basic.mul inner
              (Basic.mul (Derivative.derivative inner)
                (compose (Derivative.derivative ⟨tail⟩) inner)))
            (Basic.mul (Derivative.derivative inner)
              (Basic.mul inner (compose
                (Derivative.derivative ⟨tail⟩) inner))) :=
        Coefficientwise.coefficientwise_trans
          (Coefficientwise.coefficientwise_symm
            (Coefficientwise.coefficientwise_mul_assoc inner
              (Derivative.derivative inner)
              (compose (Derivative.derivative ⟨tail⟩) inner)))
          (Coefficientwise.coefficientwise_trans
            (Coefficientwise.coefficientwise_mul
              (Coefficientwise.coefficientwise_mul_comm inner
                (Derivative.derivative inner))
              (Coefficientwise.coefficientwise_refl _))
            (Coefficientwise.coefficientwise_mul_assoc (Derivative.derivative
              inner) inner
              (compose (Derivative.derivative ⟨tail⟩) inner)))
      change Coefficientwise.CoefficientwiseEqual
        (Derivative.derivative (Basic.add (Basic.constant head)
          (Basic.mul inner tailComposition)))
        (Basic.mul (Derivative.derivative inner) outerDerivativeComposition)
      exact Coefficientwise.coefficientwise_trans
        (Derivative.derivative_add (Basic.constant head)
          (Basic.mul inner tailComposition))
        (Coefficientwise.coefficientwise_trans
          (Coefficientwise.coefficientwise_add
            (Derivative.derivative_constant head)
            (Derivative.derivative_mul inner tailComposition))
          (Coefficientwise.coefficientwise_trans
            (Coefficientwise.coefficientwise_zero_add
              (Basic.add (Basic.mul (Derivative.derivative
                inner) tailComposition)
                (Basic.mul inner (Derivative.derivative tailComposition))))
            (Coefficientwise.coefficientwise_trans
              (Coefficientwise.coefficientwise_add
                (Coefficientwise.coefficientwise_refl _)
                (Coefficientwise.coefficientwise_trans
                  (Coefficientwise.coefficientwise_mul
                    (Coefficientwise.coefficientwise_refl inner)
                    (derivative_composeCoefficients inner
                      tail))
                  reordered))
              (Coefficientwise.coefficientwise_trans
                (Coefficientwise.coefficientwise_symm
                  (Coefficientwise.coefficientwise_mul_add (Derivative.derivative
                    inner)
                    tailComposition
                    (Basic.mul inner (compose
                      (Derivative.derivative ⟨tail⟩) inner))))
                (Coefficientwise.coefficientwise_mul
                  (Coefficientwise.coefficientwise_refl (Derivative.derivative
                  inner))
                  (Coefficientwise.coefficientwise_symm
                    (composeDerivativeTail inner tail)))))))

/-- Finite polynomial composition satisfies the chain rule coefficientwise. -/
theorem derivative_compose (outer inner :
  CoefficientPolynomial) :
    Coefficientwise.CoefficientwiseEqual (Derivative.derivative
      (compose outer inner))
      (Basic.mul (Derivative.derivative inner)
        (compose (Derivative.derivative outer) inner)) :=
  derivative_composeCoefficients inner outer.coefficients
end Purelib.Polynomial.Ascending.Rational.Composition.Derivative

end
