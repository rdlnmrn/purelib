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
    Ascending.Rational.Coefficientwise.CoefficientwiseEqual
      (Ascending.Rational.Composition.composeCoefficients (Ascending.Rational.Derivative.derivativeFrom 1 tail) inner)
      (Ascending.Rational.Basic.add (Ascending.Rational.Composition.composeCoefficients tail inner)
        (Ascending.Rational.Basic.mul inner (Ascending.Rational.Composition.compose
          (Ascending.Rational.Derivative.derivative ⟨tail⟩) inner)))
  | [] =>
      Ascending.Rational.Coefficientwise.coefficientwise_trans
        (Ascending.Rational.Coefficientwise.coefficientwise_symm
          (Ascending.Rational.Coefficientwise.coefficientwise_add_zero Ascending.Rational.Basic.zero))
        (Ascending.Rational.Coefficientwise.coefficientwise_add (Ascending.Rational.Coefficientwise.coefficientwise_refl
          Ascending.Rational.Basic.zero)
          (Ascending.Rational.Coefficientwise.coefficientwise_symm
            (Ascending.Rational.Coefficientwise.coefficientwise_mul_zero inner)))
  | coefficient :: remaining => by
      change Ascending.Rational.Coefficientwise.CoefficientwiseEqual
        (Ascending.Rational.Basic.add (Ascending.Rational.Basic.constant (((1 : Nat) : Fraction.Rational) *
          coefficient))
          (Ascending.Rational.Basic.mul inner
            (Ascending.Rational.Composition.composeCoefficients (Ascending.Rational.Derivative.derivativeFrom 2
              remaining) inner)))
        (Ascending.Rational.Basic.add
          (Ascending.Rational.Basic.add (Ascending.Rational.Basic.constant coefficient)
            (Ascending.Rational.Basic.mul inner (Ascending.Rational.Composition.composeCoefficients remaining inner)))
          (Ascending.Rational.Basic.mul inner
            (Ascending.Rational.Composition.composeCoefficients (Ascending.Rational.Derivative.derivativeFrom 1
              remaining) inner)))
      exact Ascending.Rational.Coefficientwise.coefficientwise_trans
        (Ascending.Rational.Coefficientwise.coefficientwise_add
          (Ascending.Rational.Coefficientwise.coefficientwise_constant_one_mul coefficient)
          (Ascending.Rational.Coefficientwise.coefficientwise_refl _))
        (Ascending.Rational.Coefficientwise.coefficientwise_trans
          (Ascending.Rational.Coefficientwise.coefficientwise_add
            (Ascending.Rational.Coefficientwise.coefficientwise_refl _)
            (Ascending.Rational.Coefficientwise.coefficientwise_mul
              (Ascending.Rational.Coefficientwise.coefficientwise_refl inner)
              (Ascending.Rational.Composition.composeCoefficients_derivativeFrom_succ 1 remaining inner)))
          (Ascending.Rational.Coefficientwise.coefficientwise_trans
            (Ascending.Rational.Coefficientwise.coefficientwise_add
              (Ascending.Rational.Coefficientwise.coefficientwise_refl _)
              (Ascending.Rational.Coefficientwise.coefficientwise_mul_add inner
                (Ascending.Rational.Composition.composeCoefficients (Ascending.Rational.Derivative.derivativeFrom 1
                  remaining) inner)
                (Ascending.Rational.Composition.composeCoefficients remaining inner)))
            (Ascending.Rational.Coefficientwise.coefficientwise_trans
              (Ascending.Rational.Coefficientwise.coefficientwise_add
                (Ascending.Rational.Coefficientwise.coefficientwise_refl _)
                (Ascending.Rational.Coefficientwise.coefficientwise_add_comm
                  (Ascending.Rational.Basic.mul inner
                    (Ascending.Rational.Composition.composeCoefficients (Ascending.Rational.Derivative.derivativeFrom 1
                      remaining) inner))
                  (Ascending.Rational.Basic.mul inner (Ascending.Rational.Composition.composeCoefficients remaining
                    inner))))
              (Ascending.Rational.Coefficientwise.coefficientwise_symm
                (Ascending.Rational.Coefficientwise.coefficientwise_add_assoc
                  (Ascending.Rational.Basic.constant coefficient)
                  (Ascending.Rational.Basic.mul inner (Ascending.Rational.Composition.composeCoefficients remaining
                    inner))
                  (Ascending.Rational.Basic.mul inner
                    (Ascending.Rational.Composition.composeCoefficients
                      (Ascending.Rational.Derivative.derivativeFrom 1 remaining) inner)))))))

/-- The chain rule holds coefficientwise for Horner substitution of a finite table.

Differentiate the inner polynomial and multiply it by the outer derivative substituted at the same inner polynomial. -/
theorem derivative_composeCoefficients (inner :
  CoefficientPolynomial) : ∀ outer,
    Ascending.Rational.Coefficientwise.CoefficientwiseEqual
      (Ascending.Rational.Derivative.derivative (Ascending.Rational.Composition.composeCoefficients outer inner))
      (Ascending.Rational.Basic.mul (Ascending.Rational.Derivative.derivative inner)
        (Ascending.Rational.Composition.compose (Ascending.Rational.Derivative.derivative ⟨outer⟩) inner))
  | [] =>
      Ascending.Rational.Coefficientwise.coefficientwise_trans Ascending.Rational.Derivative.derivative_zero
        (Ascending.Rational.Coefficientwise.coefficientwise_symm
          (Ascending.Rational.Coefficientwise.coefficientwise_mul_zero (Ascending.Rational.Derivative.derivative
            inner)))
  | head :: tail => by
      let tailComposition := Ascending.Rational.Composition.composeCoefficients tail inner
      let outerDerivativeComposition :=
        Ascending.Rational.Composition.composeCoefficients (Ascending.Rational.Derivative.derivativeFrom 1 tail) inner
      have reordered :
          Ascending.Rational.Coefficientwise.CoefficientwiseEqual
            (Ascending.Rational.Basic.mul inner
              (Ascending.Rational.Basic.mul (Ascending.Rational.Derivative.derivative inner)
                (Ascending.Rational.Composition.compose (Ascending.Rational.Derivative.derivative ⟨tail⟩) inner)))
            (Ascending.Rational.Basic.mul (Ascending.Rational.Derivative.derivative inner)
              (Ascending.Rational.Basic.mul inner (Ascending.Rational.Composition.compose
                (Ascending.Rational.Derivative.derivative ⟨tail⟩) inner))) :=
        Ascending.Rational.Coefficientwise.coefficientwise_trans
          (Ascending.Rational.Coefficientwise.coefficientwise_symm
            (Ascending.Rational.Coefficientwise.coefficientwise_mul_assoc inner
              (Ascending.Rational.Derivative.derivative inner)
              (Ascending.Rational.Composition.compose (Ascending.Rational.Derivative.derivative ⟨tail⟩) inner)))
          (Ascending.Rational.Coefficientwise.coefficientwise_trans
            (Ascending.Rational.Coefficientwise.coefficientwise_mul
              (Ascending.Rational.Coefficientwise.coefficientwise_mul_comm inner
                (Ascending.Rational.Derivative.derivative inner))
              (Ascending.Rational.Coefficientwise.coefficientwise_refl _))
            (Ascending.Rational.Coefficientwise.coefficientwise_mul_assoc (Ascending.Rational.Derivative.derivative
              inner) inner
              (Ascending.Rational.Composition.compose (Ascending.Rational.Derivative.derivative ⟨tail⟩) inner)))
      change Ascending.Rational.Coefficientwise.CoefficientwiseEqual
        (Ascending.Rational.Derivative.derivative (Ascending.Rational.Basic.add (Ascending.Rational.Basic.constant head)
          (Ascending.Rational.Basic.mul inner tailComposition)))
        (Ascending.Rational.Basic.mul (Ascending.Rational.Derivative.derivative inner) outerDerivativeComposition)
      exact Ascending.Rational.Coefficientwise.coefficientwise_trans
        (Ascending.Rational.Derivative.derivative_add (Ascending.Rational.Basic.constant head)
          (Ascending.Rational.Basic.mul inner tailComposition))
        (Ascending.Rational.Coefficientwise.coefficientwise_trans
          (Ascending.Rational.Coefficientwise.coefficientwise_add
            (Ascending.Rational.Derivative.derivative_constant head)
            (Ascending.Rational.Derivative.derivative_mul inner tailComposition))
          (Ascending.Rational.Coefficientwise.coefficientwise_trans
            (Ascending.Rational.Coefficientwise.coefficientwise_zero_add
              (Ascending.Rational.Basic.add (Ascending.Rational.Basic.mul (Ascending.Rational.Derivative.derivative
                inner) tailComposition)
                (Ascending.Rational.Basic.mul inner (Ascending.Rational.Derivative.derivative tailComposition))))
            (Ascending.Rational.Coefficientwise.coefficientwise_trans
              (Ascending.Rational.Coefficientwise.coefficientwise_add
                (Ascending.Rational.Coefficientwise.coefficientwise_refl _)
                (Ascending.Rational.Coefficientwise.coefficientwise_trans
                  (Ascending.Rational.Coefficientwise.coefficientwise_mul
                    (Ascending.Rational.Coefficientwise.coefficientwise_refl inner)
                    (derivative_composeCoefficients inner
                      tail))
                  reordered))
              (Ascending.Rational.Coefficientwise.coefficientwise_trans
                (Ascending.Rational.Coefficientwise.coefficientwise_symm
                  (Ascending.Rational.Coefficientwise.coefficientwise_mul_add (Ascending.Rational.Derivative.derivative
                    inner)
                    tailComposition
                    (Ascending.Rational.Basic.mul inner (Ascending.Rational.Composition.compose
                      (Ascending.Rational.Derivative.derivative ⟨tail⟩) inner))))
                (Ascending.Rational.Coefficientwise.coefficientwise_mul
                  (Ascending.Rational.Coefficientwise.coefficientwise_refl (Ascending.Rational.Derivative.derivative
                  inner))
                  (Ascending.Rational.Coefficientwise.coefficientwise_symm
                    (composeDerivativeTail inner tail)))))))

/-- Finite polynomial composition satisfies the chain rule coefficientwise. -/
theorem derivative_compose (outer inner :
  CoefficientPolynomial) :
    Ascending.Rational.Coefficientwise.CoefficientwiseEqual (Ascending.Rational.Derivative.derivative
      (Ascending.Rational.Composition.compose outer inner))
      (Ascending.Rational.Basic.mul (Ascending.Rational.Derivative.derivative inner)
        (Ascending.Rational.Composition.compose (Ascending.Rational.Derivative.derivative outer) inner)) :=
  derivative_composeCoefficients inner outer.coefficients
end Purelib.Polynomial.Ascending.Rational.Composition.Derivative

end
