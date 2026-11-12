module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Coefficientwise
import Purelib.Polynomial.Ascending.Rational.Convolution
public import Purelib.Polynomial.Ascending.Rational.Derivative
import Purelib.Polynomial.Ascending.Rational.Monomial

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Composition of ascending rational polynomials

Finite Horner substitution retains both polynomial records and their exact
coefficient tables. Coefficientwise algebra transports addition, shifts,
monomials and redundant trailing zeros through the same substitution.
-/

public section
namespace Purelib.Polynomial.Ascending.Rational.Composition

open Purelib.Data.Rat
open Purelib.Polynomial

/-- Substitute a rational polynomial into an ascending coefficient table.

Horner recursion retains the next constant entry and multiplies the substituted
remaining table by the same inner polynomial. The empty spine supplies zero. -/
@[expose] def composeCoefficients (outer : List Fraction.Rational) (inner :
  Basic.CoefficientPolynomial) :
    Basic.CoefficientPolynomial :=
  match outer with
  | [] => Basic.zero
  | coefficient :: remaining =>
      Basic.add (Basic.constant coefficient)
        (Basic.mul inner (Composition.composeCoefficients
          remaining inner))

/-- Substitute the inner polynomial into the retained outer polynomial.

The nominal outer record supplies its exact coefficient list to the finite
Horner procedure. The inner record is retained through each recursive product. -/
@[expose] def compose (outer inner : Basic.CoefficientPolynomial) :
  Basic.CoefficientPolynomial :=
  composeCoefficients outer.coefficients inner

/-- Substitution distributes over padded coefficient-list addition coefficientwise. -/
theorem composeCoefficients_add (inner : Basic.CoefficientPolynomial) : ∀ left right,
    Coefficientwise.CoefficientwiseEqual
      (composeCoefficients (Basic.addCoefficients left right) inner)
      (Basic.add (composeCoefficients left inner)
        (composeCoefficients right inner))
  | [], right =>
      Coefficientwise.coefficientwise_symm
        (Coefficientwise.coefficientwise_zero_add (composeCoefficients right inner))
  | left :: leftTail, [] => by
      rw [Basic.addCoefficients_nil_right]
      exact Coefficientwise.coefficientwise_symm
        (Coefficientwise.coefficientwise_add_zero
          (composeCoefficients (left :: leftTail) inner))
  | left :: leftTail, right :: rightTail => by
      change Coefficientwise.CoefficientwiseEqual
        (Basic.add (Basic.constant (left + right))
          (Basic.mul inner
            (composeCoefficients
              (Basic.addCoefficients leftTail rightTail) inner)))
        (Basic.add
          (Basic.add (Basic.constant left)
            (Basic.mul inner (composeCoefficients leftTail inner)))
          (Basic.add (Basic.constant right)
            (Basic.mul inner (composeCoefficients rightTail inner))))
      exact Coefficientwise.coefficientwise_trans
        (Coefficientwise.coefficientwise_add
          (Coefficientwise.coefficientwise_constant_add left right)
          (Coefficientwise.coefficientwise_refl _))
        (Coefficientwise.coefficientwise_trans
          (Coefficientwise.coefficientwise_add
            (Coefficientwise.coefficientwise_refl _)
            (Coefficientwise.coefficientwise_mul
              (Coefficientwise.coefficientwise_refl inner)
              (Composition.composeCoefficients_add inner leftTail rightTail)))
          (Coefficientwise.coefficientwise_trans
            (Coefficientwise.coefficientwise_add
              (Coefficientwise.coefficientwise_refl _)
              (Coefficientwise.coefficientwise_mul_add inner
                (composeCoefficients leftTail inner)
                (composeCoefficients rightTail inner)))
            (Coefficientwise.coefficientwise_add_rearrange
              (Basic.constant left) (Basic.constant right)
              (Basic.mul inner (composeCoefficients leftTail inner))
              (Basic.mul inner (composeCoefficients rightTail inner)))))

/-- Substitution distributes over addition of the outer polynomials coefficientwise. -/
theorem compose_add (left right inner : Basic.CoefficientPolynomial) :
    Coefficientwise.CoefficientwiseEqual (compose (Basic.add left right) inner)
      (Basic.add (compose left inner) (compose right inner)) :=
  composeCoefficients_add inner left.coefficients right.coefficients

/-- Substituting a table with all degree weights raised by one adds the unweighted substitution. -/
theorem composeCoefficients_derivativeFrom_succ (factor : Nat)
    (coefficients : List Fraction.Rational) (inner : Basic.CoefficientPolynomial) :
    Coefficientwise.CoefficientwiseEqual
      (composeCoefficients (Derivative.derivativeFrom (factor + 1) coefficients) inner)
      (Basic.add
        (composeCoefficients (Derivative.derivativeFrom factor coefficients) inner)
        (composeCoefficients coefficients inner)) := by
  rw [Derivative.derivativeFrom_succ_eq_add]
  exact composeCoefficients_add inner _ _

/-- A leading zero coefficient makes substitution equal to the inner polynomial times the substituted tail
coefficientwise. -/
theorem composeCoefficients_zero_cons (coefficients : List Fraction.Rational)
    (inner : Basic.CoefficientPolynomial) :
    Coefficientwise.CoefficientwiseEqual (composeCoefficients (0 :: coefficients) inner)
      (Basic.mul inner (composeCoefficients coefficients inner)) := by
  change Coefficientwise.CoefficientwiseEqual
    (Basic.add (Basic.constant 0)
      (Basic.mul inner (composeCoefficients coefficients inner)))
    (Basic.mul inner (composeCoefficients coefficients inner))
  exact Coefficientwise.coefficientwise_trans
    (Coefficientwise.coefficientwise_add
      Coefficientwise.coefficientwise_constant_zero
      (Coefficientwise.coefficientwise_refl _))
    (Coefficientwise.coefficientwise_zero_add _)

/-- Substituting a shifted outer polynomial introduces the corresponding power of the inner polynomial.

The equality is coefficientwise and retains the unnormalized finite tables on both sides. -/
theorem compose_shift (outer inner : Basic.CoefficientPolynomial) : ∀ count,
    Coefficientwise.CoefficientwiseEqual (compose (Basic.shift count outer) inner)
      (Basic.mul (Basic.pow inner count) (compose outer inner))
  | 0 =>
      Coefficientwise.coefficientwise_symm
        (Coefficientwise.coefficientwise_one_mul (compose outer inner))
  | count + 1 => by
      change Coefficientwise.CoefficientwiseEqual
        (composeCoefficients
          (0 :: (List.replicate count 0 ++ outer.coefficients)) inner)
        (Basic.mul (Basic.mul (Basic.pow inner count) inner)
          (compose outer inner))
      exact Coefficientwise.coefficientwise_trans
        (composeCoefficients_zero_cons _ inner)
        (Coefficientwise.coefficientwise_trans
          (Coefficientwise.coefficientwise_mul
            (Coefficientwise.coefficientwise_refl inner)
            (Composition.compose_shift outer inner count))
          (Coefficientwise.coefficientwise_trans
            (Coefficientwise.coefficientwise_symm
              (Coefficientwise.coefficientwise_mul_assoc inner (Basic.pow inner
                count)
                (compose outer inner)))
            (Coefficientwise.coefficientwise_mul
              (Coefficientwise.coefficientwise_mul_comm inner (Basic.pow inner
                count))
              (Coefficientwise.coefficientwise_refl _))))

/-- Substituting into a monomial gives its coefficient times the corresponding power of the inner polynomial. -/
theorem compose_monomial (degree : Nat) (value : Fraction.Rational)
    (inner : Basic.CoefficientPolynomial) :
    Coefficientwise.CoefficientwiseEqual (compose (Monomial.monomial degree value)
      inner)
      (Basic.scale value (Basic.pow inner degree)) := by
  exact Coefficientwise.coefficientwise_trans
    (compose_shift (Basic.constant value) inner degree)
    (Coefficientwise.coefficientwise_trans
      (Coefficientwise.coefficientwise_mul (Coefficientwise.coefficientwise_refl
        _)
        (Coefficientwise.coefficientwise_trans
          (Coefficientwise.coefficientwise_add
            (Coefficientwise.coefficientwise_refl _)
            (Coefficientwise.coefficientwise_mul_zero inner))
          (Coefficientwise.coefficientwise_add_zero (Basic.constant value))))
      (Coefficientwise.coefficientwise_trans
        (Coefficientwise.coefficientwise_mul_comm (Basic.pow inner degree)
          (Basic.constant value))
        (Coefficientwise.coefficientwise_constant_mul value (Basic.pow inner
          degree))))

/-- Substitution of a table whose every coefficient vanishes is coefficientwise zero. -/
theorem composeCoefficients_zero_of_coefficients_zero (inner : Basic.CoefficientPolynomial) :
    ∀ coefficients,
      (∀ degree, Basic.coefficientCoefficients coefficients degree = 0) →
        Coefficientwise.CoefficientwiseEqual (composeCoefficients coefficients inner)
          Basic.zero
  | [], allZero => Coefficientwise.coefficientwise_refl Basic.zero
  | coefficient :: remaining, allZero => by
      have headZero : coefficient = 0 := allZero 0
      have tailZero :
          ∀ degree, Basic.coefficientCoefficients remaining degree = 0 := by
        intro degree
        exact allZero (degree + 1)
      subst coefficient
      exact Coefficientwise.coefficientwise_trans
        (Coefficientwise.coefficientwise_add
          Coefficientwise.coefficientwise_constant_zero
          (Coefficientwise.coefficientwise_mul
            (Coefficientwise.coefficientwise_refl inner)
            (Composition.composeCoefficients_zero_of_coefficients_zero inner
              remaining
              tailZero)))
        (Coefficientwise.coefficientwise_trans
          (Coefficientwise.coefficientwise_add
            (Coefficientwise.coefficientwise_refl Basic.zero)
            (Coefficientwise.coefficientwise_mul_zero inner))
          (Coefficientwise.coefficientwise_zero_add Basic.zero))

/-- Substitution preserves coefficientwise equality of the outer tables.

The lists may have different lengths or trailing zeros; recursion uses equality of their zero-extended coefficients. -/
theorem composeCoefficients_congr (inner : Basic.CoefficientPolynomial) :
    ∀ {left right : List Fraction.Rational},
      Coefficientwise.CoefficientwiseEqual ⟨left⟩ ⟨right⟩ →
        Coefficientwise.CoefficientwiseEqual (composeCoefficients left inner)
          (composeCoefficients right inner)
  | [], [], equal => Coefficientwise.coefficientwise_refl Basic.zero
  | [], right :: rightTail, equal => by
      have rightZero :
          ∀ degree,
            Basic.coefficientCoefficients (right :: rightTail) degree = 0 := by
        intro degree
        exact (equal degree).symm
      exact Coefficientwise.coefficientwise_symm
        (composeCoefficients_zero_of_coefficients_zero inner
          (right :: rightTail) rightZero)
  | left :: leftTail, [], equal => by
      have leftZero :
          ∀ degree,
            Basic.coefficientCoefficients (left :: leftTail) degree = 0 := by
        intro degree
        exact equal degree
      exact composeCoefficients_zero_of_coefficients_zero inner
        (left :: leftTail) leftZero
  | left :: leftTail, right :: rightTail, equal => by
      have headEqual : left = right := equal 0
      have tailEqual : Coefficientwise.CoefficientwiseEqual ⟨leftTail⟩ ⟨rightTail⟩ := by
        intro degree
        exact equal (degree + 1)
      have constantEqual :
          Coefficientwise.CoefficientwiseEqual (Basic.constant left)
            (Basic.constant right) := by
        rw [headEqual]
        exact Coefficientwise.coefficientwise_refl _
      exact Coefficientwise.coefficientwise_add
        constantEqual
        (Coefficientwise.coefficientwise_mul (Coefficientwise.coefficientwise_refl
          inner)
          (Composition.composeCoefficients_congr inner tailEqual))

/-- Equal outer coefficients give coefficientwise equal substitutions into the same inner polynomial. -/
theorem compose_congr {left right : Basic.CoefficientPolynomial}
    (equal : Coefficientwise.CoefficientwiseEqual left right) (inner :
      Basic.CoefficientPolynomial) :
    Coefficientwise.CoefficientwiseEqual (compose left inner) (compose right inner) :=
  composeCoefficients_congr inner equal

/-- Substitution into a polynomial with zero constant term preserves the outer constant coefficient. -/
theorem coefficient_compose_zero_of_inner_zero (inner : Basic.CoefficientPolynomial)
    (zeroConstant : Basic.coefficient inner 0 = 0) : ∀ outer,
    Basic.coefficient (composeCoefficients outer inner) 0 =
      Basic.coefficientCoefficients outer 0
  | [] => rfl
  | outer :: remaining => by
      rw [composeCoefficients, Basic.coefficient_add,
        Coefficientwise.coefficient_constant,
        if_pos rfl, Convolution.coefficient_mul,
          Algebra.FiniteSum.Prefix.coordinateSum_succ,
        Algebra.FiniteSum.Prefix.coordinateSum_zero, Nat.zero_sub, zeroConstant,
        Fraction.Field.zero_mul_direct,
        Fraction.Field.zero_add]
      change outer + 0 = outer
      ring1

end Purelib.Polynomial.Ascending.Rational.Composition
end
