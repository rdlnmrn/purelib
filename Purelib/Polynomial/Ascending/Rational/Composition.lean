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
  Ascending.Rational.Basic.CoefficientPolynomial) :
    Ascending.Rational.Basic.CoefficientPolynomial :=
  match outer with
  | [] => Ascending.Rational.Basic.zero
  | coefficient :: remaining =>
      Ascending.Rational.Basic.add (Ascending.Rational.Basic.constant coefficient)
        (Ascending.Rational.Basic.mul inner (Purelib.Polynomial.Ascending.Rational.Composition.composeCoefficients
          remaining inner))

/-- Substitute the inner polynomial into the retained outer polynomial.

The nominal outer record supplies its exact coefficient list to the finite
Horner procedure. The inner record is retained through each recursive product. -/
@[expose] def compose (outer inner : Ascending.Rational.Basic.CoefficientPolynomial) :
  Ascending.Rational.Basic.CoefficientPolynomial :=
  composeCoefficients outer.coefficients inner

/-- Substitution distributes over padded coefficient-list addition coefficientwise. -/
theorem composeCoefficients_add (inner : Ascending.Rational.Basic.CoefficientPolynomial) : ∀ left right,
    Ascending.Rational.Coefficientwise.CoefficientwiseEqual
      (composeCoefficients (Ascending.Rational.Basic.addCoefficients left right) inner)
      (Ascending.Rational.Basic.add (composeCoefficients left inner)
        (composeCoefficients right inner))
  | [], right =>
      Ascending.Rational.Coefficientwise.coefficientwise_symm
        (Ascending.Rational.Coefficientwise.coefficientwise_zero_add (composeCoefficients right inner))
  | left :: leftTail, [] => by
      rw [Ascending.Rational.Basic.addCoefficients_nil_right]
      exact Ascending.Rational.Coefficientwise.coefficientwise_symm
        (Ascending.Rational.Coefficientwise.coefficientwise_add_zero
          (composeCoefficients (left :: leftTail) inner))
  | left :: leftTail, right :: rightTail => by
      change Ascending.Rational.Coefficientwise.CoefficientwiseEqual
        (Ascending.Rational.Basic.add (Ascending.Rational.Basic.constant (left + right))
          (Ascending.Rational.Basic.mul inner
            (composeCoefficients
              (Ascending.Rational.Basic.addCoefficients leftTail rightTail) inner)))
        (Ascending.Rational.Basic.add
          (Ascending.Rational.Basic.add (Ascending.Rational.Basic.constant left)
            (Ascending.Rational.Basic.mul inner (composeCoefficients leftTail inner)))
          (Ascending.Rational.Basic.add (Ascending.Rational.Basic.constant right)
            (Ascending.Rational.Basic.mul inner (composeCoefficients rightTail inner))))
      exact Ascending.Rational.Coefficientwise.coefficientwise_trans
        (Ascending.Rational.Coefficientwise.coefficientwise_add
          (Ascending.Rational.Coefficientwise.coefficientwise_constant_add left right)
          (Ascending.Rational.Coefficientwise.coefficientwise_refl _))
        (Ascending.Rational.Coefficientwise.coefficientwise_trans
          (Ascending.Rational.Coefficientwise.coefficientwise_add
            (Ascending.Rational.Coefficientwise.coefficientwise_refl _)
            (Ascending.Rational.Coefficientwise.coefficientwise_mul
              (Ascending.Rational.Coefficientwise.coefficientwise_refl inner)
              (Purelib.Polynomial.Ascending.Rational.Composition.composeCoefficients_add inner leftTail rightTail)))
          (Ascending.Rational.Coefficientwise.coefficientwise_trans
            (Ascending.Rational.Coefficientwise.coefficientwise_add
              (Ascending.Rational.Coefficientwise.coefficientwise_refl _)
              (Ascending.Rational.Coefficientwise.coefficientwise_mul_add inner
                (composeCoefficients leftTail inner)
                (composeCoefficients rightTail inner)))
            (Ascending.Rational.Coefficientwise.coefficientwise_add_rearrange
              (Ascending.Rational.Basic.constant left) (Ascending.Rational.Basic.constant right)
              (Ascending.Rational.Basic.mul inner (composeCoefficients leftTail inner))
              (Ascending.Rational.Basic.mul inner (composeCoefficients rightTail inner)))))

/-- Substitution distributes over addition of the outer polynomials coefficientwise. -/
theorem compose_add (left right inner : Ascending.Rational.Basic.CoefficientPolynomial) :
    Ascending.Rational.Coefficientwise.CoefficientwiseEqual (compose (Ascending.Rational.Basic.add left right) inner)
      (Ascending.Rational.Basic.add (compose left inner) (compose right inner)) :=
  composeCoefficients_add inner left.coefficients right.coefficients

/-- Substituting a table with all degree weights raised by one adds the unweighted substitution. -/
theorem composeCoefficients_derivativeFrom_succ (factor : Nat)
    (coefficients : List Fraction.Rational) (inner : Ascending.Rational.Basic.CoefficientPolynomial) :
    Ascending.Rational.Coefficientwise.CoefficientwiseEqual
      (composeCoefficients (Ascending.Rational.Derivative.derivativeFrom (factor + 1) coefficients) inner)
      (Ascending.Rational.Basic.add
        (composeCoefficients (Ascending.Rational.Derivative.derivativeFrom factor coefficients) inner)
        (composeCoefficients coefficients inner)) := by
  rw [Ascending.Rational.Derivative.derivativeFrom_succ_eq_add]
  exact composeCoefficients_add inner _ _

/-- A leading zero coefficient makes substitution equal to the inner polynomial times the substituted tail
coefficientwise. -/
theorem composeCoefficients_zero_cons (coefficients : List Fraction.Rational)
    (inner : Ascending.Rational.Basic.CoefficientPolynomial) :
    Ascending.Rational.Coefficientwise.CoefficientwiseEqual (composeCoefficients (0 :: coefficients) inner)
      (Ascending.Rational.Basic.mul inner (composeCoefficients coefficients inner)) := by
  change Ascending.Rational.Coefficientwise.CoefficientwiseEqual
    (Ascending.Rational.Basic.add (Ascending.Rational.Basic.constant 0)
      (Ascending.Rational.Basic.mul inner (composeCoefficients coefficients inner)))
    (Ascending.Rational.Basic.mul inner (composeCoefficients coefficients inner))
  exact Ascending.Rational.Coefficientwise.coefficientwise_trans
    (Ascending.Rational.Coefficientwise.coefficientwise_add
      Ascending.Rational.Coefficientwise.coefficientwise_constant_zero
      (Ascending.Rational.Coefficientwise.coefficientwise_refl _))
    (Ascending.Rational.Coefficientwise.coefficientwise_zero_add _)

/-- Substituting a shifted outer polynomial introduces the corresponding power of the inner polynomial.

The equality is coefficientwise and retains the unnormalized finite tables on both sides. -/
theorem compose_shift (outer inner : Ascending.Rational.Basic.CoefficientPolynomial) : ∀ count,
    Ascending.Rational.Coefficientwise.CoefficientwiseEqual (compose (Ascending.Rational.Basic.shift count outer) inner)
      (Ascending.Rational.Basic.mul (Ascending.Rational.Basic.pow inner count) (compose outer inner))
  | 0 =>
      Ascending.Rational.Coefficientwise.coefficientwise_symm
        (Ascending.Rational.Coefficientwise.coefficientwise_one_mul (compose outer inner))
  | count + 1 => by
      change Ascending.Rational.Coefficientwise.CoefficientwiseEqual
        (composeCoefficients
          (0 :: (List.replicate count 0 ++ outer.coefficients)) inner)
        (Ascending.Rational.Basic.mul (Ascending.Rational.Basic.mul (Ascending.Rational.Basic.pow inner count) inner)
          (compose outer inner))
      exact Ascending.Rational.Coefficientwise.coefficientwise_trans
        (composeCoefficients_zero_cons _ inner)
        (Ascending.Rational.Coefficientwise.coefficientwise_trans
          (Ascending.Rational.Coefficientwise.coefficientwise_mul
            (Ascending.Rational.Coefficientwise.coefficientwise_refl inner)
            (Purelib.Polynomial.Ascending.Rational.Composition.compose_shift outer inner count))
          (Ascending.Rational.Coefficientwise.coefficientwise_trans
            (Ascending.Rational.Coefficientwise.coefficientwise_symm
              (Ascending.Rational.Coefficientwise.coefficientwise_mul_assoc inner (Ascending.Rational.Basic.pow inner
                count)
                (compose outer inner)))
            (Ascending.Rational.Coefficientwise.coefficientwise_mul
              (Ascending.Rational.Coefficientwise.coefficientwise_mul_comm inner (Ascending.Rational.Basic.pow inner
                count))
              (Ascending.Rational.Coefficientwise.coefficientwise_refl _))))

/-- Substituting into a monomial gives its coefficient times the corresponding power of the inner polynomial. -/
theorem compose_monomial (degree : Nat) (value : Fraction.Rational)
    (inner : Ascending.Rational.Basic.CoefficientPolynomial) :
    Ascending.Rational.Coefficientwise.CoefficientwiseEqual (compose (Ascending.Rational.Monomial.monomial degree value)
      inner)
      (Ascending.Rational.Basic.scale value (Ascending.Rational.Basic.pow inner degree)) := by
  exact Ascending.Rational.Coefficientwise.coefficientwise_trans
    (compose_shift (Ascending.Rational.Basic.constant value) inner degree)
    (Ascending.Rational.Coefficientwise.coefficientwise_trans
      (Ascending.Rational.Coefficientwise.coefficientwise_mul (Ascending.Rational.Coefficientwise.coefficientwise_refl
        _)
        (Ascending.Rational.Coefficientwise.coefficientwise_trans
          (Ascending.Rational.Coefficientwise.coefficientwise_add
            (Ascending.Rational.Coefficientwise.coefficientwise_refl _)
            (Ascending.Rational.Coefficientwise.coefficientwise_mul_zero inner))
          (Ascending.Rational.Coefficientwise.coefficientwise_add_zero (Ascending.Rational.Basic.constant value))))
      (Ascending.Rational.Coefficientwise.coefficientwise_trans
        (Ascending.Rational.Coefficientwise.coefficientwise_mul_comm (Ascending.Rational.Basic.pow inner degree)
          (Ascending.Rational.Basic.constant value))
        (Ascending.Rational.Coefficientwise.coefficientwise_constant_mul value (Ascending.Rational.Basic.pow inner
          degree))))

/-- Substitution of a table whose every coefficient vanishes is coefficientwise zero. -/
theorem composeCoefficients_zero_of_coefficients_zero (inner : Ascending.Rational.Basic.CoefficientPolynomial) :
    ∀ coefficients,
      (∀ degree, Ascending.Rational.Basic.coefficientCoefficients coefficients degree = 0) →
        Ascending.Rational.Coefficientwise.CoefficientwiseEqual (composeCoefficients coefficients inner)
          Ascending.Rational.Basic.zero
  | [], allZero => Ascending.Rational.Coefficientwise.coefficientwise_refl Ascending.Rational.Basic.zero
  | coefficient :: remaining, allZero => by
      have headZero : coefficient = 0 := allZero 0
      have tailZero :
          ∀ degree, Ascending.Rational.Basic.coefficientCoefficients remaining degree = 0 := by
        intro degree
        exact allZero (degree + 1)
      subst coefficient
      exact Ascending.Rational.Coefficientwise.coefficientwise_trans
        (Ascending.Rational.Coefficientwise.coefficientwise_add
          Ascending.Rational.Coefficientwise.coefficientwise_constant_zero
          (Ascending.Rational.Coefficientwise.coefficientwise_mul
            (Ascending.Rational.Coefficientwise.coefficientwise_refl inner)
            (Purelib.Polynomial.Ascending.Rational.Composition.composeCoefficients_zero_of_coefficients_zero inner
              remaining
              tailZero)))
        (Ascending.Rational.Coefficientwise.coefficientwise_trans
          (Ascending.Rational.Coefficientwise.coefficientwise_add
            (Ascending.Rational.Coefficientwise.coefficientwise_refl Ascending.Rational.Basic.zero)
            (Ascending.Rational.Coefficientwise.coefficientwise_mul_zero inner))
          (Ascending.Rational.Coefficientwise.coefficientwise_zero_add Ascending.Rational.Basic.zero))

/-- Substitution preserves coefficientwise equality of the outer tables.

The lists may have different lengths or trailing zeros; recursion uses equality of their zero-extended coefficients. -/
theorem composeCoefficients_congr (inner : Ascending.Rational.Basic.CoefficientPolynomial) :
    ∀ {left right : List Fraction.Rational},
      Ascending.Rational.Coefficientwise.CoefficientwiseEqual ⟨left⟩ ⟨right⟩ →
        Ascending.Rational.Coefficientwise.CoefficientwiseEqual (composeCoefficients left inner)
          (composeCoefficients right inner)
  | [], [], equal => Ascending.Rational.Coefficientwise.coefficientwise_refl Ascending.Rational.Basic.zero
  | [], right :: rightTail, equal => by
      have rightZero :
          ∀ degree,
            Ascending.Rational.Basic.coefficientCoefficients (right :: rightTail) degree = 0 := by
        intro degree
        exact (equal degree).symm
      exact Ascending.Rational.Coefficientwise.coefficientwise_symm
        (composeCoefficients_zero_of_coefficients_zero inner
          (right :: rightTail) rightZero)
  | left :: leftTail, [], equal => by
      have leftZero :
          ∀ degree,
            Ascending.Rational.Basic.coefficientCoefficients (left :: leftTail) degree = 0 := by
        intro degree
        exact equal degree
      exact composeCoefficients_zero_of_coefficients_zero inner
        (left :: leftTail) leftZero
  | left :: leftTail, right :: rightTail, equal => by
      have headEqual : left = right := equal 0
      have tailEqual : Ascending.Rational.Coefficientwise.CoefficientwiseEqual ⟨leftTail⟩ ⟨rightTail⟩ := by
        intro degree
        exact equal (degree + 1)
      have constantEqual :
          Ascending.Rational.Coefficientwise.CoefficientwiseEqual (Ascending.Rational.Basic.constant left)
            (Ascending.Rational.Basic.constant right) := by
        rw [headEqual]
        exact Ascending.Rational.Coefficientwise.coefficientwise_refl _
      exact Ascending.Rational.Coefficientwise.coefficientwise_add
        constantEqual
        (Ascending.Rational.Coefficientwise.coefficientwise_mul (Ascending.Rational.Coefficientwise.coefficientwise_refl
          inner)
          (Purelib.Polynomial.Ascending.Rational.Composition.composeCoefficients_congr inner tailEqual))

/-- Equal outer coefficients give coefficientwise equal substitutions into the same inner polynomial. -/
theorem compose_congr {left right : Ascending.Rational.Basic.CoefficientPolynomial}
    (equal : Ascending.Rational.Coefficientwise.CoefficientwiseEqual left right) (inner :
      Ascending.Rational.Basic.CoefficientPolynomial) :
    Ascending.Rational.Coefficientwise.CoefficientwiseEqual (compose left inner) (compose right inner) :=
  composeCoefficients_congr inner equal

/-- Substitution into a polynomial with zero constant term preserves the outer constant coefficient. -/
theorem coefficient_compose_zero_of_inner_zero (inner : Ascending.Rational.Basic.CoefficientPolynomial)
    (zeroConstant : Ascending.Rational.Basic.coefficient inner 0 = 0) : ∀ outer,
    Ascending.Rational.Basic.coefficient (composeCoefficients outer inner) 0 =
      Ascending.Rational.Basic.coefficientCoefficients outer 0
  | [] => rfl
  | outer :: remaining => by
      rw [composeCoefficients, Ascending.Rational.Basic.coefficient_add,
        Ascending.Rational.Coefficientwise.coefficient_constant,
        if_pos rfl, Purelib.Polynomial.Ascending.Rational.Convolution.coefficient_mul,
          Purelib.Algebra.FiniteSum.Prefix.coordinateSum_succ,
        Purelib.Algebra.FiniteSum.Prefix.coordinateSum_zero, Nat.zero_sub, zeroConstant,
        Purelib.Data.Rat.Fraction.Field.zero_mul_direct,
        Purelib.Data.Rat.Fraction.Field.zero_add]
      change outer + 0 = outer
      ring1

end Purelib.Polynomial.Ascending.Rational.Composition
end
