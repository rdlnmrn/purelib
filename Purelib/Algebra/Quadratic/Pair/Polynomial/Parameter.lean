module

public import Purelib.Algebra.Quadratic.Pair.Polynomial.Derivative
public import Purelib.Polynomial.Dense.Parameter
import Purelib.Tactic.Ring

/-!
# Parameter derivatives at the original quadratic family

All parameter slopes come from the retained finite tables. The inverse-root
first, second and mixed rules keep their original radicand and the exact
polynomial numerator of each derivative. They describe formal algebraic
derivatives, separately from numerical derivative or moving-cycle evidence.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Polynomial.Expression

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic
open DensePolynomial
open Purelib.Polynomial.Dense

/-- Specialize the four original finite parameter tables without selecting another generator. -/
@[expose] def fromFamily (radicand real imaginary denominator : Parameter.Family Canonical)
    (parameter : Canonical) : Expression (Parameter.specialize radicand parameter) :=
  ⟨⟨Parameter.specialize real parameter, Parameter.specialize imaginary parameter⟩,
    Parameter.specialize denominator parameter⟩

/-- Construct the parameter derivative from the same four original finite coefficient tables. -/
@[expose] def parameterDerivative (radicand real imaginary denominator : Parameter.Family Canonical)
    (parameter : Canonical) : Expression (Parameter.specialize radicand parameter) :=
  (fromFamily radicand real imaginary denominator parameter).directionalDerivative
    (Parameter.specialize (Parameter.derivative radicand) parameter)
    (Parameter.specialize (Parameter.derivative real) parameter)
    (Parameter.specialize (Parameter.derivative imaginary) parameter)
    (Parameter.specialize (Parameter.derivative denominator) parameter)

/-- Retain the exact first directional derivative of the original inverse root. -/
@[expose] def inverseRootDerivative (radicand slope : Coefficients) : Expression radicand :=
  ⟨⟨0, -slope⟩, (Power.power radicand 2).scale 2⟩

/-- The original inverse-root directional construction certifies the computed first derivative. -/
theorem directional_inverseRoot (radicand slope : Coefficients) :
    ((inverseRoot radicand).directionalDerivative slope 0 0 slope).Equal
      (inverseRootDerivative radicand slope) := by
  apply equal_of_cross_eval
  · intro point
    simp only [directionalDerivative, inverseRoot, oddReciprocal, inverseRootDerivative,
      eval_mul, eval_sub, eval_scale, eval_zero]
    ring1
  · intro point
    simp only [directionalDerivative, inverseRoot, oddReciprocal, inverseRootDerivative,
      eval_mul, eval_add, eval_sub, eval_neg, eval_scale, eval_zero, eval_constant, Power.eval_power,
      pow_zero, pow_succ]
    ring1

/-- Retain the exact second directional derivative numerator of the original inverse root. -/
@[expose] def inverseRootSecondDerivative (radicand slope secondSlope : Coefficients) : Expression radicand :=
  ⟨⟨0, (slope * slope).scale 3 - (radicand * secondSlope).scale 2⟩,
    (Power.power radicand 3).scale 4⟩

/-- The second inverse-root derivative is derived by the same retained quotient and generator rules. -/
theorem directional_inverseRootDerivative (radicand slope secondSlope : Coefficients) :
    ((inverseRootDerivative radicand slope).directionalDerivative slope 0 (-secondSlope)
      ((radicand * slope).scale 4)).Equal (inverseRootSecondDerivative radicand slope secondSlope) := by
  apply equal_of_cross_eval
  · intro point
    simp only [directionalDerivative, inverseRootDerivative, inverseRootSecondDerivative,
      eval_mul, eval_sub, eval_scale, eval_zero]
    ring1
  · intro point
    simp only [directionalDerivative, inverseRootDerivative, inverseRootSecondDerivative,
      eval_mul, eval_add, eval_sub, eval_neg, eval_scale, Power.eval_power, pow_succ, pow_zero]
    ring1

/-- Retain the original inverse root's exact mixed directional numerator. -/
@[expose] def inverseRootMixedDerivative (radicand leftSlope rightSlope mixedSlope : Coefficients) :
    Expression radicand :=
  ⟨⟨0, (leftSlope * rightSlope).scale 3 - (radicand * mixedSlope).scale 2⟩,
    (Power.power radicand 3).scale 4⟩

/-- Differentiate the first directional inverse-root derivative in another retained direction. -/
theorem mixed_inverseRootDerivative (radicand leftSlope rightSlope mixedSlope : Coefficients) :
    ((inverseRootDerivative radicand rightSlope).directionalDerivative leftSlope 0 (-mixedSlope)
      ((radicand * leftSlope).scale 4)).Equal
        (inverseRootMixedDerivative radicand leftSlope rightSlope mixedSlope) := by
  apply equal_of_cross_eval
  · intro point
    simp only [directionalDerivative, inverseRootDerivative, inverseRootMixedDerivative,
      eval_mul, eval_sub, eval_scale, eval_zero]
    ring1
  · intro point
    simp only [directionalDerivative, inverseRootDerivative, inverseRootMixedDerivative,
      eval_mul, eval_add, eval_sub, eval_neg, eval_scale, Power.eval_power, pow_succ, pow_zero]
    ring1

/-- Exact mixed inverse-root coefficients commute when their original mixed coefficient slope is shared. -/
theorem inverseRootMixedDerivative_comm (radicand leftSlope rightSlope mixedSlope : Coefficients) :
    (inverseRootMixedDerivative radicand leftSlope rightSlope mixedSlope).Equal
      (inverseRootMixedDerivative radicand rightSlope leftSlope mixedSlope) := by
  apply equal_of_cross_eval
  · intro point
    rfl
  · intro point
    simp only [inverseRootMixedDerivative, eval_mul, eval_sub, eval_scale]
    ring1

/-- Compute the original finite family's inverse-root first parameter derivative. -/
@[expose] def parameterInverseRootDerivative (family : Parameter.Family Canonical) (parameter : Canonical) :
    Expression (Parameter.specialize family parameter) :=
  inverseRootDerivative (Parameter.specialize family parameter)
    (Parameter.specialize (Parameter.derivative family) parameter)

/-- Compute the original finite family's inverse-root second parameter derivative. -/
@[expose] def parameterInverseRootSecondDerivative (family : Parameter.Family Canonical) (parameter : Canonical) :
    Expression (Parameter.specialize family parameter) :=
  inverseRootSecondDerivative (Parameter.specialize family parameter)
    (Parameter.specialize (Parameter.derivative family) parameter)
    (Parameter.specialize (Parameter.derivative (Parameter.derivative family)) parameter)

/-- Compute the second coefficient slopes of a directional quadratic quotient.

The first direction differentiates the retained radicand, numerator and
original denominator. The second step uses the displayed mixed coefficient
slopes in the same product and quotient rules. -/
@[expose] def mixedDirectionalDerivative {radicand : Coefficients} (value : Expression radicand)
    (leftParameter rightParameter mixedParameter : Coefficients)
    (leftNumerator rightNumerator mixedNumerator : Pair Coefficients (-radicand))
    (leftDenominator rightDenominator mixedDenominator : Coefficients) : Expression radicand :=
  let right := value.directionalDerivative rightParameter rightNumerator.re rightNumerator.im rightDenominator
  let real := (leftParameter *
      (rightNumerator.re * value.denominator - value.numerator.re * rightDenominator)).scale 2 +
    (radicand * (mixedNumerator.re * value.denominator + rightNumerator.re * leftDenominator -
      leftNumerator.re * rightDenominator - value.numerator.re * mixedDenominator)).scale 2
  let imaginary := (leftParameter *
      (rightNumerator.im * value.denominator - value.numerator.im * rightDenominator)).scale 2 +
    (radicand * (mixedNumerator.im * value.denominator + rightNumerator.im * leftDenominator -
      leftNumerator.im * rightDenominator - value.numerator.im * mixedDenominator)).scale 2 +
    mixedParameter * value.numerator.im * value.denominator +
    rightParameter * leftNumerator.im * value.denominator +
    rightParameter * value.numerator.im * leftDenominator
  let denominator := (leftParameter * (value.denominator * value.denominator)).scale 2 +
    (radicand * value.denominator * leftDenominator).scale 4
  right.directionalDerivative leftParameter real imaginary denominator

/-- The finite quotient and generator rules give commuting mixed coefficient derivatives.

The original expression and the mixed coefficient slope are shared. Swapping
only the two first directions yields an exact zero-coefficient certificate. -/
theorem mixedDirectionalDerivative_comm {radicand : Coefficients} (value : Expression radicand)
    (leftParameter rightParameter mixedParameter : Coefficients)
    (leftNumerator rightNumerator mixedNumerator : Pair Coefficients (-radicand))
    (leftDenominator rightDenominator mixedDenominator : Coefficients) :
    (mixedDirectionalDerivative value leftParameter rightParameter mixedParameter
      leftNumerator rightNumerator mixedNumerator leftDenominator rightDenominator mixedDenominator).Equal
    (mixedDirectionalDerivative value rightParameter leftParameter mixedParameter
      rightNumerator leftNumerator mixedNumerator rightDenominator leftDenominator mixedDenominator) := by
  apply equal_of_cross_eval
  · intro point
    simp only [mixedDirectionalDerivative, directionalDerivative, eval_mul, eval_add, eval_sub, eval_scale]
    ring1
  · intro point
    simp only [mixedDirectionalDerivative, directionalDerivative, eval_mul, eval_add, eval_sub, eval_scale]
    ring1

/-- The original automatic spatial derivative realizes the computed mixed directional coefficients. -/
theorem derivative_directionalDerivative {radicand : Coefficients} (value : Expression radicand)
    (parameterSlope realSlope imaginarySlope denominatorSlope : Coefficients) :
    (value.directionalDerivative parameterSlope realSlope imaginarySlope denominatorSlope).derivative.Equal
      (mixedDirectionalDerivative value (Derivative.derivative radicand) parameterSlope
        (Derivative.derivative parameterSlope)
        ⟨Derivative.derivative value.numerator.re, Derivative.derivative value.numerator.im⟩
        ⟨realSlope, imaginarySlope⟩ ⟨Derivative.derivative realSlope, Derivative.derivative imaginarySlope⟩
        (Derivative.derivative value.denominator) denominatorSlope (Derivative.derivative denominatorSlope)) := by
  apply equal_of_cross_eval
  · intro point
    simp only [derivative, mixedDirectionalDerivative, directionalDerivative,
      Derivative.eval_derivative_mul, Derivative.eval_derivative_sub,
      Derivative.eval_derivative_scale, eval_mul, eval_add, eval_sub, eval_scale]
    ring1
  · intro point
    simp only [derivative, mixedDirectionalDerivative, directionalDerivative,
      Derivative.eval_derivative_mul, Derivative.eval_derivative_sub, Derivative.eval_derivative_add,
      Derivative.eval_derivative_scale, eval_mul, eval_add, eval_sub, eval_scale]
    ring1

/-- Construct the original family's mixed spatial and parameter derivative from its retained coefficient tables. -/
@[expose] def mixedFamilyDerivative (radicand real imaginary denominator : Parameter.Family Canonical)
    (parameter : Canonical) : Expression (Parameter.specialize radicand parameter) :=
  let value := fromFamily radicand real imaginary denominator parameter
  let parameterSlope := Parameter.specialize (Parameter.derivative radicand) parameter
  let realSlope := Parameter.specialize (Parameter.derivative real) parameter
  let imaginarySlope := Parameter.specialize (Parameter.derivative imaginary) parameter
  let denominatorSlope := Parameter.specialize (Parameter.derivative denominator) parameter
  mixedDirectionalDerivative value (Derivative.derivative (Parameter.specialize radicand parameter)) parameterSlope
    (Derivative.derivative parameterSlope)
    ⟨Derivative.derivative value.numerator.re, Derivative.derivative value.numerator.im⟩
    ⟨realSlope, imaginarySlope⟩ ⟨Derivative.derivative realSlope, Derivative.derivative imaginarySlope⟩
    (Derivative.derivative value.denominator) denominatorSlope (Derivative.derivative denominatorSlope)

/-- The constructed mixed family expression is the exact derivative of the original parameter derivative. -/
theorem derivative_parameterDerivative (radicand real imaginary denominator : Parameter.Family Canonical)
    (parameter : Canonical) :
    (parameterDerivative radicand real imaginary denominator parameter).derivative.Equal
      (mixedFamilyDerivative radicand real imaginary denominator parameter) :=
  derivative_directionalDerivative (fromFamily radicand real imaginary denominator parameter)
    (Parameter.specialize (Parameter.derivative radicand) parameter)
    (Parameter.specialize (Parameter.derivative real) parameter)
    (Parameter.specialize (Parameter.derivative imaginary) parameter)
    (Parameter.specialize (Parameter.derivative denominator) parameter)

end Purelib.Algebra.Quadratic.Pair.Polynomial.Expression
