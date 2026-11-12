module

public import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Polynomial.Dense.Power
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-!
# Exact differentiation of quadratic polynomial expressions

The formal coordinate retains its original radicand and satisfies `Y²=P`.
Differentiation uses `Y'=P'Y/(2P)`, with the new denominator retaining the
original denominator and the regular-chart guard. All displayed identities
produce finite zero-coefficient certificates.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Polynomial.Expression

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Polynomial.Dense.Basic
open DensePolynomial
open Purelib.Polynomial.Dense

variable {radicand : Coefficients}

/-- Compute the directional quotient and generator rule from four retained coefficient slopes.

The supplied polynomial tables are the directional slopes of the original
radicand, two numerator coordinates and denominator. The resulting denominator
is `2P C²`, preserving the original quotient guard; the spatial and parameter
constructors compute the slopes from their retained sources.
-/
@[expose] def directionalDerivative (value : Expression radicand)
    (parameterSlope realSlope imaginarySlope denominatorSlope : Coefficients) : Expression radicand :=
  let twiceParameter := radicand.scale 2
  ⟨⟨twiceParameter * (realSlope * value.denominator - value.numerator.re * denominatorSlope),
      twiceParameter * (imaginarySlope * value.denominator - value.numerator.im * denominatorSlope) +
        parameterSlope * value.numerator.im * value.denominator⟩,
    twiceParameter * (value.denominator * value.denominator)⟩

/-- Differentiate all original spatial coefficient tables by their finite Horner algorithms. -/
@[expose] def derivative (value : Expression radicand) : Expression radicand :=
  directionalDerivative value (Derivative.derivative radicand)
    (Derivative.derivative value.numerator.re) (Derivative.derivative value.numerator.im)
    (Derivative.derivative value.denominator)

/-- The derivative retains exactly the nonvanishing source denominator and regular radicand guards. -/
theorem defined_derivative (value : Expression radicand) (point : Canonical)
    (defined : value.Defined point) (regular : radicand.eval point ≠ 0) :
    value.derivative.Defined point := by
  change (radicand.scale 2 * (value.denominator * value.denominator)).eval point ≠ 0
  rewrite [eval_mul, eval_scale, eval_mul]
  exact ExplicitField.mul_ne_zero
    (ExplicitField.mul_ne_zero (by decide : (2 : Canonical) ≠ 0) regular)
    (ExplicitField.mul_ne_zero defined defined)

/-- Exact differentiation preserves addition after clearing the retained denominators. -/
theorem derivative_add (left right : Expression radicand) :
    (left.add right).derivative.Equal (left.derivative.add right.derivative) := by
  apply equal_of_cross_eval
  · intro point
    simp only [derivative, directionalDerivative, add, Pair.scale, Pair.add_re,
      eval_mul, eval_add, eval_sub, eval_scale,
      Derivative.eval_derivative_add, Derivative.eval_derivative_mul]
    ring1
  · intro point
    simp only [derivative, directionalDerivative, add, Pair.scale, Pair.add_im,
      eval_mul, eval_add, eval_sub, eval_scale,
      Derivative.eval_derivative_add, Derivative.eval_derivative_mul]
    ring1

/-- Exact differentiation preserves negation without changing either original denominator. -/
theorem derivative_neg (value : Expression radicand) :
    value.neg.derivative.Equal value.derivative.neg := by
  apply equal_of_cross_eval
  · intro point
    simp only [derivative, directionalDerivative, neg, Pair.neg_re, eval_mul, eval_neg, eval_sub, eval_scale,
      Derivative.eval_derivative_neg]
    ring1
  · intro point
    simp only [derivative, directionalDerivative, neg, Pair.neg_im, eval_mul, eval_neg, eval_add, eval_sub, eval_scale,
      Derivative.eval_derivative_neg]
    ring1

/-- The finite product rule retains the same radicand, generator and both original quotient owners. -/
theorem derivative_mul (left right : Expression radicand) :
    (left.mul right).derivative.Equal
      ((left.derivative.mul right).add (left.mul right.derivative)) := by
  apply equal_of_cross_eval
  · intro point
    simp only [derivative, directionalDerivative, mul, add, Pair.scale, Pair.add_re, Pair.mul_re, Pair.mul_im,
      eval_mul, eval_add, eval_sub, eval_neg, eval_scale,
      Derivative.eval_derivative_sub,
      Derivative.eval_derivative_neg, Derivative.eval_derivative_mul]
    ring1
  · intro point
    simp only [derivative, directionalDerivative, mul, add, Pair.scale, Pair.add_im, Pair.mul_re, Pair.mul_im,
      eval_mul, eval_add, eval_sub, eval_scale,
      Derivative.eval_derivative_add, Derivative.eval_derivative_mul]
    ring1

/-- A polynomial scalar differentiates by the original finite Horner derivative. -/
theorem derivative_scalar (coefficient : Coefficients) :
    (scalar (radicand := radicand) coefficient).derivative.Equal
      (scalar (Derivative.derivative coefficient)) := by
  apply equal_of_cross_eval
  · intro point
    simp only [derivative, directionalDerivative, scalar, Pair.scalar_re, Pair.scalar_im,
      eval_mul, eval_sub, eval_scale,
      eval_constant, Power.eval_derivative_constant]
    ring1
  · intro point
    simp only [derivative, directionalDerivative, scalar, Pair.scalar_re, Pair.scalar_im,
      eval_mul, eval_add, eval_sub, eval_scale,
      eval_zero, eval_constant, Power.eval_derivative_constant, Power.eval_derivative_zero]
    ring1

/-- Polynomial scaling differentiates by the same finite product rule and original quotient guards. -/
theorem derivative_scale (factor : Coefficients) (value : Expression radicand) :
    (value.scale factor).derivative.Equal
      ((value.derivative.scale factor).add (value.scale (Derivative.derivative factor))) := by
  apply equal_of_cross_eval
  · intro point
    simp only [-eq_self, -iff_self, derivative, directionalDerivative, scale, add, Pair.scale, Pair.add_re,
      eval_mul, eval_add, eval_sub, eval_scale, Derivative.eval_derivative_mul]
    ring1
  · intro point
    simp only [-eq_self, -iff_self, derivative, directionalDerivative, scale, add, Pair.scale, Pair.add_im,
      eval_mul, eval_add, eval_sub, eval_scale, Derivative.eval_derivative_mul]
    ring1

/-- The original generator follows the same quotient rule in any retained polynomial direction. -/
theorem directional_generator (radicand slope : Coefficients) :
    ((generator (radicand := radicand)).directionalDerivative slope 0 0 0).Equal
      ⟨⟨0, slope⟩, radicand.scale 2⟩ := by
  apply equal_of_cross_eval
  · intro point
    simp only [-eq_self, -iff_self, directionalDerivative, generator, eval_mul, eval_sub,
      eval_scale, eval_zero, eval_constant]
    ring1
  · intro point
    simp only [-eq_self, -iff_self, directionalDerivative, generator, eval_mul, eval_add,
      eval_sub, eval_scale, eval_zero, eval_constant]
    ring1

/-- Differentiation preserves the original defining relation `Y²=P` as a finite coefficient identity. -/
theorem derivative_generator_relation :
    (((generator (radicand := radicand)).mul generator).sub (scalar radicand)).derivative.Equal zero := by
  apply equal_of_cross_eval
  · intro point
    simp only [-eq_self, -iff_self, derivative, directionalDerivative, sub, add, neg, mul,
      scalar, generator, zero, Pair.scale, Pair.add_re, Pair.neg_re, Pair.mul_re, Pair.scalar_re,
      eval_mul, eval_add, eval_sub, eval_neg, eval_scale, eval_constant, eval_zero,
      Derivative.eval_derivative_mul, Derivative.eval_derivative_add, Derivative.eval_derivative_sub,
      Derivative.eval_derivative_neg, Power.eval_derivative_constant, Power.eval_derivative_zero]
    ring1
  · intro point
    simp only [-eq_self, -iff_self, derivative, directionalDerivative, sub, add, neg, mul,
      scalar, generator, zero, Pair.scale, Pair.add_im, Pair.neg_im, Pair.mul_im, Pair.scalar_im,
      eval_mul, eval_add, eval_sub, eval_neg, eval_scale, eval_constant, eval_zero,
      Derivative.eval_derivative_mul, Derivative.eval_derivative_add, Derivative.eval_derivative_neg,
      Power.eval_derivative_constant, Power.eval_derivative_zero]
    ring1

/-- Retain the generator coefficient of its regular-chart derivative `P'Y/(2P)`. -/
@[expose] def generatorDerivative (radicand : Coefficients) : Expression radicand :=
  ⟨⟨0, Derivative.derivative radicand⟩, radicand.scale 2⟩

/-- The formal generator's derivative is constructed from the original radicand coefficients. -/
theorem derivative_generator :
    (generator (radicand := radicand)).derivative.Equal (generatorDerivative radicand) := by
  apply equal_of_cross_eval
  · intro point
    simp only [derivative, directionalDerivative, generator, generatorDerivative,
      eval_mul, eval_sub, eval_scale, eval_zero,
      eval_constant, Power.eval_derivative_zero]
    ring1
  · intro point
    simp only [derivative, directionalDerivative, generator, generatorDerivative,
      eval_mul, eval_add, eval_sub, eval_scale,
      eval_constant, Power.eval_derivative_constant]
    ring1

/-- Reduce an odd reciprocal sheet power to the same original quadratic pair.

The expression is `R Y/P^(n+1)`, representing `R/Y^(2n+1)` only where
the original radicand is nonzero. No scalar inverse or root selection occurs.
-/
@[expose] def oddReciprocal (radicand : Coefficients) (pairs : Nat) (numerator : Coefficients) :
    Expression radicand :=
  ⟨⟨0, numerator⟩, Power.power radicand (pairs + 1)⟩

/-- The inverse-root expression uses the original generator and radicand. -/
@[expose] def inverseRoot (radicand : Coefficients) : Expression radicand :=
  oddReciprocal radicand 0 (constant 1)

/-- A finite Bézout identity gives polynomial coefficients for the original generator and its differential.

The exact coordinate identity is `R/Y = (RL)Y + (2RM)Y'` when
`LF+MF'=1`. Interpreted as a one-form presentation, its two polynomial
coefficients multiply `dx` and `dY`; this coefficient theorem alone asserts
neither quotient admission at a branch point nor an analytic chart bridge.
-/
theorem oddReciprocal_generator_identity (radicand numerator left right : Coefficients)
    (identity : ∀ point : Canonical,
      1 = left.eval point * radicand.eval point +
        right.eval point * (Derivative.derivative radicand).eval point) :
    (oddReciprocal radicand 0 numerator).Equal
      (((generator (radicand := radicand)).scale (numerator * left)).add
        ((generatorDerivative radicand).scale ((numerator * right).scale 2))) := by
  apply equal_of_cross_eval
  · intro point
    simp only [-eq_self, -iff_self, oddReciprocal, generator, generatorDerivative, scale, add, Pair.scale, Pair.add_re,
      eval_mul, eval_add, eval_scale, eval_zero, eval_constant, Power.eval_power]
    ring1
  · intro point
    have unit := identity point
    simp only [-eq_self, -iff_self, oddReciprocal, generator, generatorDerivative, scale, add, Pair.scale, Pair.add_im,
      eval_mul, eval_add, eval_scale, eval_constant, Power.eval_power]
    calc
      _ = (2 * numerator.eval point * radicand.eval point) * 1 := by ring1
      _ = (2 * numerator.eval point * radicand.eval point) *
          (left.eval point * radicand.eval point +
            right.eval point * (Derivative.derivative radicand).eval point) :=
        congrArg (fun value : Canonical => 2 * numerator.eval point * radicand.eval point * value) unit
      _ = _ := by ring1

/-- Compute the cleared numerator of the derivative of an odd reciprocal primitive. -/
@[expose] def oddPrimitiveNumerator (radicand numerator : Coefficients) (pairs : Nat) : Coefficients :=
  (radicand * Derivative.derivative numerator).scale 2 -
    (numerator * Derivative.derivative radicand).scale (2 * (pairs : Canonical) + 1)

/-- Construct the exact derivative of `R/Y^(2n+1)` with a retained regular-chart denominator. -/
@[expose] def oddPrimitiveDerivative (radicand : Coefficients) (pairs : Nat) (numerator : Coefficients) :
    Expression radicand :=
  ⟨⟨0, oddPrimitiveNumerator radicand numerator pairs⟩,
    (Power.power radicand (pairs + 2)).scale 2⟩

/-- Odd-power differentiation is certified by the original finite coefficient arithmetic. -/
theorem derivative_oddReciprocal (radicand numerator : Coefficients) (pairs : Nat) :
    (oddReciprocal radicand pairs numerator).derivative.Equal
      (oddPrimitiveDerivative radicand pairs numerator) := by
  apply equal_of_cross_eval
  · intro point
    simp only [derivative, directionalDerivative, oddReciprocal, oddPrimitiveDerivative, eval_mul, eval_sub, eval_scale,
      eval_zero, Power.eval_derivative_zero]
    ring1
  · intro point
    simp only [derivative, directionalDerivative, oddReciprocal, oddPrimitiveDerivative, oddPrimitiveNumerator,
      eval_mul, eval_add, eval_sub, eval_scale, Power.eval_power]
    have powerRule := Power.eval_derivative_power_mul radicand (pairs + 1) point
    rewrite [Nat.cast_succ] at powerRule
    rewrite [pow_succ] at powerRule
    simp only [pow_succ]
    calc
      _ = 2 * (radicand.eval point ^ pairs * radicand.eval point) ^ 2 *
          (2 * radicand.eval point * (Derivative.derivative numerator).eval point -
            (2 * (pairs : Canonical) + 1) * numerator.eval point * (Derivative.derivative radicand).eval point) *
          radicand.eval point +
        4 * numerator.eval point * (radicand.eval point ^ pairs * radicand.eval point) *
          radicand.eval point *
          (((pairs : Canonical) + 1) * (radicand.eval point ^ pairs * radicand.eval point) *
            (Derivative.derivative radicand).eval point -
              (Derivative.derivative (Power.power radicand (pairs + 1))).eval point * radicand.eval point) := by ring1
      _ = _ := by rewrite [← powerRule]; ring1

/-- The inverse-root differential equation is an exact finite coefficient identity. -/
theorem inverseRoot_equation (radicand : Coefficients) :
    (((inverseRoot radicand).derivative.scale (radicand.scale 2)).add
      ((inverseRoot radicand).scale (Derivative.derivative radicand))).Equal zero := by
  apply equal_of_cross_eval
  · intro point
    simp only [derivative, directionalDerivative, scale, add, inverseRoot, oddReciprocal, zero, scalar,
      Pair.scale, Pair.add_re, Pair.scalar_re, eval_mul, eval_add, eval_sub, eval_scale,
      eval_zero, eval_constant, Power.eval_derivative_zero]
    ring1
  · intro point
    simp only [derivative, directionalDerivative, scale, add, inverseRoot, oddReciprocal, zero, scalar,
      Pair.scale, Pair.add_im, Pair.scalar_im, eval_mul, eval_add, eval_sub, eval_scale,
      eval_zero, eval_constant, Power.eval_derivative_constant, Power.eval_power]
    rw [Power.eval_derivative_power_succ]
    simp only [Nat.cast_zero, pow_zero]
    ring1

/-- Differentiate a conjugate-norm inverse by the same retained quotient rule.

The equality is an exact coefficient certificate. Realization still needs the
original source denominator and the computed norm-route guard; a zero norm
never acquires an inverse or a selected-sheet zero assertion from this law. -/
theorem derivative_inverse (value : Expression radicand) :
    value.inverse.derivative.Equal (value.derivative.mul (value.inverse.mul value.inverse)).neg := by
  apply equal_of_cross_eval
  · intro point
    simp only [derivative, directionalDerivative, inverse, normNumerator, Pair.norm, Pair.conjugate,
      Pair.scale, mul, neg, Pair.neg_re, Pair.mul_re, Pair.mul_im,
      eval_mul, eval_add, eval_sub, eval_scale, eval_neg,
      Derivative.eval_derivative_mul, Derivative.eval_derivative_add,
      Derivative.eval_derivative_neg]
    ring1
  · intro point
    simp only [derivative, directionalDerivative, inverse, normNumerator, Pair.norm, Pair.conjugate,
      Pair.scale, mul, neg, Pair.neg_im, Pair.mul_re, Pair.mul_im,
      eval_mul, eval_add, eval_sub, eval_scale, eval_neg,
      Derivative.eval_derivative_mul, Derivative.eval_derivative_add,
      Derivative.eval_derivative_neg]
    ring1

end Purelib.Algebra.Quadratic.Pair.Polynomial.Expression
