module

import Purelib.Algebra.Quadratic.Pair.Polynomial.Primitive
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Algebra.Quadratic.Pair.Polynomial.Derivative
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Power
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-!
# Original-domain rational primitive regressions

An identically zero denominator passes bare cleared derivative comparison but
has no admitted coordinate. A second primitive retains a genuine cancelled
coordinate: the numerator theorem derives an admitted point from the original
nonzero denominator without extending its domain at the cancelled zero.
-/

namespace TestPurelib.Algebra.QuadraticPrimitive

open Purelib.Polynomial
open Dense.Basic.DensePolynomial
open Purelib.Algebra.Quadratic.Pair.Polynomial
open Purelib.Data.Gaussian.Basic (Canonical)

/-- The nonconstant squarefree radicand one plus the coordinate square. -/
private def radicand : Coefficients := ⟨[1, 0, 1]⟩

/-- The original coordinate polynomial. -/
private def coordinate : Coefficients := ⟨[1, 0]⟩

/-- The coordinate polynomial reads back as the supplied exact scalar. -/
private theorem coordinate_eval (point : Canonical) : coordinate.eval point = point := by
  change (0 * point + 1) * point + 0 = point
  ring1

/-- The radicand's coefficient table reads back as one plus the exact coordinate square. -/
private theorem radicand_eval (point : Canonical) : radicand.eval point = point * point + 1 := by
  change ((0 * point + 1) * point + 0) * point + 1 = point * point + 1
  ring1

/-- The original finite derivative has the exact doubled-coordinate table. -/
private theorem radicand_derivative : Dense.Derivative.derivative radicand = coordinate.scale 2 := by
  decide +kernel

/-- The coordinate's actual finite derivative has the unit coefficient table. -/
private theorem coordinate_derivative : Dense.Derivative.derivative coordinate = constant 1 := by
  decide +kernel

/-- The radicand is certified squarefree by its retained finite unit Bézout identity. -/
private def squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate radicand :=
  Dense.Gaussian.Squarefree.Evaluation.ofEvalBezout radicand (by decide +kernel)
    (constant 1) (coordinate.scale (-((2 : Canonical)⁻¹))) (by
      intro point
      rewrite [radicand_eval, Dense.Gaussian.GCD.derivative, radicand_derivative,
        eval_constant, eval_scale, eval_scale, coordinate_eval]
      have paid : (2 : Canonical) * (2 : Canonical)⁻¹ = 1 := by decide +kernel
      calc
        _ = point * point + 1 - (2 * (2 : Canonical)⁻¹) * (point * point) := by ring1
        _ = 1 := by rewrite [paid]; ring1)

/-- The displayed zero denominator is kept by the original expression. -/
private def invalid : Expression radicand := ⟨⟨0, 0⟩, 0⟩

example (point : Canonical) : ¬invalid.Defined point := by
  intro defined
  exact defined (eval_zero point)

/-- Bare cross equality alone certifies arbitrary targets for this invalid zero-denominator expression. -/
private theorem invalid_cross (numerator : Coefficients) :
    invalid.derivative.Equal (Expression.oddReciprocal radicand 0 numerator) := by
  apply Expression.equal_of_cross_eval
  · intro point
    simp only [invalid, Expression.derivative, Expression.directionalDerivative, Expression.oddReciprocal,
      eval_mul, eval_sub, eval_scale, eval_zero, Dense.Power.eval_derivative_zero,
      -eq_self, -iff_self]
    ring0
  · intro point
    simp only [invalid, Expression.derivative, Expression.directionalDerivative, Expression.oddReciprocal,
      eval_mul, eval_sub, eval_add, eval_scale, eval_zero, Dense.Power.eval_derivative_zero,
      -eq_self, -iff_self]
    ring0

/-- The original numerator and denominator cancel algebraically but retain their original zero at the origin. -/
private def cancelled : Expression radicand := ⟨⟨0, coordinate⟩, coordinate⟩

example : ¬cancelled.Defined 0 := by
  intro defined
  exact defined (by
    change coordinate.eval 0 = 0
    rewrite [coordinate_eval]
    rfl)

example : cancelled.Defined 1 := by
  change coordinate.eval 1 ≠ 0
  rewrite [coordinate_eval]
  decide +kernel

/-- Differentiating this admitted rational presentation gives the exact original inverse-root target. -/
private theorem cancelled_derivative :
    cancelled.derivative.Equal (Expression.oddReciprocal radicand 0 coordinate) := by
  apply Expression.equal_of_cross_eval
  · intro point
    simp only [cancelled, Expression.derivative, Expression.directionalDerivative, Expression.oddReciprocal,
      eval_mul, eval_sub, eval_scale, eval_zero, Dense.Power.eval_derivative_zero,
      -eq_self, -iff_self]
    ring0
  · intro point
    simp only [cancelled, Expression.derivative, Expression.directionalDerivative, Expression.oddReciprocal,
      coordinate_derivative, radicand_derivative, eval_mul, eval_sub, eval_add, eval_scale,
      eval_constant, coordinate_eval, Dense.Power.eval_power, -eq_self, -iff_self]
    ring0

example : ∃ coefficient : Coefficients, ∀ point : Canonical,
    cancelled.numerator.im.eval point = coefficient.eval point * cancelled.denominator.eval point :=
  Expression.primitive_imaginary_polynomial cancelled coordinate (by decide +kernel)
    (by decide +kernel) squarefree cancelled_derivative

example : ∃ coefficient : Coefficients,
    (∀ point : Canonical,
      cancelled.numerator.im.eval point = coefficient.eval point * cancelled.denominator.eval point) ∧
    (coordinate.scale 2 -
      ((radicand * Dense.Derivative.derivative coefficient).scale 2 +
        Dense.Derivative.derivative radicand * coefficient)).isZero = true :=
  Expression.primitive_polynomial_operator cancelled coordinate (by decide +kernel)
    (by decide +kernel) squarefree cancelled_derivative

end TestPurelib.Algebra.QuadraticPrimitive
