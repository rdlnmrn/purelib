module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.CoordinatePower
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Reciprocal
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Nat.Order

/-!
# Executable squarefreeness under finite coefficient reversal

Clear the reciprocal denominators in the original finite Bézout identity.
This gives a power of the coordinate in the ideal of the reversed polynomial
and its derivative. The reversed constant coefficient is the original
nonzero leading coefficient; a finite recursive Bézout calculation removes
that coordinate power. No root enumeration or nonzero affine constant term
is assumed.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree.Reciprocal

open Purelib.Data
open Purelib.Polynomial

/-- Squarefreeness of the exact reversed coefficient list, including inputs
with a zero constant coefficient.

The retained Bézout factors are padded to the same natural degree bound.
Their reversed finite identity retains an explicit coordinate-power witness. -/
@[expose] def reversedSquarefree (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (nonzero :
  polynomial.isZero =
  false)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate polynomial) :
      Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate (Dense.Gaussian.Reciprocal.reversed polynomial)
      := by
  let left := squarefree.left
  let right := squarefree.right
  let padding := max left.natDegree right.natDegree + 1
  have leftBelow : left.natDegree < padding := Nat.lt_succ_of_le (Nat.Order.le_max_left _ _)
  have rightBelow : right.natDegree < padding := Nat.lt_succ_of_le (Nat.Order.le_max_right _ _)
  let leftPad := Dense.Gaussian.Reciprocal.padded left padding
  let rightPad := Dense.Gaussian.Reciprocal.padded right padding
  let first := leftPad + Dense.Basic.DensePolynomial.scale (polynomial.natDegree : Gaussian.Basic.Canonical)
    (Dense.Basic.DensePolynomial.shift 1 rightPad)
  let second := -(Dense.Basic.DensePolynomial.shift 2 rightPad)
  have originNonzero : (Dense.Gaussian.Reciprocal.reversed polynomial).eval 0 ≠ 0 := by
    rw [Dense.Gaussian.Reciprocal.reversed_origin]
    exact Dense.Basic.DensePolynomial.leadingCoeff_ne_zero nonzero
  apply Dense.Gaussian.Coprime.CoordinatePower.ofPowerIdentity (Dense.Gaussian.Reciprocal.reversed polynomial)
    (Dense.Gaussian.GCD.derivative (Dense.Gaussian.Reciprocal.reversed polynomial))
    (Dense.Gaussian.Reciprocal.reversed_nonzero nonzero) originNonzero (polynomial.natDegree + padding) first second
  intro point
  by_cases zero : point = 0
  · subst point
    have paddingPositive : 0 < polynomial.natDegree + padding := by
      dsimp only [padding]
      rw [Nat.add_succ]
      exact Nat.zero_lt_succ _
    dsimp only [first, second, leftPad, rightPad]
    rw [zero_pow paddingPositive.ne', Dense.Basic.DensePolynomial.eval_add, Dense.Basic.DensePolynomial.eval_scale,
      Dense.Basic.DensePolynomial.eval_shift, Dense.Basic.DensePolynomial.eval_neg,
      Dense.Basic.DensePolynomial.eval_shift,
      Dense.Gaussian.Reciprocal.padded_origin left padding leftBelow, Dense.Gaussian.Reciprocal.padded_origin right
        padding rightBelow]
    ring1
  · have derivativeIdentity :
        point ^ polynomial.natDegree * (Dense.Gaussian.GCD.derivative polynomial).eval point⁻¹ =
          (polynomial.natDegree : Gaussian.Basic.Canonical) * point * (Dense.Gaussian.Reciprocal.reversed
            polynomial).eval point -
            point ^ 2 * (Dense.Gaussian.GCD.derivative (Dense.Gaussian.Reciprocal.reversed polynomial)).eval point :=
      by
        have identity := Dense.Gaussian.Reciprocal.reversed_derivative_identity polynomial nonzero point zero
        have recovery (first second : Gaussian.Basic.Canonical) :
            (first + second) - second = first := by ring1
        exact (recovery _ _).symm.trans
          (congrArg (fun value : Gaussian.Basic.Canonical => value -
            point ^ 2 * (Dense.Gaussian.GCD.derivative (Dense.Gaussian.Reciprocal.reversed polynomial)).eval point)
              identity)
    dsimp only [first, second, leftPad, rightPad]
    rw [Dense.Basic.DensePolynomial.eval_add, Dense.Basic.DensePolynomial.eval_scale,
      Dense.Basic.DensePolynomial.eval_shift, Dense.Basic.DensePolynomial.eval_neg,
      Dense.Basic.DensePolynomial.eval_shift,
      Dense.Gaussian.Reciprocal.padded_identity left padding leftBelow.le point zero,
      Dense.Gaussian.Reciprocal.padded_identity right padding rightBelow.le point zero]
    calc
      _ = point ^ padding * point ^ polynomial.natDegree *
          (left.eval point⁻¹ * polynomial.eval point⁻¹ +
            right.eval point⁻¹ * (Dense.Gaussian.GCD.derivative polynomial).eval point⁻¹) := by
              rw [← squarefree.identity, pow_add]; ring1
      _ = point ^ padding * (left.eval point⁻¹ *
            (point ^ polynomial.natDegree * polynomial.eval point⁻¹) +
          right.eval point⁻¹ * (point ^ polynomial.natDegree *
            (Dense.Gaussian.GCD.derivative polynomial).eval point⁻¹)) := by ring1
      _ = _ := by
        rw [← Dense.Gaussian.Reciprocal.reversed_identity polynomial point zero, derivativeIdentity, pow_one]
        ring1
end Purelib.Polynomial.Dense.Gaussian.Squarefree.Reciprocal

end
