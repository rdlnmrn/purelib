module
import Purelib.Data.List.Map
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Fraction.NaturalDenominator
import Purelib.Data.GaussianInt.Arithmetic.Scale
import Purelib.Data.GaussianInt.Embedding
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Basic
public import Purelib.Polynomial.Dense.GaussianInt.Evaluation
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic.Canonical.Fraction (NaturalDenominator)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite denominator-height lower bounds for polynomial residuals

The finite coefficient list is cleared to Gaussian integers by a structural
product of the canonical coordinate denominators.  Homogeneous evaluation at
a displayed common-denominator Gaussian fraction then gives an integral
numerator.  If the residual is nonzero, its integral norm is at least one.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Product

open Purelib.Data
open Purelib.Data.List
open Purelib.Algebra
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Polynomial.Dense.GaussianInt
open Purelib.Polynomial.Dense.Gaussian.Denominator

/-- Clear a finite Gaussian-rational coefficient list by structural recursion. -/
def clear : List Gaussian.Basic.Canonical →
  Dense.Gaussian.Denominator.Clearing.Basic.ClearedCoefficients
  | [] => ⟨1, by decide, []⟩
  | coefficient :: remaining =>
      let head := NaturalDenominator.ofGaussian coefficient
      let tail := clear remaining
      { scale := head.denominator * tail.scale
        scalePositive := Nat.mul_pos head.denominatorPositive tail.scalePositive
        coefficients :=
          Data.GaussianInt.Arithmetic.Scale.scale tail.scale head.numerator ::
            tail.coefficients.map (Data.GaussianInt.Arithmetic.Scale.scale head.denominator) }

/-- Structural denominator clearing retains the source coefficient count.

The scaled leading coefficient contributes one entry, and scaling the original
cleared tail preserves its exact list length. -/
@[simp] theorem clear_length (coefficients : List
  Gaussian.Basic.Canonical) :
    (clear coefficients).coefficients.length = coefficients.length := by
  induction coefficients with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      change Nat.succ (((clear remaining).coefficients.map
        (Data.GaussianInt.Arithmetic.Scale.scale
          (NaturalDenominator.ofGaussian coefficient).denominator)).length) =
        Nat.succ remaining.length
      exact congrArg Nat.succ ((Map.length_map _ _).trans inductionHypothesis)

/-- Clearing coefficients multiplies evaluation by the displayed positive real scale.

The structural clearing construction retains its actual integer coefficients
and product denominator. Their evaluation uses the same point and source list. -/
theorem eval_clear (point :
  Gaussian.Basic.Canonical) (coefficients : List Gaussian.Basic.Canonical) :
    Evaluation.evalIntegers point (clear coefficients).coefficients =
      ⟨((clear coefficients).scale : Rat.Fraction.Rational), 0⟩ *
        DensePolynomial.evalCoeffs point coefficients := by
  induction coefficients with
  | nil => exact (Gaussian.Basic.mul_zero _).symm
  | cons coefficient remaining inductionHypothesis =>
      let head := NaturalDenominator.ofGaussian coefficient
      let tail := clear remaining
      have headValue : head.value = coefficient :=
        NaturalDenominator.ofGaussian_value coefficient
      have headClear := head.value_mul_denominator
      rw [show (clear (coefficient :: remaining)).coefficients =
          Data.GaussianInt.Arithmetic.Scale.scale tail.scale head.numerator ::
            tail.coefficients.map (Data.GaussianInt.Arithmetic.Scale.scale head.denominator)
        from rfl]
      rw [Evaluation.evalIntegers_cons, Map.length_map, clear_length,
        Evaluation.evalIntegers_map_scale, inductionHypothesis]
      rw [Data.GaussianInt.Arithmetic.Scale.toGaussian_scale]
      change
        (⟨(tail.scale : Rat.Fraction.Rational), 0⟩ *
              GaussianInt.toGaussian
                head.numerator) * point ^ remaining.length +
            ⟨(head.denominator : Rat.Fraction.Rational), 0⟩ *
              (⟨(tail.scale : Rat.Fraction.Rational), 0⟩ *
                DensePolynomial.evalCoeffs point remaining) =
          ⟨((head.denominator * tail.scale : Nat) : Rat.Fraction.Rational), 0⟩ *
            DensePolynomial.evalCoeffs point (coefficient :: remaining)
      have headIdentity :
          coefficient * ⟨(head.denominator : Rat.Fraction.Rational), 0⟩ =
            GaussianInt.toGaussian
              head.numerator := by
        rw [← headValue]
        simpa only [GaussianInt.toGaussian_ofNat] using headClear
      rw [DensePolynomial.evalCoeffs_cons_expansion, ← headIdentity, NatCast.mul]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;>
        ring1
end Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Product

end
