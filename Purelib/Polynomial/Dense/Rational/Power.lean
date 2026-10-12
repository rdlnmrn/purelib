module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Fold
import Purelib.Data.List.Append
import Purelib.Data.List.Replicate
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.Nat.Subtraction
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Sparse power-minus-value polynomials

The retained descending table contains its original leading one, zero padding
and negative constant coefficient. Direct length, normalization and Horner
certificates follow that same displayed table for every positive degree.
-/
namespace Purelib.Polynomial.Dense.Rational.Power

open Purelib.Data.Rat
open Purelib.Polynomial

open Purelib.Data.List Purelib.Data.Nat

/-! ## The sparse norm equation -/

/-- The high-to-low coefficient list of `T^q-value`, for positive `q`.

The original descending table retains its leading one, degree-minus-one zero
padding and negative trailing value. No normalization or coefficient selection
is performed by this builder. -/
@[expose] public def powerPolynomial (value : Fraction.Rational) (degree : Nat) : Dense.Basic.DensePolynomial
  Fraction.Rational :=
  ⟨1 :: (List.replicate (degree - 1) 0 ++ [-value])⟩

/-- The displayed power-minus-value coefficient list is already normalized by its leading one.

The original nonzero leading coefficient selects the retained branch of the
leading-zero scan, preserving its entire padding and trailing constant. -/
public theorem powerPolynomial_normalized (value : Fraction.Rational) (degree : Nat) :
    (powerPolynomial value degree).normalize = powerPolynomial value degree := by
  have oneNonzero : (1 : Fraction.Rational) ≠ 0 := by decide
  apply Dense.Basic.DensePolynomial.ext
  change
    (1 :: (List.replicate (degree - 1) 0 ++ [-value])).dropWhile
        (· = 0) =
      1 :: (List.replicate (degree - 1) 0 ++ [-value])
  exact DropWhile.cons_of_false (fun coefficient : Fraction.Rational => decide (coefficient = 0))
    1 (List.replicate (degree - 1) 0 ++ [-value]) (decide_eq_false oneNonzero)

/-- A positive power-minus-value table contains the degree plus one coefficients.

The original leading one and trailing negative value surround the retained zero
padding. The positive degree reconstructs its exact predecessor length. -/
public theorem powerPolynomial_coefficients_length (value : Fraction.Rational)
    (degree : Nat) (positive : 0 < degree) :
    (powerPolynomial value degree).coeffs.length = degree + 1 := by
  change (List.replicate (degree - 1) (0 : Fraction.Rational) ++ [-value]).length + 1 = _
  rewrite [Append.length_append, Replicate.length_replicate]
  change (degree - 1 + 1) + 1 = degree + 1
  exact congrArg (fun count => count + 1)
    ((Nat.add_comm _ 1).trans (Subtraction.add_sub_of_le positive))

/-- A positive power-minus-value polynomial has exactly that degree.

Its normalized table is the original table with degree plus one entries.
Subtracting the retained final length unit recovers the supplied degree. -/
public theorem powerPolynomial_degree (value : Fraction.Rational) (degree : Nat)
    (positive : 0 < degree) :
    (powerPolynomial value degree).natDegree = degree := by
  change (powerPolynomial value degree).normalize.coeffs.length - 1 = degree
  rewrite [powerPolynomial_normalized, powerPolynomial_coefficients_length value degree positive]
  exact Subtraction.add_sub_cancel_right degree 1

/-- Appending a final descending coefficient performs one final multiply-and-add Horner step.

The original fold first evaluates the unchanged coefficient list. Its retained
accumulator then consumes the supplied trailing coefficient exactly once. -/
private theorem evalCoeffs_append_singleton
    (point : Fraction.Rational) (coefficients : List Fraction.Rational)
    (trailing : Fraction.Rational) :
    Dense.Basic.DensePolynomial.evalCoeffs point
        (coefficients ++ [trailing]) =
      Dense.Basic.DensePolynomial.evalCoeffs point coefficients *
        point + trailing := open Purelib in by
  unfold Dense.Basic.DensePolynomial.evalCoeffs
  rewrite [Purelib.Data.List.Fold.foldl_append]
  exact Eq.refl _

/-- For a positive exponent, the displayed polynomial evaluates as the point power minus the supplied value.

The original zero padding follows the same Horner accumulator. Its positive
degree reconstructs the retained predecessor exponent before the final constant. -/
public theorem powerPolynomial_eval (value point : Fraction.Rational) (degree : Nat)
    (positive : 0 < degree) :
    (powerPolynomial value degree).eval point = point ^ degree - value := by
  have predecessor : degree - 1 + 1 = degree :=
    (Nat.add_comm _ 1).trans (Subtraction.add_sub_of_le positive)
  change Dense.Basic.DensePolynomial.evalCoeffs point
      (1 :: (List.replicate (degree - 1) 0 ++ [-value])) =
    point ^ degree - value
  rw [show
      1 :: (List.replicate (degree - 1) 0 ++ [-value]) =
        ([1] ++ List.replicate (degree - 1) 0) ++ [-value] by
      exact Eq.refl _]
  rw [evalCoeffs_append_singleton,
    Dense.Basic.DensePolynomial.evalCoeffs_append_replicate_zero]
  change ((0 * point + 1) * point ^ (degree - 1)) * point + -value =
    point ^ degree - value
  calc
    (0 * point + 1) * point ^ (degree - 1) * point + -value =
        point ^ (degree - 1) * point - value := by ring1
    _ = point ^ degree - value := by
      rw [← pow_succ, predecessor]

/-- The displayed power-minus-value polynomial is nonzero because its normalized list begins with one. -/
public theorem powerPolynomial_nonzero (value : Fraction.Rational) (degree : Nat)
    (_positive : 0 < degree) :
    (powerPolynomial value degree).isZero = false := by
  have normalized := powerPolynomial_normalized value degree
  change (powerPolynomial value degree).normalize.coeffs.isEmpty = false
  rw [normalized]
  rfl
end Purelib.Polynomial.Dense.Rational.Power
