module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Fraction
import Purelib.Data.Nat.Choose
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Algebra.Binomial
public import Purelib.Algebra.Binomial.Gaussian
import Purelib.Algebra.FiniteSum.Prefix
public import Purelib.Approximation.Gaussian.Exponential.Taylor.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.FiniteSum.Scale
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Nat.Factorial.Basic
import Purelib.Data.Rat.Factorial
import Purelib.Data.Rat.Fraction.Field

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

section
public section

/-! Approximation Gaussian Exponential Taylor Cauchy and its finite structural certificates. -/

namespace Purelib.Approximation.Gaussian.Exponential.Taylor.Cauchy

open Purelib
open Purelib.Algebra
open Purelib.Algebra.Binomial
open Purelib.Algebra.FiniteSum
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Data.Gaussian
open Purelib.Data.Nat
open Purelib.Data.Rat

/-- The product of the two Taylor monomials at complementary degrees in one finite Cauchy row. -/
@[expose] public def cauchyTerm (x y : Data.Gaussian.Basic.Canonical) (row column : Nat) : Data.Gaussian.Basic.Canonical
  :=
  Taylor.Basic.taylorTerm x column * Taylor.Basic.taylorTerm y (row - column)

/-- A Cauchy-row term is its Gaussian binomial term scaled by the reciprocal row factorial when the column lies within
the row. -/
theorem cauchyTerm_eq_scaled_binomial (x y : Data.Gaussian.Basic.Canonical) (row column : Nat)
    (order : column ≤ row) :
    Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTerm x y row column =
      Scale.scale
        (1 / (Factorial.Basic.factorial row : Fraction.Rational)) (Binomial.Gaussian.binomialTerm x y row column) := by
  rw [Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTerm, Taylor.Basic.taylorTerm, Taylor.Basic.taylorTerm,
    Scale.scale_mul_scale,
    Binomial.Gaussian.binomialTerm]
  have coefficient := Factorial.reciprocal_factorial_product row column order
  have coefficient' :
      (1 / (Factorial.Basic.factorial column : Fraction.Rational)) *
          (1 / (Factorial.Basic.factorial (row - column) : Fraction.Rational)) =
        (1 / (Factorial.Basic.factorial row : Fraction.Rational)) * (Data.Nat.Choose.Pascal.choose row column :
          Fraction.Rational) :=
    coefficient.trans (by
      change (Data.Nat.Choose.Pascal.choose row column : Fraction.Rational) *
          (Factorial.Basic.factorial row : Fraction.Rational)⁻¹ =
        (1 * (Factorial.Basic.factorial row : Fraction.Rational)⁻¹) *
          (Data.Nat.Choose.Pascal.choose row column : Fraction.Rational)
      rw [Fraction.Field.one_mul]
      exact Fraction.Field.mul_comm _ _)
  apply Data.Gaussian.Basic.ext <;>
    simp only [Scale.scale_re,
      Scale.scale_im, Basic.mul_re, Basic.mul_im,
      Cast.natCast_re, Cast.natCast_im] <;>
    rw [coefficient'] <;> ring1

/-- Sum the complete finite row of complementary-degree Taylor products. -/
@[expose] public def cauchyDiagonal (x y : Data.Gaussian.Basic.Canonical) (row : Nat) : Data.Gaussian.Basic.Canonical :=
  Prefix.sum (Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTerm x y row) (row + 1)

/-- Each complete finite Cauchy-product diagonal is exactly the corresponding Taylor monomial at `x + y`. -/
theorem cauchyDiagonal_eq_taylorTerm (x y : Data.Gaussian.Basic.Canonical) (row : Nat) :
    Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyDiagonal x y row = Taylor.Basic.taylorTerm (x + y) row := by
  rw [Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyDiagonal]
  calc
    Prefix.sum (Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTerm x y row) (row + 1) =
        Prefix.sum
          (fun column => Scale.scale
            (1 / (Factorial.Basic.factorial row : Fraction.Rational))
            (Binomial.Gaussian.binomialTerm x y row column)) (row + 1) :=
      Prefix.sum_congr_lt (row + 1)
        (fun column order => Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTerm_eq_scaled_binomial x y row
          column
          (Nat.le_of_lt_succ order))
    _ = Scale.scale
        (1 / (Factorial.Basic.factorial row : Fraction.Rational)) (Binomial.Gaussian.binomialSum x y row) := by
      rw [Binomial.Gaussian.binomialSum, FiniteSum.Scale.scale_sum]
    _ = Scale.scale
        (1 / (Factorial.Basic.factorial row : Fraction.Rational)) ((x + y) ^ row) := by
      rw [Purelib.Algebra.Binomial.Gaussian.binomial]
    _ = Taylor.Basic.taylorTerm (x + y) row := rfl

/-- The degree-zero exponential Taylor monomial is one. -/
@[simp] theorem taylorTerm_zero (x : Data.Gaussian.Basic.Canonical) : Taylor.Basic.taylorTerm x 0 = 1 := by
  rw [Taylor.Basic.taylorTerm, Factorial.Basic.factorial_zero, pow_zero]
  apply Data.Gaussian.Basic.ext <;>
    simp only [Scale.scale_re,
      Scale.scale_im, Basic.one_re, Basic.one_im] <;>
    rw [show ((1 : Nat) : Fraction.Rational) = 1 by rfl,
      show (1 / (1 : Fraction.Rational)) = 1 by decide] <;> ring1

/-- The finite exponential Taylor polynomial equals the explicit prefix sum of its monomials. -/
theorem truncatedExp_eq_sum (x : Data.Gaussian.Basic.Canonical) : ∀ degree : Nat,
    Taylor.Basic.truncatedExp x degree = Prefix.sum (Taylor.Basic.taylorTerm x) (degree + 1)
  | 0 => by
      rw [Taylor.Basic.truncatedExp_zero, Prefix.sum_succ, Prefix.sum_zero,
        Approximation.Gaussian.Exponential.Taylor.Cauchy.taylorTerm_zero,
        Data.Gaussian.Basic.zero_add]
  | degree + 1 => by
      calc
        Taylor.Basic.truncatedExp x (degree + 1) =
            Taylor.Basic.truncatedExp x degree + Taylor.Basic.taylorTerm x (degree + 1) := rfl
        _ = Prefix.sum (Taylor.Basic.taylorTerm x) (degree + 1) +
            Taylor.Basic.taylorTerm x (degree + 1) := by
          rw [Purelib.Approximation.Gaussian.Exponential.Taylor.Cauchy.truncatedExp_eq_sum x degree]
        _ = Prefix.sum (Taylor.Basic.taylorTerm x) (degree + 1 + 1) := rfl

/-- Sum the square array of Taylor products with each operand degree bounded by the displayed degree. -/
@[expose] public def cauchyRectangle (x y : Data.Gaussian.Basic.Canonical) (degree : Nat) :
  Data.Gaussian.Basic.Canonical :=
  Prefix.sum
    (fun leftDegree =>
      Prefix.sum
        (fun rightDegree =>
          Taylor.Basic.taylorTerm x leftDegree * Taylor.Basic.taylorTerm y rightDegree)
        (degree + 1))
    (degree + 1)

/-- The product of two equal-degree Taylor polynomials equals the finite square Cauchy array. -/
theorem truncatedExp_mul_eq_cauchyRectangle
    (x y : Data.Gaussian.Basic.Canonical) (degree : Nat) :
    Taylor.Basic.truncatedExp x degree * Taylor.Basic.truncatedExp y degree =
      Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyRectangle x y degree := by
  rw [Approximation.Gaussian.Exponential.Taylor.Cauchy.truncatedExp_eq_sum,
    Approximation.Gaussian.Exponential.Taylor.Cauchy.truncatedExp_eq_sum,
    Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyRectangle, Prefix.sum_product]

/-- Sum the finite Taylor products whose combined degree is at most the displayed cutoff. -/
@[expose] public def cauchyTriangle (x y : Data.Gaussian.Basic.Canonical) (degree : Nat) : Data.Gaussian.Basic.Canonical
  :=
  Prefix.sum
    (fun leftDegree =>
      Prefix.sum
        (fun rightDegree =>
          Taylor.Basic.taylorTerm x leftDegree * Taylor.Basic.taylorTerm y rightDegree)
        (degree - leftDegree + 1))
    (degree + 1)

/-- The portion of the square Cauchy product strictly above total degree `degree`. Row `leftDegree` contains exactly
`leftDegree` displayed terms. -/
@[expose] public def cauchyUpperTail (x y : Data.Gaussian.Basic.Canonical) (degree : Nat) :
  Data.Gaussian.Basic.Canonical :=
  Prefix.sum
    (fun leftDegree =>
      Prefix.sum
        (fun offset =>
          Taylor.Basic.taylorTerm x leftDegree *
            Taylor.Basic.taylorTerm y (degree - leftDegree + 1 + offset))
        leftDegree)
    (degree + 1)

/-- The square Cauchy array splits exactly into its lower-degree triangle and retained upper tail. -/
theorem cauchyRectangle_eq_triangle_add_upper
    (x y : Data.Gaussian.Basic.Canonical) (degree : Nat) :
    Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyRectangle x y degree =
      Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTriangle x y degree +
        Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyUpperTail x y degree := by
  rw [Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyRectangle,
    Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTriangle,
    Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyUpperTail]
  calc
    Prefix.sum
        (fun leftDegree =>
          Prefix.sum
            (fun rightDegree =>
              Taylor.Basic.taylorTerm x leftDegree * Taylor.Basic.taylorTerm y rightDegree)
            (degree + 1))
        (degree + 1) =
      Prefix.sum
        (fun leftDegree =>
          Prefix.sum
              (fun rightDegree =>
                Taylor.Basic.taylorTerm x leftDegree * Taylor.Basic.taylorTerm y rightDegree)
              (degree - leftDegree + 1) +
            Prefix.sum
              (fun offset =>
                Taylor.Basic.taylorTerm x leftDegree *
                  Taylor.Basic.taylorTerm y (degree - leftDegree + 1 + offset))
              leftDegree)
        (degree + 1) := by
      apply Prefix.sum_congr_lt
      intro leftDegree leftOrder
      have leftLe : leftDegree ≤ degree := Nat.le_of_lt_succ leftOrder
      have countIdentity :
          degree + 1 = degree - leftDegree + 1 + leftDegree := by
        calc
          degree + 1 = (degree - leftDegree + leftDegree) + 1 :=
            congrArg (fun value => value + 1)
              (Purelib.Data.Nat.Subtraction.sub_add_cancel leftLe).symm
          _ = degree - leftDegree + 1 + leftDegree :=
            Nat.add_right_comm (degree - leftDegree) leftDegree 1
      rw [countIdentity, Prefix.sum_append]
    _ = Prefix.sum
          (fun leftDegree =>
            Prefix.sum
              (fun rightDegree =>
                Taylor.Basic.taylorTerm x leftDegree * Taylor.Basic.taylorTerm y rightDegree)
              (degree - leftDegree + 1))
          (degree + 1) +
        Prefix.sum
          (fun leftDegree =>
            Prefix.sum
              (fun offset =>
                Taylor.Basic.taylorTerm x leftDegree *
                  Taylor.Basic.taylorTerm y (degree - leftDegree + 1 + offset))
              leftDegree)
          (degree + 1) :=
      Prefix.sum_add _ _ (degree + 1)

/-- Increasing the triangular degree cutoff adds exactly the next complete Cauchy diagonal. -/
theorem cauchyTriangle_succ (x y : Data.Gaussian.Basic.Canonical) (degree : Nat) :
    Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTriangle x y (degree + 1) =
      Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTriangle x y degree +
        Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyDiagonal x y (degree + 1) := by
  rw [Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTriangle,
    Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTriangle,
    Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyDiagonal, Prefix.sum_succ]
  have rowSplit :
      Prefix.sum
          (fun leftDegree =>
            Prefix.sum
              (fun rightDegree =>
                Taylor.Basic.taylorTerm x leftDegree * Taylor.Basic.taylorTerm y rightDegree)
              (degree + 1 - leftDegree + 1))
          (degree + 1) =
        Prefix.sum
          (fun leftDegree =>
            Prefix.sum
                (fun rightDegree =>
                  Taylor.Basic.taylorTerm x leftDegree * Taylor.Basic.taylorTerm y rightDegree)
                (degree - leftDegree + 1) +
              Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTerm x y (degree + 1) leftDegree)
          (degree + 1) := by
    apply Prefix.sum_congr_lt
    intro leftDegree leftOrder
    have leftLe : leftDegree ≤ degree := Nat.le_of_lt_succ leftOrder
    have countIdentity :
        degree + 1 - leftDegree + 1 = degree - leftDegree + 1 + 1 := by
      rw [Purelib.Data.Nat.Subtraction.succ_sub leftLe]
    rw [countIdentity, Prefix.sum_succ, Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTerm]
    rw [show degree - leftDegree + 1 =
      degree + 1 - leftDegree from (Purelib.Data.Nat.Subtraction.succ_sub leftLe).symm]
  rw [rowSplit, Prefix.sum_add]
  have finalRow :
      Prefix.sum
          (fun rightDegree =>
            Taylor.Basic.taylorTerm x (degree + 1) * Taylor.Basic.taylorTerm y rightDegree)
          (degree + 1 - (degree + 1) + 1) =
        Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTerm x y (degree + 1) (degree + 1) := by
    rewrite [Nat.sub_self, Nat.zero_add, Prefix.sum_succ, Prefix.sum_zero,
      Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTerm, Nat.sub_self, Data.Gaussian.Basic.zero_add]
    exact Eq.refl _
  rw [finalRow]
  have diagonalSucc :
      Prefix.sum (Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTerm x y (degree + 1)) (degree + 1 + 1) =
        Prefix.sum (Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTerm x y (degree + 1)) (degree + 1) +
          Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTerm x y (degree + 1) (degree + 1) := rfl
  rw [diagonalSucc]
  apply Data.Gaussian.Basic.ext <;>
    simp only [Basic.add_re, Basic.add_im] <;> ring1

/-- The lower triangular finite Cauchy product is exactly the Taylor polynomial at the sum. -/
theorem cauchyTriangle_eq_truncatedExp (x y : Data.Gaussian.Basic.Canonical) : ∀ degree : Nat,
    Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTriangle x y degree = Taylor.Basic.truncatedExp (x + y)
      degree
  | 0 => by
      change (0 : Data.Gaussian.Basic.Canonical) +
          ((0 : Data.Gaussian.Basic.Canonical) + Taylor.Basic.taylorTerm x 0 * Taylor.Basic.taylorTerm y 0) = 1
      rw [Approximation.Gaussian.Exponential.Taylor.Cauchy.taylorTerm_zero,
        Approximation.Gaussian.Exponential.Taylor.Cauchy.taylorTerm_zero,
        Data.Gaussian.Basic.one_mul,
        Data.Gaussian.Basic.zero_add,
        Data.Gaussian.Basic.zero_add]
  | degree + 1 => by
      rw [Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTriangle_succ,
        Purelib.Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTriangle_eq_truncatedExp x y degree,
        Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyDiagonal_eq_taylorTerm, Taylor.Basic.truncatedExp_succ]

/-- Exact finite decomposition of the exponential product error into only the displayed high-total-degree terms of the
square Cauchy product. -/
theorem truncatedExp_mul_sub_truncatedExp_eq_upper
    (x y : Data.Gaussian.Basic.Canonical) (degree : Nat) :
    Taylor.Basic.truncatedExp x degree * Taylor.Basic.truncatedExp y degree -
        Taylor.Basic.truncatedExp (x + y) degree =
      Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyUpperTail x y degree := by
  rw [Approximation.Gaussian.Exponential.Taylor.Cauchy.truncatedExp_mul_eq_cauchyRectangle,
    Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyRectangle_eq_triangle_add_upper,
    Approximation.Gaussian.Exponential.Taylor.Cauchy.cauchyTriangle_eq_truncatedExp]
  apply Data.Gaussian.Basic.ext <;>
    simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im] <;> ring1
end Purelib.Approximation.Gaussian.Exponential.Taylor.Cauchy

end
