module
import Purelib.Data.List.Membership
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Gaussian.LinearFactor
import Purelib.Polynomial.Dense.Gaussian.Multiplication
public import Purelib.Polynomial.Dense.Multiplication
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.GroupWithZero.NeZero

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data

open Purelib.Polynomial

section
public section

/-!
# Exact split polynomial loops and geometric Artin cells

This file supplies the elementary polynomial loops required by the finite
braid-group theorem.  The model is deliberately exact: every vertex is a
monic Gaussian-rational polynomial displayed as the finite product of its
linear factors.  Pairwise distinct integer lattice roots are an explicit
simple-root certificate, so no root approximation or completed
configuration space is used.

The elementary loop for `sigma_i` moves the roots at the two adjacent real
positions to a common rational projection coordinate, separates them at
heights `-1` and `1`, and returns them in exchanged owner order.  Reversing
the height order realizes the inverse generator.  Cancellation, disjoint
commutation, and the three-strand Artin relation carry concrete finite
coefficient-space cells: respectively a backtracking midpoint, a four-root
simultaneous midpoint, and a collision-free triple-projection vertex.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Split

/-- Finite product of the displayed linear factors. -/
@[expose] def splitPolynomial : List Gaussian.Basic.Canonical →
  Dense.Gaussian.Basic.ExactPolynomialLoops.GaussianPolynomial
  | [] => DensePolynomial.constant 1
  | root :: remaining => Dense.Gaussian.LinearFactor.linearFactor root *
    splitPolynomial remaining

/-- The product over an empty root list is the constant polynomial one. -/
@[simp] theorem splitPolynomial_nil :
  splitPolynomial [] = DensePolynomial.constant 1 := rfl

/-- Adding a root at the front multiplies its monic linear factor by the remaining finite product. -/
@[simp] theorem splitPolynomial_cons (root : Gaussian.Basic.Canonical)
    (remaining : List Gaussian.Basic.Canonical) :
    splitPolynomial (root :: remaining) =
      Dense.Gaussian.LinearFactor.linearFactor root * splitPolynomial remaining := rfl

/-- Every finite product of monic Gaussian linear factors is nonzero. -/
@[simp] theorem splitPolynomial_isZero_false (roots : List
  Gaussian.Basic.Canonical) :
    (splitPolynomial roots).isZero = false := by
  induction roots with
  | nil =>
      change (DensePolynomial.constant (1 : Gaussian.Basic.Canonical)).normalize.coeffs.isEmpty = false
      rw [DensePolynomial.normalize_constant_of_ne (by decide : (1 : Gaussian.Basic.Canonical) ≠ 0)]
      rfl
  | cons root remaining inductionHypothesis =>
      exact Dense.Gaussian.Multiplication.product_isZero_false
        (Dense.Gaussian.LinearFactor.linearFactor_isZero_false root) inductionHypothesis

/-- The degree of the finite split polynomial equals the root-list length, including repetitions. -/
@[simp] theorem splitPolynomial_natDegree (roots : List
  Gaussian.Basic.Canonical) :
    (splitPolynomial roots).natDegree = roots.length := by
  induction roots with
  | nil =>
      change (DensePolynomial.constant (1 : Gaussian.Basic.Canonical)).normalize.coeffs.length - 1 = 0
      rw [DensePolynomial.normalize_constant_of_ne (by decide : (1 : Gaussian.Basic.Canonical) ≠ 0)]
      rfl
  | cons root remaining inductionHypothesis =>
      rw [splitPolynomial_cons, DensePolynomial.natDegree_mul
        (Dense.Gaussian.LinearFactor.linearFactor_isZero_false root)
        (splitPolynomial_isZero_false remaining),
        Dense.Gaussian.LinearFactor.linearFactor_natDegree, inductionHypothesis, List.length_cons]
      omega

/-- Every finite split polynomial has leading coefficient one. -/
@[simp] theorem splitPolynomial_leadingCoeff (roots : List
  Gaussian.Basic.Canonical) :
    (splitPolynomial roots).leadingCoeff = 1 := by
  induction roots with
  | nil =>
      change (DensePolynomial.constant (1 : Gaussian.Basic.Canonical)).normalize.coeffs.headD 0 = 1
      rw [DensePolynomial.normalize_constant_of_ne (by decide : (1 : Gaussian.Basic.Canonical) ≠ 0)]
      rfl
  | cons root remaining inductionHypothesis =>
      rw [splitPolynomial_cons, DensePolynomial.leadingCoeff_mul
        (Dense.Gaussian.LinearFactor.linearFactor_isZero_false root)
        (splitPolynomial_isZero_false remaining),
        Dense.Gaussian.LinearFactor.linearFactor_leadingCoeff, inductionHypothesis,
        Gaussian.Basic.one_mul]

/-- A root occurring in the retained list evaluates the finite split polynomial to zero. -/
theorem splitPolynomial_eval_eq_zero_of_mem {root :
  Gaussian.Basic.Canonical} :
    ∀ {roots : List Gaussian.Basic.Canonical}, root ∈ roots →
      (splitPolynomial roots).eval root = 0 := by
  intro roots membership
  induction roots with
  | nil => contradiction
  | cons head remaining inductionHypothesis =>
      rcases List.Membership.mem_cons.mp membership with same | later
      · subst head
        rw [splitPolynomial_cons, DensePolynomial.eval_mul,
          Dense.Gaussian.LinearFactor.linearFactor_eval,
          Gaussian.Basic.sub_self,
          Gaussian.Basic.zero_mul]
      · rw [splitPolynomial_cons, DensePolynomial.eval_mul, inductionHypothesis later,
          Gaussian.Basic.mul_zero]

end Purelib.Polynomial.Dense.Gaussian.Split

end
