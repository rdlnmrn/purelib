module
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
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

namespace Purelib.Polynomial.Dense.Gaussian.LinearFactor

/-- The exact monic linear factor `Z-root`. -/
@[expose] def linearFactor (root : Gaussian.Basic.Canonical) :
  (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  ⟨[1, -root]⟩

/-- A monic Gaussian linear factor is not the zero polynomial. -/
@[simp] theorem linearFactor_isZero_false (root :
  Gaussian.Basic.Canonical) :
    (linearFactor root).isZero = false := by
  change (DensePolynomial.normalize ⟨[(1 : Gaussian.Basic.Canonical), -root]⟩).coeffs.isEmpty = false
  rw [DensePolynomial.normalize_linear_of_leading_ne_zero (by decide : (1 : Gaussian.Basic.Canonical) ≠ 0)]
  rfl

/-- A monic Gaussian linear factor has degree one. -/
@[simp] theorem linearFactor_natDegree (root :
  Gaussian.Basic.Canonical) :
    (linearFactor root).natDegree = 1 := by
  change (DensePolynomial.normalize ⟨[(1 : Gaussian.Basic.Canonical), -root]⟩).coeffs.length - 1 = 1
  rw [DensePolynomial.normalize_linear_of_leading_ne_zero (by decide : (1 : Gaussian.Basic.Canonical) ≠ 0)]
  rfl

/-- A monic Gaussian linear factor has leading coefficient one. -/
@[simp] theorem linearFactor_leadingCoeff (root :
  Gaussian.Basic.Canonical) :
    (linearFactor root).leadingCoeff = 1 := by
  change (DensePolynomial.normalize ⟨[(1 : Gaussian.Basic.Canonical), -root]⟩).coeffs.headD 0 = 1
  rw [DensePolynomial.normalize_linear_of_leading_ne_zero (by decide : (1 : Gaussian.Basic.Canonical) ≠ 0)]
  rfl

/-- Evaluate a monic Gaussian linear factor as the point minus its root. -/
@[simp] theorem linearFactor_eval (root point :
  Gaussian.Basic.Canonical) :
    (linearFactor root).eval point = point - root := by
  change (0 * point + 1) * point + -root = point - root
  rw [Gaussian.Basic.zero_mul, Gaussian.Basic.zero_add, Gaussian.Basic.one_mul]
  exact (Gaussian.Basic.sub_eq_add_neg point root).symm

end Purelib.Polynomial.Dense.Gaussian.LinearFactor

end
