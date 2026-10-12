module
import Purelib.Data.Gaussian.Basic
public import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-!
# Ascending Gaussian coefficient polynomials

Ascending finite coordinates produce the same dense polynomial by a
constant term followed by a one-degree shift of the retained tail. Its
readback is the finite coefficient-monomial sum.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Ascending

open Purelib.Algebra
open Purelib.Data
open Purelib.Polynomial

/-! ## Cofactor vectors as dense polynomials -/

/-- Construct a dense Gaussian polynomial from coefficients indexed in ascending degree.

The recursion adds the constant coefficient to the shifted polynomial of the remaining finite indices. -/
@[expose] def polynomialFromLow : (n : Nat) → (Fin n → Gaussian.Basic.Canonical) →
    Basic.CanonicalCoefficients.CoefficientPolynomial
  | 0, _ => 0
  | n + 1, coefficients =>
      Dense.Basic.DensePolynomial.constant (coefficients 0) +
        Dense.Basic.DensePolynomial.shift 1 (Purelib.Polynomial.Dense.Gaussian.Ascending.polynomialFromLow n (fun index
          => coefficients index.succ))

/-- Evaluate the ascending-index construction as the finite sum of coefficient monomials.

The empty family contributes zero. Each successor-sized family retains its
constant coordinate and the same shifted tail before finite summation. -/
@[simp] theorem eval_polynomialFromLow (outer : Gaussian.Basic.Canonical) :
    ∀ (n : Nat) (coefficients : Fin n → Gaussian.Basic.Canonical),
      (Dense.Gaussian.Ascending.polynomialFromLow n coefficients).eval outer =
        FiniteSum.Fin.sumFin
          (fun index => coefficients index * outer ^ (index : Nat))
  | 0, _ => by
      rfl
  | n + 1, coefficients => by
      rw [Dense.Gaussian.Ascending.polynomialFromLow, Dense.Basic.DensePolynomial.eval_add,
        Dense.Basic.DensePolynomial.eval_constant, Dense.Basic.DensePolynomial.eval_shift,
        Purelib.Polynomial.Dense.Gaussian.Ascending.eval_polynomialFromLow outer n,
        FiniteSum.Fin.sumFin_succ]
      change coefficients 0 +
          FiniteSum.Fin.sumFin
            (fun index : Fin n => coefficients index.succ * outer ^ (index : Nat)) *
              outer ^ 1 =
        coefficients 0 * outer ^ 0 +
          FiniteSum.Fin.sumFin
            (fun index : Fin n =>
              coefficients index.succ * outer ^ (index.succ : Nat))
      have tailPower :
          FiniteSum.Fin.sumFin
              (fun index : Fin n =>
                coefficients index.succ * outer ^ (index.succ : Nat)) =
            FiniteSum.Fin.sumFin
              (fun index : Fin n =>
                (coefficients index.succ * outer ^ (index : Nat)) * outer) :=
        FiniteSum.Fin.sumFin_congr
        (left := fun index : Fin n =>
          coefficients index.succ * outer ^ (index.succ : Nat))
        (right := fun index : Fin n =>
          (coefficients index.succ * outer ^ (index : Nat)) * outer)
        (fun index => by
          change coefficients index.succ * outer ^ ((index : Nat) + 1) = _
          rw [pow_succ]
          ring1)
      rw [tailPower]
      rw [FiniteSum.Fin.sumFin_mul_right]
      ring1

end Purelib.Polynomial.Dense.Gaussian.Ascending

end
