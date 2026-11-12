module

public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Map
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.Ring

/-!
# Conjugation of finite Gaussian coefficient polynomials

The original coefficient table is conjugated in its retained descending order.
The same executable scalar embedding preserves normalization, degree and Horner
evaluation, including zero coefficients and repeated roots.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Conjugation

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

/-- Gaussian conjugation as an explicit injective field embedding. -/
@[expose] def embedding : Algebra.Field.Embedding Canonical Canonical where
  toFun := Basic.conj
  injective := by
    intro first second equal
    exact (Basic.conj_conj first).symm.trans
      ((congrArg Basic.conj equal).trans (Basic.conj_conj second))
  map_zero := Basic.conj_zero
  map_one := rfl
  map_add := Basic.conj_add
  map_neg := by
    intro value
    apply Basic.ext <;> simp only [Basic.conj, Basic.neg_re, Basic.neg_im, -eq_self, -iff_self] <;> ring1
  map_mul := Basic.conj_mul
  map_inv := by
    intro value
    rw [Field.inv_eq, Field.inv_eq]
    apply Basic.ext
    · change value.re / Norm.Basic.normSq value =
        (Basic.conj value).re / Norm.Basic.normSq (Basic.conj value)
      rw [Norm.Basic.normSq_conj]
      rfl
    · change -(-value.im / Norm.Basic.normSq value) =
        -(Basic.conj value).im / Norm.Basic.normSq (Basic.conj value)
      rw [Norm.Basic.normSq_conj]
      change -(-value.im / Norm.Basic.normSq value) = - -value.im / Norm.Basic.normSq value
      rw [Algebra.Field.ExplicitField.div_eq_mul_inv, Algebra.Field.ExplicitField.div_eq_mul_inv]
      ring1

/-- Conjugate every original coefficient without changing its finite order. -/
@[expose] def conjugate (polynomial : CoefficientPolynomial) : CoefficientPolynomial :=
  Dense.Map.map embedding.toFun polynomial

/-- Conjugation preserves the exact displayed coefficient count after normalization. -/
theorem natDegree (polynomial : CoefficientPolynomial) :
    (conjugate polynomial).natDegree = polynomial.natDegree :=
  Dense.Map.map_natDegree embedding.toFun embedding.map_zero embedding.injective polynomial

/-- Conjugated coefficients evaluated at the conjugated input give the conjugated original finite value. -/
theorem eval (polynomial : CoefficientPolynomial) (point : Canonical) :
    (conjugate polynomial).eval (Basic.conj point) = Basic.conj (polynomial.eval point) :=
  (Dense.Map.map_eval embedding.toFun embedding.map_zero embedding.map_add embedding.map_mul
    polynomial point).symm

end Purelib.Polynomial.Dense.Gaussian.Conjugation

end
