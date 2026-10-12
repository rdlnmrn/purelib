module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Gaussian.Constants
public import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
public import Purelib.Polynomial.Dense.Multiplication

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Linear.Affine

/-- Executable affine linear program `s(Z-c)`. -/
def affineCoordinate (s c : Gaussian.Basic.Canonical) :
  (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Dense.Gaussian.Constants.gaussianConstant s * Dense.Gaussian.Linear.Translated.translatedCoordinate c

/-- Exact two-coefficient representation of the affine program. -/
theorem affineCoordinate_eq_linear
    {s : Gaussian.Basic.Canonical} (slopeNonzero : s ≠ 0) (c : Gaussian.Basic.Canonical) :
    affineCoordinate s c = ⟨[s, -(s * c)]⟩ := by
  rw [affineCoordinate, Dense.Gaussian.Constants.gaussianConstant]
  change DensePolynomial.mulPolynomial (DensePolynomial.constant s)
    (Dense.Gaussian.Linear.Translated.translatedCoordinate c) =
    ⟨[s, -(s * c)]⟩
  rw [DensePolynomial.mulPolynomial]
  simp only [DensePolynomial.constant_coeffs, List.foldl_cons, List.foldl_nil]
  rw [DensePolynomial.shift_zero, DensePolynomial.zero_add_normalize,
    DensePolynomial.normalize_scale]
  apply DensePolynomial.ext
  rw [DensePolynomial.scale_coeffs_of_ne_zero slopeNonzero]
  simp only [Dense.Gaussian.Linear.Translated.translatedCoordinate, DensePolynomial.normalize_coeffs,
    List.dropWhile]
  apply congrArg₂ List.cons (by
    exact Gaussian.Basic.mul_one s)
  apply congrArg₂ List.cons (by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im] <;>
      ring1) rfl

/-- The affine polynomial evaluates to the slope times the displacement from its center. -/
@[simp] theorem affineCoordinate_eval (s c z :
  Gaussian.Basic.Canonical) :
    (affineCoordinate s c).eval z = s * (z - c) := by
  rw [affineCoordinate, DensePolynomial.eval_mul,
    Dense.Gaussian.Constants.gaussianConstant_eval,
    Dense.Gaussian.Linear.Translated.translatedCoordinate_eval]
end Purelib.Polynomial.Dense.Gaussian.Linear.Affine

end
