module

import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Multiplication.Basic

/-!
# Original dense products over a ring with zero divisors

The original coefficient fold now operates on the same square-zero quadratic
coordinates without requiring a field instance.
-/

namespace TestPurelib.Polynomial.Dense.Multiplication

open Purelib.Algebra.Quadratic
open Purelib.Polynomial.Dense.Basic

/-- The original quadratic ring with a square-zero generator. -/
private abbrev Dual := Pair Purelib.Data.Gaussian.Basic.Canonical 0

/-- The original nonzero nilpotent scalar. -/
private def epsilon : Dual := Pair.generator

/-- The same nonzero scalar has a zero square. -/
private theorem epsilon_nonzero : epsilon ≠ 0 := by decide +kernel

/-- Multiplying its two constant coefficient tables gives the actual zero product. -/
private theorem nilpotent_product :
    ((⟨[epsilon]⟩ : DensePolynomial Dual) * ⟨[epsilon]⟩).isZero = true := by decide +kernel

/-- The two monic factors retain their exact quadratic product coefficient table. -/
private theorem opposite_factors :
    ((⟨[1, epsilon]⟩ : DensePolynomial Dual) * ⟨[1, -epsilon]⟩).coeffs = [1, 0, 0] := by decide +kernel

/-- Original multiplication evaluation applies at every point of the same zero-divisor ring. -/
private theorem product_readback (point : Dual) :
    ((⟨[1, epsilon]⟩ : DensePolynomial Dual) * ⟨[1, -epsilon]⟩).eval point =
      (⟨[1, epsilon]⟩ : DensePolynomial Dual).eval point *
        (⟨[1, -epsilon]⟩ : DensePolynomial Dual).eval point :=
  DensePolynomial.eval_mul _ _ point

end TestPurelib.Polynomial.Dense.Multiplication
