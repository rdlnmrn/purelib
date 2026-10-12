module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Components

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial.Clearance

open Purelib.Polynomial.Dense.Gaussian.Basic

open Purelib.Polynomial.Dense.Gaussian.Path

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Polynomial.Path.Clearance.Nonzero
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- A certified clearance for the path components excludes a zero of the Gaussian polynomial.

At each parameter in the retained interval, the real and imaginary evaluations cannot vanish simultaneously. -/
private theorem path_value_ne_zero_of_certificate
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
      Data.Gaussian.Basic.Canonical)
    {interval : Data.Rat.Interval.Bounds}
    (certificate : Pair.Basic.Certificate
      (Components.pathReal p origin direction)
      (Components.pathImag p origin direction) interval)
    {time : Fraction.Rational} (inside : interval.Contains time) :
    p.eval (Affine.line origin direction time) ≠ 0 := by
  intro zero
  have pair := certificate.eval_ne_zero inside
  rw [Components.eval_pathReal,
    Components.eval_pathImag, zero] at pair
  simp only [Data.Gaussian.Basic.zero_re, Data.Gaussian.Basic.zero_im] at pair
  exact pair.elim (fun impossible => impossible rfl)
    (fun impossible => impossible rfl)
end Purelib.Geometry.Polynomial.Path.Clearance.Nonzero

end
