module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Division
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Scale

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Gaussian

section
@[expose] public section

/-!
# Low-to-high finite polynomials for transcendental identities

This is a deliberately small, executable polynomial kernel.  A polynomial is
only a displayed finite list of rational coefficients, stored from constant
term upward.  It exists to prove finite Taylor identities without importing a
sparse-polynomial or formal-power-series API.
-/

namespace Purelib.Geometry.Projective.Homography.Cayley.Basic

/-- Factor the difference of two scaled Cayley coordinates.

With both affine denominators nonzero, the difference is twice the scaled input difference divided by their denominator
product. -/
theorem scaledReduced_sub_scaledReduced (factor x y :
  Data.Gaussian.Basic.Canonical)
    (xDenominatorNonzero : factor * x + 1 ≠ 0)
    (yDenominatorNonzero : factor * y + 1 ≠ 0) :
    (factor * x - 1) / (factor * x + 1) -
        (factor * y - 1) / (factor * y + 1) =
      Scale.scale 2 (factor * (x - y)) /
        ((factor * x + 1) * (factor * y + 1)) := by
  have productNonzero :=
    Data.Gaussian.Field.mul_ne_zero_direct
      xDenominatorNonzero yDenominatorNonzero
  apply Data.Gaussian.Field.mul_right_cancel_of_ne
    productNonzero
  calc
    ((factor * x - 1) / (factor * x + 1) -
          (factor * y - 1) / (factor * y + 1)) *
          ((factor * x + 1) * (factor * y + 1)) =
        (((factor * x - 1) / (factor * x + 1)) *
            (factor * x + 1)) * (factor * y + 1) -
          (((factor * y - 1) / (factor * y + 1)) *
            (factor * y + 1)) * (factor * x + 1) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1
    _ = (factor * x - 1) * (factor * y + 1) -
          (factor * y - 1) * (factor * x + 1) := by
      rw [Division.gaussian_div_mul_cancel _ _ xDenominatorNonzero,
        Division.gaussian_div_mul_cancel _ _ yDenominatorNonzero]
    _ = Scale.scale 2 (factor * (x - y)) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Scale.scale_re,
          Scale.scale_im, Basic.add_re, Basic.add_im, Basic.sub_re,
          Basic.sub_im, Basic.mul_re, Basic.mul_im, Basic.one_re, Basic.one_im] <;> ring1
    _ = (Scale.scale 2 (factor * (x - y)) /
          ((factor * x + 1) * (factor * y + 1))) *
            ((factor * x + 1) * (factor * y + 1)) :=
      (Division.gaussian_div_mul_cancel _ _ productNonzero).symm

/-- Exact difference between an asynchronously sampled scaled quotient and a diagonal reduced-coordinate sample. -/
theorem asynchronousScaledReduced_sub_scaledReduced
    (factor x y z : Data.Gaussian.Basic.Canonical)
    (yDenominatorNonzero : factor * y + 1 ≠ 0)
    (zDenominatorNonzero : factor * z + 1 ≠ 0) :
    (factor * x - 1) / (factor * y + 1) -
        (factor * z - 1) / (factor * z + 1) =
      (factor * factor * z * (x - y) +
          factor * ((x - z) + (y - z))) /
        ((factor * y + 1) * (factor * z + 1)) := by
  have productNonzero :=
    Data.Gaussian.Field.mul_ne_zero_direct
      yDenominatorNonzero zDenominatorNonzero
  apply Data.Gaussian.Field.mul_right_cancel_of_ne
    productNonzero
  calc
    ((factor * x - 1) / (factor * y + 1) -
          (factor * z - 1) / (factor * z + 1)) *
          ((factor * y + 1) * (factor * z + 1)) =
        (((factor * x - 1) / (factor * y + 1)) *
            (factor * y + 1)) * (factor * z + 1) -
          (((factor * z - 1) / (factor * z + 1)) *
            (factor * z + 1)) * (factor * y + 1) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1
    _ = (factor * x - 1) * (factor * z + 1) -
          (factor * z - 1) * (factor * y + 1) := by
      rw [Division.gaussian_div_mul_cancel _ _ yDenominatorNonzero,
        Division.gaussian_div_mul_cancel _ _ zDenominatorNonzero]
    _ = factor * factor * z * (x - y) +
          factor * ((x - z) + (y - z)) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im,
          Basic.one_re, Basic.one_im] <;> ring1
    _ = ((factor * factor * z * (x - y) +
          factor * ((x - z) + (y - z))) /
            ((factor * y + 1) * (factor * z + 1))) *
              ((factor * y + 1) * (factor * z + 1)) :=
      (Division.gaussian_div_mul_cancel _ _ productNonzero).symm
end Purelib.Geometry.Projective.Homography.Cayley.Basic

end
