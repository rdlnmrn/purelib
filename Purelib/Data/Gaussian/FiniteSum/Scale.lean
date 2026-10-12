module
import Purelib.Data.Rat.Fraction
public import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Scale

import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Finite operational laws for transcendental CCL programs

This module begins the analytic identification layer without adjoining a
completed non-rational value.  Laws compare finite approximation programs:
from any current indices and any positive displayed rational tolerance they
compute synchronized later indices whose entire displayed tails agree to that
tolerance.

The exponential addition law will be proved here by a finite polynomial
Cauchy-product identity followed by explicit rational remainder bounds.  The
normalization law `exp(0) = 1` is already exact at every finite Horner depth.
-/

namespace Purelib.Data.Gaussian.FiniteSum.Scale

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Rational coordinate scaling commutes with the original finite Gaussian prefix sum. -/
theorem scale_sum (factor : Fraction.Rational) (term : Nat →
  Basic.Canonical) :
    ∀ count,
      Scale.scale factor (FiniteSum.Prefix.sum term count) =
        FiniteSum.Prefix.sum
          (fun index => Scale.scale factor (term index))
          count
  | 0 => by
      apply Basic.ext <;>
        simp only [FiniteSum.Prefix.sum_zero, Scale.scale_re,
          Scale.scale_im, Basic.zero_re, Basic.zero_im] <;> ring1
  | count + 1 => by
      rw [FiniteSum.Prefix.sum_succ, FiniteSum.Prefix.sum_succ,
        ← scale_sum factor term count]
      apply Basic.ext <;>
        simp only [Scale.scale_re,
          Scale.scale_im, Basic.add_re, Basic.add_im] <;> ring1
end Purelib.Data.Gaussian.FiniteSum.Scale

end
