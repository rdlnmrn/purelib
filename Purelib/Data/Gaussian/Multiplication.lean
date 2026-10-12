module
public import Purelib.Data.Gaussian.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Basic

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

namespace Purelib.Data.Gaussian.Multiplication

/-- Split a difference of Gaussian products into two one-factor differences.

For four canonical Gaussian rationals, changing both factors is the sum of the left-factor change against the later
right factor and the right-factor change against the earlier left factor. -/
public theorem product_difference_identity
    (xLater xEarlier yLater yEarlier : Canonical) :
    xLater * yLater - xEarlier * yEarlier =
      (xLater - xEarlier) * yLater +
        xEarlier * (yLater - yEarlier) := by
  apply Basic.ext <;>
    simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im] <;> ring1

end Purelib.Data.Gaussian.Multiplication

end
