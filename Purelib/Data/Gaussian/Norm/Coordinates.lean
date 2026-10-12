module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Automatic positive-real charting for a CCL logarithm

The input certificate supplies a displayed positive rational lower bound for
the real coordinate of every candidate at the current finite state.  One
explicit refinement makes the current ball small relative to that bound.
The rational real coordinate of the refined ball centre is then normalized
by a bounded dyadic scan, and every explicitly possible candidate at the
refined state is proved to land in the overlapping local logarithm chart.
The geometric ball may of course contain irrelevant non-real points; the
separate positive-real certificate excludes those from the process semantics.

This is branch data and finite error accounting only.  It neither selects a
point common to all refinements nor asserts a completed logarithm.  Its
purpose is to make positive-real logarithm an automatic CCL-to-CCL operator
on this certified domain: chart preparation, local logarithm, the finite
`log 2` correction, and every correction addition remain arithmetic CCL
names.
-/

namespace Purelib.Data.Gaussian.Norm.Coordinates

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The squared real-coordinate displacement is at most the full Gaussian squared displacement. -/
public theorem re_sub_sq_le_normSq (value center : Basic.Canonical) :
    (value.re - center.re) ^ 2 ≤ Basic.Canonical.normSq (value - center) := by
  rw [Basic.Canonical.normSq]
  simp only [Basic.sub_re, Basic.sub_im]
  rw [← pow_two, ← pow_two]
  exact le_add_of_nonneg_right
    (Fraction.Order.Arithmetic.sq_nonneg_direct (value.im - center.im))

end Purelib.Data.Gaussian.Norm.Coordinates

end
