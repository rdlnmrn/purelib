module
public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Aggregate horizontal quartic sample certificates

This module connects the exact rational samples emitted by the standalone
Python generator to the 64 canonical centered edges of the prepared
A-forward horizontal connector, then aggregates the local error bounds by
finite Cauchy--Schwarz.
-/

namespace Purelib.Data.Gaussian.Dyadic.Grid

/-- Adjacent natural-scale rational parameters give the exact positive dyadic
displacement on the negated horizontal grid.

With n = m + 1, subtracting the point at -n/32 from the point at -m/32 yields real
displacement 1/32 and zero imaginary displacement. -/
theorem negativeHorizontalStep
    (n m : Rational) (adjacent : n = m + 1) :
    Gaussian.Basic.point (-(m / 32)) (-1 / 2) - Gaussian.Basic.point (-(n / 32)) (-1 / 2) =
      Gaussian.Basic.point (1 / 32) 0 := by
  apply Gaussian.Basic.ext
  · simp only [Gaussian.Basic.sub_re, Gaussian.Basic.point]
    simp only [Field.div_eq_mul_inv_direct]
    rw [adjacent]
    ring1
  · simp only [Gaussian.Basic.sub_im, Gaussian.Basic.point]
    ring1

/-- Adjacent rational parameters give exact real displacement one thirty-second on the
horizontal dyadic grid. -/
theorem positiveHorizontalStep
    (n m : Rational) (adjacent : n = m + 1) :
    Gaussian.Basic.point (n / 32) (-1 / 2) - Gaussian.Basic.point (m / 32) (-1 / 2) =
      Gaussian.Basic.point (1 / 32) 0 := by
  apply Gaussian.Basic.ext
  · simp only [Gaussian.Basic.sub_re, Gaussian.Basic.point]
    simp only [Field.div_eq_mul_inv_direct]
    rw [adjacent]
    ring1
  · simp only [Gaussian.Basic.sub_im, Gaussian.Basic.point]
    ring1
end Purelib.Data.Gaussian.Dyadic.Grid

end
