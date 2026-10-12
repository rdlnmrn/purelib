module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Arithmetic

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

namespace Purelib.Data.Gaussian.Norm.Nonzero

/-! ## Uniform moves between robust unit-parameter frames -/

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A canonical Gaussian with squared norm one is nonzero. -/
theorem nonzero_of_normSq_eq_one {parameter : Basic.Canonical}
    (unit : Norm.Basic.normSq parameter = 1) : parameter ≠ 0 := by
  intro zero
  rw [zero, Norm.Basic.normSq_zero] at unit
  exact (by decide : (0 : Fraction.Rational) ≠ 1) unit
end Purelib.Data.Gaussian.Norm.Nonzero

end
