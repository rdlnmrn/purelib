module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic

open Purelib.Data.Rat.Fraction

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

namespace Purelib.Data.Gaussian.Coordinates.Rotation

open Purelib.Data.Gaussian

/-- Multiplication by one minus the imaginary unit sends the real coordinate to the sum
of the original coordinates. -/
private theorem diagonalRotation_real (point : Canonical) :
    (⟨1, -1⟩ * point : Canonical).re = point.re + point.im := by
  change (1 : Rational) * point.re - (-1) * point.im =
    point.re + point.im
  ring1
end Purelib.Data.Gaussian.Coordinates.Rotation

end
