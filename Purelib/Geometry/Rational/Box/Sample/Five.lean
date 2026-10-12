module
public import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data

open Purelib.Geometry

section
@[expose] public section

/-!
# Checked initial root extraction

The initial positive-winding region can contain several roots.  In particular,
its midpoint may be a critical point even when the polynomial is squarefree.
Try its midpoint and four off-centre seeds before using the total extractor.
These seeds are only proposals: the existing finite checker proves strict
containment, winding four, full-line clearance and the requested accuracy.

No Newton-convergence hypothesis or caller search budget is needed.  Failure
of the bounded shortcut retains the original unconditional finite fallback.
The selected root is whichever checked seed succeeds first; no equality with
the old extractor's ordering of independent roots is asserted.
-/

namespace Purelib.Geometry.Rational.Box.Sample.Five

/-- A fixed finite list computed from the region alone. Diagonal seeds avoid the zero derivative at the midpoint of a
symmetric quadratic root region. -/
def seeds (box : Rational.Box) : List
  Gaussian.Basic.Canonical :=
  let x := (box.xLower + box.xUpper) / 2
  let y := (box.yLower + box.yUpper) / 2
  let dx := box.widthX / 4
  let dy := box.widthY / 4
  [⟨x, y⟩, ⟨x + dx, y + dy⟩, ⟨x - dx, y + dy⟩,
    ⟨x - dx, y - dy⟩, ⟨x + dx, y - dy⟩]
end Purelib.Geometry.Rational.Box.Sample.Five

end
