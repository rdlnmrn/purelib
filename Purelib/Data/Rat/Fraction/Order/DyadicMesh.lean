module
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# The dyadic grid of the second prepared quartic connector cell

This module caches the nine Purelib.Data.Gaussian-rational radicands of the second outer
connector cell on its depth-three dyadic mesh.  A common fine unit keeps the
endpoint evaluations and all eight squared displacements constructive and
small enough to elaborate at the ordinary limits.
-/

namespace Purelib.Data.Rat.Fraction.Order.DyadicMesh

open Purelib.Data.Rat in
/-- The squared spacing of successive eighth-mesh parameters is the square of one eighth. -/
public theorem adjacentParameterSquare (k : Fraction.Rational) :
    (k / 8 - (k + 1) / 8) ^ 2 = (0 - 1 / 8 : Fraction.Rational) ^ 2 := by
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  ring1

end Purelib.Data.Rat.Fraction.Order.DyadicMesh

end

section
@[expose] public section

/-!
# Analytic and grid data for the third prepared quartic connector cell

The third outer horizontal cell retains the terminal box of the second cell.
Its preparation estimate uses one certified leaf of the finite radicand scan,
and its depth-three grid uses reduced rational representatives for the exact
quadratic boundary checks.
-/

namespace Purelib.Data.Rat.Fraction.Order.DyadicMesh

open Purelib.Data.Rat in
/-- Every pair of successive eighth-mesh parameters has the same squared spacing as zero and one eighth. -/
private theorem thirdAdjacentParameterSquareRaw (k :
  Fraction.Rational) :
    (k / 8 - (k + 1) / 8) ^ 2 = (0 - 1 / 8 : Fraction.Rational) ^ 2 := by
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  ring1
end Purelib.Data.Rat.Fraction.Order.DyadicMesh

end
