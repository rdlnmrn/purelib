module
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Grid.Central.Cell
import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Geometry.Rational.Box.Separation
import Purelib.Geometry.Rational.Box.Refinement
import Mathlib.Order.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free eight-cell complement of a central band

A strictly interior rectangle induces a `3 × 3` grid.  The middle cell is
the selected Newton band; the other eight cells inherit quantitative
clearance from the parent boundary and the four globally clear band sides.
-/

namespace Purelib.Polynomial.Clearance.Box.Grid.Central.Cell.ClearCell

/-- Any box strictly inside a complement cell is separated from the removed
center by one strict coordinate inequality. -/
theorem center_separated_from_strictInterior
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {outer center : Box}
    (cell : Clearance.Box.Grid.Central.Cell.ClearCell p outer center) {small : Box}
    (strict : small.StrictInterior cell.box) : center.Separated small := by
  rcases cell.touchesCenter with westTouch | eastTouch | southTouch | northTouch
  · exact Or.inr (Or.inl (strict.right.trans_eq westTouch))
  · exact Or.inl (eastTouch.symm.trans_lt strict.left)
  · exact Or.inr (Or.inr (Or.inr (strict.top.trans_eq southTouch)))
  · exact Or.inr (Or.inr (Or.inl (northTouch.symm.trans_lt strict.bottom)))
end Purelib.Polynomial.Clearance.Box.Grid.Central.Cell.ClearCell

end
