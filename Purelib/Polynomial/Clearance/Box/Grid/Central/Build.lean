module
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Lines
public import Purelib.Polynomial.Clearance.Box.Grid.Central.Cell
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Refinement

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

namespace Purelib.Polynomial.Clearance.Box.Grid.Central.Build

/-- Construct a clear complement cell from its geometry, four ambient line certificates and retained center-side
contact.

Each line certificate is restricted to the same child box; their minimum supplies its boundary clearance without a new
scan. -/
def makeCell
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {outer center box : Box}
    (refines : box.Refines outer) (proper : box.Proper)
    (left : Clearance.Box.Line.Basic.VerticalLineClearance p outer box.xLower)
    (right : Clearance.Box.Line.Basic.VerticalLineClearance p outer box.xUpper)
    (bottom : Clearance.Box.Line.Basic.HorizontalLineClearance p outer box.yLower)
    (top : Clearance.Box.Line.Basic.HorizontalLineClearance p outer box.yUpper)
    (touches :
      box.xUpper = center.xLower ∨ box.xLower = center.xUpper ∨
        box.yUpper = center.yLower ∨ box.yLower = center.yUpper) :
    Clearance.Box.Grid.Central.Cell.ClearCell p outer center where
  box := box
  refines := refines
  proper := proper
  clearance := Clearance.Box.Boundary.Lines.boundaryOfLines
    (left.restrict refines) (right.restrict refines)
    (bottom.restrict refines) (top.restrict refines)
  touchesCenter := touches
end Purelib.Polynomial.Clearance.Box.Grid.Central.Build

end
