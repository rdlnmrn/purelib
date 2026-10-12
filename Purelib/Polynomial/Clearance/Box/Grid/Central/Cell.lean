module

import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction
meta import Purelib.Elab.ConstructiveInjectivity

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

namespace Purelib.Polynomial.Clearance.Box.Grid.Central.Cell

set_option genInjectivity false in
/-- One clear complement cell, including a side on which it touches the
removed center. -/
structure ClearCell
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (outer center : Box) where
  /-- The retained complement-cell rectangle. -/ box : Box
  /-- The cell lies within its original outer box. -/ refines : box.Refines outer
  /-- Both cell coordinate intervals have positive width. -/ proper : box.Proper
  /-- The retained quantitative polynomial clearance on this cell's boundary. -/ clearance :
    Clearance.Box.Boundary.Basic.BoundaryClearance p box
  /-- A displayed cell side coincides with an oppositely oriented side of the removed center. -/ touchesCenter :
    box.xUpper = center.xLower ∨ box.xLower = center.xUpper ∨
      box.yUpper = center.yLower ∨ box.yLower = center.yUpper

constructive_injectivity ClearCell

end Purelib.Polynomial.Clearance.Box.Grid.Central.Cell

end
