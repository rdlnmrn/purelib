module
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Grid.Four.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Subdivision
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Subdivision

open Purelib.Polynomial.Clearance.Box.Grid.Four.Basic (ClearFourGrid)

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

@[expose] public section

namespace Purelib.Polynomial.Clearance.Box.Grid.Four.Basic.ClearFourGrid
section

/-- A certified four-cell grid splits the parent raw winding into the four ordered child contributions. -/
theorem winding_additive {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) :
    Winding.Box.Basic.quadrupledBoxWinding p parent =
      Winding.Box.Basic.quadrupledBoxWinding p grid.lowerLeft +
      Winding.Box.Basic.quadrupledBoxWinding p grid.upperLeft +
      Winding.Box.Basic.quadrupledBoxWinding p grid.lowerRight +
      Winding.Box.Basic.quadrupledBoxWinding p grid.upperRight := by
  simpa only [ClearFourGrid.left, ClearFourGrid.right,
    ClearFourGrid.lowerLeft, ClearFourGrid.upperLeft,
    ClearFourGrid.lowerRight, ClearFourGrid.upperRight]
    using Winding.Box.Subdivision.quadrupledBoxWinding_four_split p parent grid.xCut grid.yCut
      grid.xInside grid.yInside
end
end Purelib.Polynomial.Clearance.Box.Grid.Four.Basic.ClearFourGrid

end
