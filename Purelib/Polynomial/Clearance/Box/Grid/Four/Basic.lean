module

import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data.Rat

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

namespace Purelib.Polynomial.Clearance.Box.Grid.Four.Basic

set_option genInjectivity false in
/-- The two selected clear lines and their exact positions in the parent. -/
structure ClearFourGrid (p :
  CoefficientPolynomial) (parent : Box) where
  /-- The retained real coordinate of the vertical cut. -/ xCut : Fraction.Rational
  /-- The retained imaginary coordinate of the horizontal cut. -/ yCut : Fraction.Rational
  /-- The vertical cut lies between the parent's real-coordinate bounds. -/ xInside : parent.xLower ≤ xCut ∧ xCut ≤
    parent.xUpper
  /-- The horizontal cut lies between the parent's imaginary-coordinate bounds. -/ yInside : parent.yLower ≤ yCut ∧ yCut
    ≤ parent.yUpper
  /-- Quantitative clearance along the original parent's vertical cut. -/ verticalClearance :
    Clearance.Box.Line.Basic.VerticalLineClearance p parent xCut
  /-- Quantitative clearance along the original parent's horizontal cut. -/ horizontalClearance :
    Clearance.Box.Line.Basic.HorizontalLineClearance p parent yCut

constructive_injectivity ClearFourGrid

namespace ClearFourGrid

/-- The left half of the retained parent cut by the displayed grid coordinates. -/
def left {p :
  CoefficientPolynomial}
  {parent : Box}
    (grid : ClearFourGrid p parent) : Box :=
  parent.verticalLeft grid.xCut grid.xInside

/-- The right half of the retained parent cut by the displayed grid coordinates. -/
def right {p :
  CoefficientPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : Box :=
  parent.verticalRight grid.xCut grid.xInside

/-- The lower-left child of the retained parent cut by the displayed grid coordinates. -/
def lowerLeft {p :
  CoefficientPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : Box :=
  grid.left.horizontalLower grid.yCut grid.yInside

/-- The upper-left child of the retained parent cut by the displayed grid coordinates. -/
def upperLeft {p :
  CoefficientPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : Box :=
  grid.left.horizontalUpper grid.yCut grid.yInside

/-- The lower-right child of the retained parent cut by the displayed grid coordinates. -/
def lowerRight {p :
  CoefficientPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : Box :=
  grid.right.horizontalLower grid.yCut grid.yInside

/-- The upper-right child of the retained parent cut by the displayed grid coordinates. -/
def upperRight {p :
  CoefficientPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : Box :=
  grid.right.horizontalUpper grid.yCut grid.yInside

/-- The retained grid's left half refines its original parent box. -/
theorem left_refines {p :
  CoefficientPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : grid.left.Refines parent :=
  parent.verticalLeft_refines grid.xCut grid.xInside

/-- The retained grid's right half refines its original parent box. -/
theorem right_refines {p :
  CoefficientPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : grid.right.Refines parent :=
  parent.verticalRight_refines grid.xCut grid.xInside

/-- The retained grid's lower-left child refines its original parent box. -/
theorem lowerLeft_refines {p :
  CoefficientPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : grid.lowerLeft.Refines parent :=
  (grid.left.horizontalLower_refines grid.yCut grid.yInside).trans
    grid.left_refines

/-- The retained grid's upper-left child refines its original parent box. -/
theorem upperLeft_refines {p :
  CoefficientPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : grid.upperLeft.Refines parent :=
  (grid.left.horizontalUpper_refines grid.yCut grid.yInside).trans
    grid.left_refines

/-- The retained grid's lower-right child refines its original parent box. -/
theorem lowerRight_refines {p :
  CoefficientPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : grid.lowerRight.Refines parent :=
  (grid.right.horizontalLower_refines grid.yCut grid.yInside).trans
    grid.right_refines

/-- The retained grid's upper-right child refines its original parent box. -/
theorem upperRight_refines {p :
  CoefficientPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : grid.upperRight.Refines parent :=
  (grid.right.horizontalUpper_refines grid.yCut grid.yInside).trans
    grid.right_refines
end ClearFourGrid
end Purelib.Polynomial.Clearance.Box.Grid.Four.Basic

end
