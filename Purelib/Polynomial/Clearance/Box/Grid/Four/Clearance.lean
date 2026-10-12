module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Lines
public import Purelib.Polynomial.Clearance.Box.Grid.Four.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic

open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)
open Purelib.Polynomial.Clearance.Box.Line.Basic (HorizontalLineClearance VerticalLineClearance)

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

/-- Parent boundary clearance and the two selected clear lines give all four
child boundary certificates. -/
def childClearances {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {parent : Box}
    (grid : Clearance.Box.Grid.Four.Basic.ClearFourGrid p parent) (parentClear :
      BoundaryClearance p parent) :
    BoundaryClearance p grid.lowerLeft ×
      BoundaryClearance p grid.upperLeft ×
      BoundaryClearance p grid.lowerRight ×
      BoundaryClearance p grid.upperRight :=
  let leftParent := Clearance.Box.Boundary.Lines.leftOfBoundary parentClear
  let rightParent := Clearance.Box.Boundary.Lines.rightOfBoundary parentClear
  let bottomParent := Clearance.Box.Boundary.Lines.bottomOfBoundary parentClear
  let topParent := Clearance.Box.Boundary.Lines.topOfBoundary parentClear
  let lowerLeftClear := Clearance.Box.Boundary.Lines.boundaryOfLines
    (VerticalLineClearance.restrict (small := grid.lowerLeft)
      leftParent grid.lowerLeft_refines)
    (VerticalLineClearance.restrict (small := grid.lowerLeft)
      grid.verticalClearance grid.lowerLeft_refines)
    (HorizontalLineClearance.restrict (small := grid.lowerLeft)
      bottomParent grid.lowerLeft_refines)
    (HorizontalLineClearance.restrict (small := grid.lowerLeft)
      grid.horizontalClearance grid.lowerLeft_refines)
  let upperLeftClear := Clearance.Box.Boundary.Lines.boundaryOfLines
    (VerticalLineClearance.restrict (small := grid.upperLeft)
      leftParent grid.upperLeft_refines)
    (VerticalLineClearance.restrict (small := grid.upperLeft)
      grid.verticalClearance grid.upperLeft_refines)
    (HorizontalLineClearance.restrict (small := grid.upperLeft)
      grid.horizontalClearance grid.upperLeft_refines)
    (HorizontalLineClearance.restrict (small := grid.upperLeft)
      topParent grid.upperLeft_refines)
  let lowerRightClear := Clearance.Box.Boundary.Lines.boundaryOfLines
    (VerticalLineClearance.restrict (small := grid.lowerRight)
      grid.verticalClearance grid.lowerRight_refines)
    (VerticalLineClearance.restrict (small := grid.lowerRight)
      rightParent grid.lowerRight_refines)
    (HorizontalLineClearance.restrict (small := grid.lowerRight)
      bottomParent grid.lowerRight_refines)
    (HorizontalLineClearance.restrict (small := grid.lowerRight)
      grid.horizontalClearance grid.lowerRight_refines)
  let upperRightClear := Clearance.Box.Boundary.Lines.boundaryOfLines
    (VerticalLineClearance.restrict (small := grid.upperRight)
      grid.verticalClearance grid.upperRight_refines)
    (VerticalLineClearance.restrict (small := grid.upperRight)
      rightParent grid.upperRight_refines)
    (HorizontalLineClearance.restrict (small := grid.upperRight)
      grid.horizontalClearance grid.upperRight_refines)
    (HorizontalLineClearance.restrict (small := grid.upperRight)
      topParent grid.upperRight_refines)
  (lowerLeftClear, upperLeftClear, lowerRightClear, upperRightClear)

end
end Purelib.Polynomial.Clearance.Box.Grid.Four.Basic.ClearFourGrid

end
