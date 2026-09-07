import RFAP.Geometry.BoxClearance
import RFAP.Isolation.SafeCandidates
import mathlib.RFAP.ConstructiveSylvesterBezout

/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

namespace RFAP.AxisSafeCuts

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Box := RFAP.Boxes.Box

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.PathPolynomial
open RFAP.Winding
open RFAP.PathClearance
open RFAP.BoxClearance
open RFAP.SafeCandidates

def verticalPathReal (p : GaussianPolynomial) (x : Coordinate) : Polynomial :=
  pathReal p (verticalBase x) verticalDirection

def verticalPathImag (p : GaussianPolynomial) (x : Coordinate) : Polynomial :=
  pathImag p (verticalBase x) verticalDirection

def horizontalPathReal (p : GaussianPolynomial) (y : Coordinate) : Polynomial :=
  pathReal p (horizontalBase y) horizontalDirection

def horizontalPathImag (p : GaussianPolynomial) (y : Coordinate) : Polynomial :=
  pathImag p (horizontalBase y) horizontalDirection

/-- Finite elimination data consumed by the two bounded axis searches. -/
structure AxisEliminationCertificate
    (p : GaussianPolynomial) (degreeBound : Nat) where
  vertical : Polynomial
  horizontal : Polynomial
  vertical_nonzero : vertical.isZero = false
  horizontal_nonzero : horizontal.isZero = false
  vertical_degree : vertical.natDegree ≤ degreeBound
  horizontal_degree : horizontal.natDegree ≤ degreeBound
  vertical_coprime : ∀ x : Coordinate, vertical.eval x ≠ 0 →
    CoprimeCertificate (verticalPathReal p x) (verticalPathImag p x)
  horizontal_coprime : ∀ y : Coordinate, horizontal.eval y ≠ 0 →
    CoprimeCertificate (horizontalPathReal p y) (horizontalPathImag p y)

/-- The actual finite degree bound of the two separated-Sylvester
eliminants. -/
def separatedEliminationDegree (p : GaussianPolynomial) : Nat :=
  max (RFAP.ConstructiveSylvesterBezout.scalarEliminant p).natDegree
    (RFAP.ConstructiveSylvesterBezout.horizontalEliminant p).natDegree

/-- Closed constructive axis-elimination data from the two fraction-free
separated Sylvester inverses. -/
def separatedAxisEliminationCertificate (p : GaussianPolynomial)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree) :
    AxisEliminationCertificate p (separatedEliminationDegree p) where
  vertical := RFAP.ConstructiveSylvesterBezout.scalarEliminant p
  horizontal := RFAP.ConstructiveSylvesterBezout.horizontalEliminant p
  vertical_nonzero :=
    RFAP.ConstructiveSylvesterBezout.scalarEliminant_nonzero p nonzero
  horizontal_nonzero :=
    RFAP.ConstructiveSylvesterBezout.horizontalEliminant_nonzero p nonzero
  vertical_degree := le_max_left _ _
  horizontal_degree := le_max_right _ _
  vertical_coprime := by
    intro x eliminantNonzero
    simpa only [verticalPathReal, verticalPathImag] using
      RFAP.ConstructiveSylvesterBezout.verticalCoprimeCertificate p nonzero
        degreePositive x eliminantNonzero
  horizontal_coprime := by
    intro y eliminantNonzero
    simpa only [horizontalPathReal, horizontalPathImag] using
      RFAP.ConstructiveSylvesterBezout.horizontalCoprimeCertificate p nonzero
        degreePositive y eliminantNonzero

def verticalSafeCoordinate {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) (box : Box)
    (proper : box.Proper) : Coordinate :=
  centralSearchValue elimination.vertical degreeBound proper.1
    elimination.vertical_nonzero elimination.vertical_degree

def horizontalSafeCoordinate {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) (box : Box)
    (proper : box.Proper) : Coordinate :=
  centralSearchValue elimination.horizontal degreeBound proper.2
    elimination.horizontal_nonzero elimination.horizontal_degree

theorem verticalSafeCoordinate_spec
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) (box : Box)
    (proper : box.Proper) :
    elimination.vertical.eval
        (verticalSafeCoordinate elimination box proper) ≠ 0 ∧
      box.xLower < verticalSafeCoordinate elimination box proper ∧
      verticalSafeCoordinate elimination box proper < box.xUpper :=
  centralSearchValue_spec elimination.vertical degreeBound proper.1
    elimination.vertical_nonzero elimination.vertical_degree

theorem horizontalSafeCoordinate_spec
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) (box : Box)
    (proper : box.Proper) :
    elimination.horizontal.eval
        (horizontalSafeCoordinate elimination box proper) ≠ 0 ∧
      box.yLower < horizontalSafeCoordinate elimination box proper ∧
      horizontalSafeCoordinate elimination box proper < box.yUpper :=
  centralSearchValue_spec elimination.horizontal degreeBound proper.2
    elimination.horizontal_nonzero elimination.horizontal_degree

theorem verticalSafeCoordinate_contraction
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) (box : Box)
    (proper : box.Proper) :
    verticalSafeCoordinate elimination box proper - box.xLower <
        (2 / 3 : Coordinate) * box.widthX ∧
      box.xUpper - verticalSafeCoordinate elimination box proper <
        (2 / 3 : Coordinate) * box.widthX := by
  simpa only [verticalSafeCoordinate, RFAP.Boxes.Box.widthX] using
    centralSearchValue_contraction elimination.vertical degreeBound proper.1
    elimination.vertical_nonzero elimination.vertical_degree

theorem horizontalSafeCoordinate_contraction
    {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) (box : Box)
    (proper : box.Proper) :
    horizontalSafeCoordinate elimination box proper - box.yLower <
        (2 / 3 : Coordinate) * box.widthY ∧
      box.yUpper - horizontalSafeCoordinate elimination box proper <
        (2 / 3 : Coordinate) * box.widthY := by
  simpa only [horizontalSafeCoordinate, RFAP.Boxes.Box.widthY] using
    centralSearchValue_contraction elimination.horizontal degreeBound proper.2
    elimination.horizontal_nonzero elimination.horizontal_degree

/-- The two selected clear lines and their exact positions in the parent. -/
structure ClearFourGrid (p : GaussianPolynomial) (parent : Box) where
  xCut : Coordinate
  yCut : Coordinate
  xInside : parent.xLower ≤ xCut ∧ xCut ≤ parent.xUpper
  yInside : parent.yLower ≤ yCut ∧ yCut ≤ parent.yUpper
  verticalClearance : VerticalLineClearance p parent xCut
  horizontalClearance : HorizontalLineClearance p parent yCut

namespace ClearFourGrid

def left {p : GaussianPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : Box :=
  parent.verticalLeft grid.xCut grid.xInside

def right {p : GaussianPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : Box :=
  parent.verticalRight grid.xCut grid.xInside

def lowerLeft {p : GaussianPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : Box :=
  grid.left.horizontalLower grid.yCut grid.yInside

def upperLeft {p : GaussianPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : Box :=
  grid.left.horizontalUpper grid.yCut grid.yInside

def lowerRight {p : GaussianPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : Box :=
  grid.right.horizontalLower grid.yCut grid.yInside

def upperRight {p : GaussianPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : Box :=
  grid.right.horizontalUpper grid.yCut grid.yInside

theorem left_refines {p : GaussianPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : grid.left.Refines parent :=
  parent.verticalLeft_refines grid.xCut grid.xInside

theorem right_refines {p : GaussianPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : grid.right.Refines parent :=
  parent.verticalRight_refines grid.xCut grid.xInside

theorem lowerLeft_refines {p : GaussianPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : grid.lowerLeft.Refines parent :=
  (grid.left.horizontalLower_refines grid.yCut grid.yInside).trans
    grid.left_refines

theorem upperLeft_refines {p : GaussianPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : grid.upperLeft.Refines parent :=
  (grid.left.horizontalUpper_refines grid.yCut grid.yInside).trans
    grid.left_refines

theorem lowerRight_refines {p : GaussianPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : grid.lowerRight.Refines parent :=
  (grid.right.horizontalLower_refines grid.yCut grid.yInside).trans
    grid.right_refines

theorem upperRight_refines {p : GaussianPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) : grid.upperRight.Refines parent :=
  (grid.right.horizontalUpper_refines grid.yCut grid.yInside).trans
    grid.right_refines

theorem winding_additive {p : GaussianPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) :
    quadrupledBoxWinding p parent =
      quadrupledBoxWinding p grid.lowerLeft +
      quadrupledBoxWinding p grid.upperLeft +
      quadrupledBoxWinding p grid.lowerRight +
      quadrupledBoxWinding p grid.upperRight := by
  simpa only [left, right, lowerLeft, upperLeft, lowerRight, upperRight]
    using quadrupledBoxWinding_four_split p parent grid.xCut grid.yCut
      grid.xInside grid.yInside

/-- Parent boundary clearance and the two selected clear lines give all four
child boundary certificates. -/
def childClearances {p : GaussianPolynomial} {parent : Box}
    (grid : ClearFourGrid p parent) (parentClear : BoundaryClearance p parent) :
    BoundaryClearance p grid.lowerLeft ×
      BoundaryClearance p grid.upperLeft ×
      BoundaryClearance p grid.lowerRight ×
      BoundaryClearance p grid.upperRight :=
  let leftParent := leftOfBoundary parentClear
  let rightParent := rightOfBoundary parentClear
  let bottomParent := bottomOfBoundary parentClear
  let topParent := topOfBoundary parentClear
  let lowerLeftClear := boundaryOfLines
    (VerticalLineClearance.restrict (small := grid.lowerLeft)
      leftParent grid.lowerLeft_refines)
    (VerticalLineClearance.restrict (small := grid.lowerLeft)
      grid.verticalClearance grid.lowerLeft_refines)
    (HorizontalLineClearance.restrict (small := grid.lowerLeft)
      bottomParent grid.lowerLeft_refines)
    (HorizontalLineClearance.restrict (small := grid.lowerLeft)
      grid.horizontalClearance grid.lowerLeft_refines)
  let upperLeftClear := boundaryOfLines
    (VerticalLineClearance.restrict (small := grid.upperLeft)
      leftParent grid.upperLeft_refines)
    (VerticalLineClearance.restrict (small := grid.upperLeft)
      grid.verticalClearance grid.upperLeft_refines)
    (HorizontalLineClearance.restrict (small := grid.upperLeft)
      grid.horizontalClearance grid.upperLeft_refines)
    (HorizontalLineClearance.restrict (small := grid.upperLeft)
      topParent grid.upperLeft_refines)
  let lowerRightClear := boundaryOfLines
    (VerticalLineClearance.restrict (small := grid.lowerRight)
      grid.verticalClearance grid.lowerRight_refines)
    (VerticalLineClearance.restrict (small := grid.lowerRight)
      rightParent grid.lowerRight_refines)
    (HorizontalLineClearance.restrict (small := grid.lowerRight)
      bottomParent grid.lowerRight_refines)
    (HorizontalLineClearance.restrict (small := grid.lowerRight)
      grid.horizontalClearance grid.lowerRight_refines)
  let upperRightClear := boundaryOfLines
    (VerticalLineClearance.restrict (small := grid.upperRight)
      grid.verticalClearance grid.upperRight_refines)
    (VerticalLineClearance.restrict (small := grid.upperRight)
      rightParent grid.upperRight_refines)
    (HorizontalLineClearance.restrict (small := grid.upperRight)
      grid.horizontalClearance grid.upperRight_refines)
    (HorizontalLineClearance.restrict (small := grid.upperRight)
      topParent grid.upperRight_refines)
  (lowerLeftClear, upperLeftClear, lowerRightClear, upperRightClear)

end ClearFourGrid

/-- Execute both bounded searches and obtain the two quantitative clear lines. -/
def buildClearFourGrid {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) (parent : Box)
    (proper : parent.Proper) : ClearFourGrid p parent := by
  let xCut := verticalSafeCoordinate elimination parent proper
  let yCut := horizontalSafeCoordinate elimination parent proper
  have xSpec := verticalSafeCoordinate_spec elimination parent proper
  have ySpec := horizontalSafeCoordinate_spec elimination parent proper
  let verticalCoprime := elimination.vertical_coprime xCut xSpec.1
  let horizontalCoprime := elimination.horizontal_coprime yCut ySpec.1
  exact
    { xCut := xCut
      yCut := yCut
      xInside := ⟨xSpec.2.1.le, xSpec.2.2.le⟩
      yInside := ⟨ySpec.2.1.le, ySpec.2.2.le⟩
      verticalClearance := by
        simpa only [verticalPathReal, verticalPathImag] using
          verticalOfCoprime p parent xCut verticalCoprime
      horizontalClearance := by
        simpa only [horizontalPathReal, horizontalPathImag] using
          horizontalOfCoprime p parent yCut horizontalCoprime }

end RFAP.AxisSafeCuts
