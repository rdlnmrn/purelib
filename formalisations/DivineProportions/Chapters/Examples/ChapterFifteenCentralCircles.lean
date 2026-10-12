module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Conics.Circle.Finite.Display
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Finite.Grid
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Algebra.Field.Finite.Eleven
public import Purelib.Algebra.Field.Finite.Thirteen
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

section
@[expose] public section

/-!
# Divine Proportions, Example 15.2 and Exercise 15.3

The two source figures are retained as literal finite coordinate grids.  Their
entries are checked against central quadrance, and filtering the displayed
points by a quadrance label gives the printed circle counts.  These are finite
display certificates: they do not assert that either coordinate list globally
enumerates an ambient field carrier.
-/

namespace formalisations.DivineProportions.Chapters.Examples

namespace ChapterFifteenCentralCircles

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
namespace ExampleFifteenTwo

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Plane.Point in
/-- The displayed origin. -/
def origin : Purelib.Geometry.Plane.Point Eleven.Element := ⟨0, 0⟩

section
open Purelib.Algebra.Field.Finite
/-- Figure 15.1's horizontal coordinate labels, from `-5` through `5`. -/
def xCoordinates : List Eleven.Element :=
  [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5]

/-- Figure 15.1's vertical coordinate labels, from `5` through `-5`. -/
def yCoordinates : List Eleven.Element :=
  [5, 4, 3, 2, 1, 0, -1, -2, -3, -4, -5]

end

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Plane.Point in
open Purelib.Geometry.Plane.Point.Finite in
/-- The 121 literal point positions in Figure 15.1, retained row by row. -/
def displayedPointRows : List (List (Purelib.Geometry.Plane.Point Eleven.Element)) :=
  Grid.pointRows xCoordinates yCoordinates

section
open Purelib.Algebra.Field.Finite
/-- The eleven rows of central quadrances printed in Figure 15.1. -/
def displayedValueRows : List (List Eleven.Element) :=
  [ [6, 8, 1, 7, 4, 3, 4, 7, 1, 8, 6],
    [8, 10, 3, 9, 6, 5, 6, 9, 3, 10, 8],
    [1, 3, 7, 2, 10, 9, 10, 2, 7, 3, 1],
    [7, 9, 2, 8, 5, 4, 5, 8, 2, 9, 7],
    [4, 6, 10, 5, 2, 1, 2, 5, 10, 6, 4],
    [3, 5, 9, 4, 1, 0, 1, 4, 9, 5, 3],
    [4, 6, 10, 5, 2, 1, 2, 5, 10, 6, 4],
    [7, 9, 2, 8, 5, 4, 5, 8, 2, 9, 7],
    [1, 3, 7, 2, 10, 9, 10, 2, 7, 3, 1],
    [8, 10, 3, 9, 6, 5, 6, 9, 3, 10, 8],
    [6, 8, 1, 7, 4, 3, 4, 7, 1, 8, 6] ]

/-- The eleven central-circle labels in Figure 15.1. -/
def circleQuadrances : List Eleven.Element :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

end

/-- The point count printed for the null circle followed by the ten non-null
circles. -/
def circlePointCounts : List Nat :=
  [1, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12]

open Purelib.Geometry.Conics.Circle.Finite in
open Purelib.Geometry.Plane.Point in
open Purelib.Geometry.Plane.Point.Finite in
/-- Example 15.2: Figure 15.1 is the exact central-quadrance table over the
displayed `F₁₁` labels, its 121 positions are duplicate-free, and the
null/non-null circle filters have respectively one and twelve points. -/
theorem example_15_2 :
    Display.CentralCircleDisplayCertified origin displayedPointRows
      displayedValueRows circleQuadrances circlePointCounts := by
  unfold Display.CentralCircleDisplayCertified
  constructor
  · unfold Display.centralQuadranceRows displayedPointRows Grid.pointRows Grid.pointRow origin
      xCoordinates yCoordinates displayedValueRows Quadrance.quadrance
    decide
  constructor
  · unfold displayedPointRows
    apply Grid.pointRows_flatten_nodup
    · unfold xCoordinates
      decide
    · unfold yCoordinates
      decide
  constructor
  · unfold circleQuadrances
    decide
  · unfold Display.displayedCircleCounts Display.displayedCircleCount
      Display.displayedCirclePointRows Display.displayedCirclePoints displayedPointRows
      Grid.pointRows Grid.pointRow origin xCoordinates yCoordinates circleQuadrances
      circlePointCounts Quadrance.quadrance
    decide

end ExampleFifteenTwo

namespace ExerciseFifteenThree

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Plane.Point in
/-- The displayed origin. -/
def origin : Purelib.Geometry.Plane.Point Thirteen.Element := ⟨0, 0⟩

section
open Purelib.Algebra.Field.Finite
/-- Figure 15.3's horizontal coordinate labels, from `-6` through `6`. -/
def xCoordinates : List Thirteen.Element :=
  [-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6]

/-- Figure 15.3's vertical coordinate labels, from `6` through `-6`. -/
def yCoordinates : List Thirteen.Element :=
  [6, 5, 4, 3, 2, 1, 0, -1, -2, -3, -4, -5, -6]

end

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Plane.Point in
open Purelib.Geometry.Plane.Point.Finite in
/-- The 169 literal point positions in Figure 15.3, retained row by row. -/
def displayedPointRows : List (List (Purelib.Geometry.Plane.Point Thirteen.Element)) :=
  Grid.pointRows xCoordinates yCoordinates

section
open Purelib.Algebra.Field.Finite
/-- The thirteen rows of central quadrances printed in Figure 15.3. -/
def displayedValueRows : List (List Thirteen.Element) :=
  [ [7, 9, 0, 6, 1, 11, 10, 11, 1, 6, 0, 9, 7],
    [9, 11, 2, 8, 3, 0, 12, 0, 3, 8, 2, 11, 9],
    [0, 2, 6, 12, 7, 4, 3, 4, 7, 12, 6, 2, 0],
    [6, 8, 12, 5, 0, 10, 9, 10, 0, 5, 12, 8, 6],
    [1, 3, 7, 0, 8, 5, 4, 5, 8, 0, 7, 3, 1],
    [11, 0, 4, 10, 5, 2, 1, 2, 5, 10, 4, 0, 11],
    [10, 12, 3, 9, 4, 1, 0, 1, 4, 9, 3, 12, 10],
    [11, 0, 4, 10, 5, 2, 1, 2, 5, 10, 4, 0, 11],
    [1, 3, 7, 0, 8, 5, 4, 5, 8, 0, 7, 3, 1],
    [6, 8, 12, 5, 0, 10, 9, 10, 0, 5, 12, 8, 6],
    [0, 2, 6, 12, 7, 4, 3, 4, 7, 12, 6, 2, 0],
    [9, 11, 2, 8, 3, 0, 12, 0, 3, 8, 2, 11, 9],
    [7, 9, 0, 6, 1, 11, 10, 11, 1, 6, 0, 9, 7] ]

/-- The thirteen central-circle labels in Figure 15.3. -/
def circleQuadrances : List Thirteen.Element :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

end

/-- The point count printed for the null circle followed by the twelve
non-null circles. -/
def circlePointCounts : List Nat :=
  [25, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12]

open Purelib.Geometry.Conics.Circle.Finite in
open Purelib.Geometry.Plane.Point in
open Purelib.Geometry.Plane.Point.Finite in
/-- Exercise 15.3: Figure 15.3 is the exact central-quadrance table over the
displayed `F₁₃` labels, its 169 positions are duplicate-free, and the
null/non-null circle filters have respectively twenty-five and twelve points. -/
theorem exercise_15_3 :
    Display.CentralCircleDisplayCertified origin displayedPointRows
      displayedValueRows circleQuadrances circlePointCounts := by
  unfold Display.CentralCircleDisplayCertified
  constructor
  · unfold Display.centralQuadranceRows displayedPointRows Grid.pointRows Grid.pointRow origin
      xCoordinates yCoordinates displayedValueRows Quadrance.quadrance
    decide
  constructor
  · unfold displayedPointRows
    apply Grid.pointRows_flatten_nodup
    · unfold xCoordinates
      decide
    · unfold yCoordinates
      decide
  constructor
  · unfold circleQuadrances
    decide
  · unfold Display.displayedCircleCounts Display.displayedCircleCount
      Display.displayedCirclePointRows Display.displayedCirclePoints displayedPointRows
      Grid.pointRows Grid.pointRow origin xCoordinates yCoordinates circleQuadrances
      circlePointCounts Quadrance.quadrance
    decide

end ExerciseFifteenThree

end ChapterFifteenCentralCircles

end formalisations.DivineProportions.Chapters.Examples

end
