module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Gap
public import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Elimination.Axis.Gap
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Grid.Central.Build
import Purelib.Polynomial.Winding.Box.Nonnegative.Squarefree
import Purelib.Polynomial.Winding.Box.Subdivision
public import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
public import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Dense.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Winding bounds for strictly contained states

An eliminant-safe finite subdivision compares the original surrounding
region with one or two separated winding-one states inside it.
-/

namespace Purelib.RootIsolation.State.WindingOne.Count

/-- A clear region strictly containing a winding-one state has quadrupled winding at least four.

The squarefree polynomial has degree at least two and retains its axis-elimination certificate; the surrounding finite
grid cells have nonnegative winding. -/
public theorem region_rawWinding_ge_four_of_strictInterior
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (state : Basic.WindingOneState p ambient)
    (region : Clearance.Box.Region.ClearRegion p ambient)
    (strict : state.box.StrictInterior region.box) :
    4 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box := by
  let grid := Winding.Box.Grid.Central.Build.build region.clearance state.proper strict
    (state.ambientLeftClearance.restrict region.refinesAmbient)
    (state.ambientRightClearance.restrict region.refinesAmbient)
    (state.ambientBottomClearance.restrict region.refinesAmbient)
    (state.ambientTopClearance.restrict region.refinesAmbient)
  have southwestNonnegative :=
    Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination
      (grid.southwest.refines.trans region.refinesAmbient)
      grid.southwest.proper grid.southwest.clearance
  have westNonnegative :=
    Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination
      (grid.west.refines.trans region.refinesAmbient)
      grid.west.proper grid.west.clearance
  have northwestNonnegative :=
    Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination
      (grid.northwest.refines.trans region.refinesAmbient)
      grid.northwest.proper grid.northwest.clearance
  have southNonnegative :=
    Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination
      (grid.south.refines.trans region.refinesAmbient)
      grid.south.proper grid.south.clearance
  have northNonnegative :=
    Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination
      (grid.north.refines.trans region.refinesAmbient)
      grid.north.proper grid.north.clearance
  have southeastNonnegative :=
    Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination
      (grid.southeast.refines.trans region.refinesAmbient)
      grid.southeast.proper grid.southeast.clearance
  have eastNonnegative :=
    Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination
      (grid.east.refines.trans region.refinesAmbient)
      grid.east.proper grid.east.clearance
  have northeastNonnegative :=
    Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination
      (grid.northeast.refines.trans region.refinesAmbient)
      grid.northeast.proper grid.northeast.clearance
  have additive := grid.additive
  rw [state.rawWindingFour] at additive
  omega

/-- A clear region strictly containing two winding-one states separated horizontally has quadrupled winding at least
eight.

An eliminant-safe vertical cut separates the two states while retaining their original polynomial and ambient box. -/
public theorem region_rawWinding_ge_eight_of_x_ordered
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (region : Clearance.Box.Region.ClearRegion p ambient) (left right :
      Basic.WindingOneState p ambient)
    (leftInside : left.box.StrictInterior region.box)
    (rightInside : right.box.StrictInterior region.box)
    (gap : left.box.xUpper < right.box.xLower) :
    8 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box := by
  let cut := Elimination.Axis.Gap.verticalGapCoordinate elimination gap
  have cutSpec := Elimination.Axis.Gap.verticalGapCoordinate_spec elimination gap
  have cutInside : region.box.xLower ≤ cut ∧ cut ≤ region.box.xUpper :=
    ⟨((leftInside.left.trans_le left.box.x_valid).trans
        cutSpec.2.1).le,
      cutSpec.2.2.le.trans
        (right.box.x_valid.trans_lt rightInside.right).le⟩
  let leftBox := region.box.verticalLeft cut cutInside
  let rightBox := region.box.verticalRight cut cutInside
  have leftRefines : leftBox.Refines region.box :=
    region.box.verticalLeft_refines cut cutInside
  have rightRefines : rightBox.Refines region.box :=
    region.box.verticalRight_refines cut cutInside
  let cutClearance := Clearance.Box.Line.Elimination.Gap.verticalGapClearance elimination gap region.box
  let leftClearance : Clearance.Box.Boundary.Basic.BoundaryClearance p leftBox :=
    Clearance.Box.Boundary.Lines.boundaryOfLines
    ((Clearance.Box.Boundary.Lines.leftOfBoundary region.clearance).restrict leftRefines)
    (cutClearance.restrict leftRefines)
    ((Clearance.Box.Boundary.Lines.bottomOfBoundary region.clearance).restrict leftRefines)
    ((Clearance.Box.Boundary.Lines.topOfBoundary region.clearance).restrict leftRefines)
  let rightClearance : Clearance.Box.Boundary.Basic.BoundaryClearance p rightBox :=
    Clearance.Box.Boundary.Lines.boundaryOfLines
    (cutClearance.restrict rightRefines)
    ((Clearance.Box.Boundary.Lines.rightOfBoundary region.clearance).restrict rightRefines)
    ((Clearance.Box.Boundary.Lines.bottomOfBoundary region.clearance).restrict rightRefines)
    ((Clearance.Box.Boundary.Lines.topOfBoundary region.clearance).restrict rightRefines)
  let leftRegion : Clearance.Box.Region.ClearRegion p ambient :=
    { box := leftBox
      refinesAmbient := leftRefines.trans region.refinesAmbient
      proper :=
        ⟨(leftInside.left.trans_le left.box.x_valid).trans cutSpec.2.1,
          region.proper.2⟩
      clearance := leftClearance }
  let rightRegion : Clearance.Box.Region.ClearRegion p ambient :=
    { box := rightBox
      refinesAmbient := rightRefines.trans region.refinesAmbient
      proper :=
        ⟨cutSpec.2.2.trans
            (right.box.x_valid.trans_lt rightInside.right),
          region.proper.2⟩
      clearance := rightClearance }
  have leftStrict : left.box.StrictInterior leftRegion.box :=
    { left := leftInside.left
      right := cutSpec.2.1
      bottom := leftInside.bottom
      top := leftInside.top }
  have rightStrict : right.box.StrictInterior rightRegion.box :=
    { left := cutSpec.2.2
      right := rightInside.right
      bottom := rightInside.bottom
      top := rightInside.top }
  have leftFour := State.WindingOne.Count.region_rawWinding_ge_four_of_strictInterior
    degreeAtLeastTwo squarefree elimination left leftRegion leftStrict
  have rightFour := State.WindingOne.Count.region_rawWinding_ge_four_of_strictInterior
    degreeAtLeastTwo squarefree elimination right rightRegion rightStrict
  have additive := Winding.Box.Subdivision.quadrupledBoxWinding_vertical_split
    p region.box cut cutInside
  rw [additive]
  simp only [leftRegion, leftBox] at leftFour
  simp only [rightRegion, rightBox] at rightFour
  omega

/-- A clear region strictly containing two winding-one states separated vertically has quadrupled winding at least
eight.

An eliminant-safe horizontal cut separates the two states while retaining their original polynomial and ambient box. -/
public theorem region_rawWinding_ge_eight_of_y_ordered
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (region : Clearance.Box.Region.ClearRegion p ambient) (bottom top :
      Basic.WindingOneState p ambient)
    (bottomInside : bottom.box.StrictInterior region.box)
    (topInside : top.box.StrictInterior region.box)
    (gap : bottom.box.yUpper < top.box.yLower) :
    8 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box := by
  let cut := Elimination.Axis.Gap.horizontalGapCoordinate elimination gap
  have cutSpec := Elimination.Axis.Gap.horizontalGapCoordinate_spec elimination gap
  have cutInside : region.box.yLower ≤ cut ∧ cut ≤ region.box.yUpper :=
    ⟨((bottomInside.bottom.trans_le bottom.box.y_valid).trans
        cutSpec.2.1).le,
      cutSpec.2.2.le.trans
        (top.box.y_valid.trans_lt topInside.top).le⟩
  let lowerBox := region.box.horizontalLower cut cutInside
  let upperBox := region.box.horizontalUpper cut cutInside
  have lowerRefines : lowerBox.Refines region.box :=
    region.box.horizontalLower_refines cut cutInside
  have upperRefines : upperBox.Refines region.box :=
    region.box.horizontalUpper_refines cut cutInside
  let cutClearance := Clearance.Box.Line.Elimination.Gap.horizontalGapClearance elimination gap region.box
  let lowerClearance : Clearance.Box.Boundary.Basic.BoundaryClearance p lowerBox :=
    Clearance.Box.Boundary.Lines.boundaryOfLines
    ((Clearance.Box.Boundary.Lines.leftOfBoundary region.clearance).restrict lowerRefines)
    ((Clearance.Box.Boundary.Lines.rightOfBoundary region.clearance).restrict lowerRefines)
    ((Clearance.Box.Boundary.Lines.bottomOfBoundary region.clearance).restrict lowerRefines)
    (cutClearance.restrict lowerRefines)
  let upperClearance : Clearance.Box.Boundary.Basic.BoundaryClearance p upperBox :=
    Clearance.Box.Boundary.Lines.boundaryOfLines
    ((Clearance.Box.Boundary.Lines.leftOfBoundary region.clearance).restrict upperRefines)
    ((Clearance.Box.Boundary.Lines.rightOfBoundary region.clearance).restrict upperRefines)
    (cutClearance.restrict upperRefines)
    ((Clearance.Box.Boundary.Lines.topOfBoundary region.clearance).restrict upperRefines)
  let lowerRegion : Clearance.Box.Region.ClearRegion p ambient :=
    { box := lowerBox
      refinesAmbient := lowerRefines.trans region.refinesAmbient
      proper :=
        ⟨region.proper.1,
          (bottomInside.bottom.trans_le bottom.box.y_valid).trans cutSpec.2.1⟩
      clearance := lowerClearance }
  let upperRegion : Clearance.Box.Region.ClearRegion p ambient :=
    { box := upperBox
      refinesAmbient := upperRefines.trans region.refinesAmbient
      proper :=
        ⟨region.proper.1,
          cutSpec.2.2.trans (top.box.y_valid.trans_lt topInside.top)⟩
      clearance := upperClearance }
  have bottomStrict : bottom.box.StrictInterior lowerRegion.box :=
    { left := bottomInside.left
      right := bottomInside.right
      bottom := bottomInside.bottom
      top := cutSpec.2.1 }
  have topStrict : top.box.StrictInterior upperRegion.box :=
    { left := topInside.left
      right := topInside.right
      bottom := cutSpec.2.2
      top := topInside.top }
  have lowerFour := State.WindingOne.Count.region_rawWinding_ge_four_of_strictInterior
    degreeAtLeastTwo squarefree elimination bottom lowerRegion bottomStrict
  have upperFour := State.WindingOne.Count.region_rawWinding_ge_four_of_strictInterior
    degreeAtLeastTwo squarefree elimination top upperRegion topStrict
  have additive := Winding.Box.Subdivision.quadrupledBoxWinding_horizontal_split
    p region.box cut cutInside
  rw [additive]
  simp only [lowerRegion, lowerBox] at lowerFour
  simp only [upperRegion, upperBox] at upperFour
  omega

/-- A clear region strictly containing two separated winding-one states has quadrupled winding at least eight.

The certificate retains the squarefree polynomial of degree at least two, axis elimination and the two original states.
-/
public theorem region_rawWinding_ge_eight_of_separated
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (region : Clearance.Box.Region.ClearRegion p ambient) (left right :
      Basic.WindingOneState p ambient)
    (leftInside : left.box.StrictInterior region.box)
    (rightInside : right.box.StrictInterior region.box)
    (separated : left.box.Separated right.box) :
    8 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box := by
  rcases separated with leftOf | rightOf | below | above
  · exact State.WindingOne.Count.region_rawWinding_ge_eight_of_x_ordered degreeAtLeastTwo
      squarefree elimination region left right leftInside rightInside leftOf
  · exact State.WindingOne.Count.region_rawWinding_ge_eight_of_x_ordered degreeAtLeastTwo
      squarefree elimination region right left rightInside leftInside rightOf
  · exact State.WindingOne.Count.region_rawWinding_ge_eight_of_y_ordered degreeAtLeastTwo
      squarefree elimination region left right leftInside rightInside below
  · exact State.WindingOne.Count.region_rawWinding_ge_eight_of_y_ordered degreeAtLeastTwo
      squarefree elimination region right left rightInside leftInside above

end Purelib.RootIsolation.State.WindingOne.Count
