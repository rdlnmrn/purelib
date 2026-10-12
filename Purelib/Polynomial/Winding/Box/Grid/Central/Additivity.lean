module
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Grid.Central
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Subdivision

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Tactic.Ring

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

namespace Purelib.Polynomial.Winding.Box.Grid.Central.Additivity

/-- Exact raw additivity for the displayed `3 × 3` grid. -/
theorem raw_additivity
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (outer center : Box)
    (strict : center.StrictInterior outer) :
    Winding.Box.Basic.quadrupledBoxWinding p outer =
      Winding.Box.Basic.quadrupledBoxWinding p center +
      Winding.Box.Basic.quadrupledBoxWinding p (Box.Grid.Central.southwest outer center strict) +
      Winding.Box.Basic.quadrupledBoxWinding p (Box.Grid.Central.west outer center strict) +
      Winding.Box.Basic.quadrupledBoxWinding p (Box.Grid.Central.northwest outer center strict) +
      Winding.Box.Basic.quadrupledBoxWinding p (Box.Grid.Central.south outer center strict) +
      Winding.Box.Basic.quadrupledBoxWinding p (Box.Grid.Central.north outer center strict) +
      Winding.Box.Basic.quadrupledBoxWinding p (Box.Grid.Central.southeast outer center strict) +
      Winding.Box.Basic.quadrupledBoxWinding p (Box.Grid.Central.east outer center strict) +
      Winding.Box.Basic.quadrupledBoxWinding p (Box.Grid.Central.northeast outer center strict) := by
  let xLowerInside : outer.xLower ≤ center.xLower ∧
      center.xLower ≤ outer.xUpper :=
    ⟨strict.left.le, center.x_valid.trans strict.right.le⟩
  let rightRemainder := outer.verticalRight center.xLower xLowerInside
  let xUpperInside : rightRemainder.xLower ≤ center.xUpper ∧
      center.xUpper ≤ rightRemainder.xUpper :=
    ⟨center.x_valid, strict.right.le⟩
  let leftColumn := outer.verticalLeft center.xLower xLowerInside
  let middleColumn := rightRemainder.verticalLeft center.xUpper xUpperInside
  let rightColumn := rightRemainder.verticalRight center.xUpper xUpperInside
  have leftLowerInside : leftColumn.yLower ≤ center.yLower ∧
      center.yLower ≤ leftColumn.yUpper :=
    ⟨strict.bottom.le, center.y_valid.trans strict.top.le⟩
  let leftUpper := leftColumn.horizontalUpper center.yLower leftLowerInside
  have leftUpperInside : leftUpper.yLower ≤ center.yUpper ∧
      center.yUpper ≤ leftUpper.yUpper :=
    ⟨center.y_valid, strict.top.le⟩
  have middleLowerInside : middleColumn.yLower ≤ center.yLower ∧
      center.yLower ≤ middleColumn.yUpper :=
    ⟨strict.bottom.le, center.y_valid.trans strict.top.le⟩
  let middleUpper := middleColumn.horizontalUpper center.yLower
    middleLowerInside
  have middleUpperInside : middleUpper.yLower ≤ center.yUpper ∧
      center.yUpper ≤ middleUpper.yUpper :=
    ⟨center.y_valid, strict.top.le⟩
  have rightLowerInside : rightColumn.yLower ≤ center.yLower ∧
      center.yLower ≤ rightColumn.yUpper :=
    ⟨strict.bottom.le, center.y_valid.trans strict.top.le⟩
  let rightUpper := rightColumn.horizontalUpper center.yLower
    rightLowerInside
  have rightUpperInside : rightUpper.yLower ≤ center.yUpper ∧
      center.yUpper ≤ rightUpper.yUpper :=
    ⟨center.y_valid, strict.top.le⟩
  have verticalLower := Winding.Box.Subdivision.quadrupledBoxWinding_vertical_split
    p outer center.xLower xLowerInside
  have verticalUpper := Winding.Box.Subdivision.quadrupledBoxWinding_vertical_split
    p rightRemainder center.xUpper xUpperInside
  have leftLower := Winding.Box.Subdivision.quadrupledBoxWinding_horizontal_split
    p leftColumn center.yLower leftLowerInside
  have leftTop := Winding.Box.Subdivision.quadrupledBoxWinding_horizontal_split
    p leftUpper center.yUpper leftUpperInside
  have middleLower := Winding.Box.Subdivision.quadrupledBoxWinding_horizontal_split
    p middleColumn center.yLower middleLowerInside
  have middleTop := Winding.Box.Subdivision.quadrupledBoxWinding_horizontal_split
    p middleUpper center.yUpper middleUpperInside
  have rightLower := Winding.Box.Subdivision.quadrupledBoxWinding_horizontal_split
    p rightColumn center.yLower rightLowerInside
  have rightTop := Winding.Box.Subdivision.quadrupledBoxWinding_horizontal_split
    p rightUpper center.yUpper rightUpperInside
  have southwestEq :
      leftColumn.horizontalLower center.yLower leftLowerInside =
        Box.Grid.Central.southwest outer center strict := by
    apply Box.ext <;> rfl
  have westEq : leftUpper.horizontalLower center.yUpper leftUpperInside =
      Box.Grid.Central.west outer center strict := by
    apply Box.ext <;> rfl
  have northwestEq : leftUpper.horizontalUpper center.yUpper leftUpperInside =
      Box.Grid.Central.northwest outer center strict := by
    apply Box.ext <;> rfl
  have southEq : middleColumn.horizontalLower center.yLower
      middleLowerInside = Box.Grid.Central.south outer center strict := by
    apply Box.ext <;> rfl
  have centerEq : middleUpper.horizontalLower center.yUpper
      middleUpperInside = center := by
    apply Box.ext <;> rfl
  have northEq : middleUpper.horizontalUpper center.yUpper
      middleUpperInside = Box.Grid.Central.north outer center strict := by
    apply Box.ext <;> rfl
  have southeastEq : rightColumn.horizontalLower center.yLower
      rightLowerInside = Box.Grid.Central.southeast outer center strict := by
    apply Box.ext <;> rfl
  have eastEq : rightUpper.horizontalLower center.yUpper rightUpperInside =
      Box.Grid.Central.east outer center strict := by
    apply Box.ext <;> rfl
  have northeastEq : rightUpper.horizontalUpper center.yUpper
      rightUpperInside = Box.Grid.Central.northeast outer center strict := by
    apply Box.ext <;> rfl
  rw [verticalLower, verticalUpper, leftLower, leftTop, middleLower,
    middleTop, rightLower, rightTop, southwestEq, westEq, northwestEq,
    southEq, centerEq, northEq, southeastEq, eastEq, northeastEq]
  ring1
end Purelib.Polynomial.Winding.Box.Grid.Central.Additivity

end
