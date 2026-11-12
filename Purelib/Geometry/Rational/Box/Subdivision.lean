module
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Tactic.Ring
public import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Geometry.Rational.Box.Neighborhood
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
public import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Symmetric boxes and certified coordinate cuts

A nonnegative radius determines a box centered at zero. A displayed cut inside
one coordinate interval retains the other interval and supplies both child
order certificates directly from the same parent and cut witnesses.
-/

namespace Purelib.Geometry.Rational.Box

-- Retain the established Box declaration names.
open Purelib.Data.Rat
open Purelib.Geometry.Rational (Box)

/-- The square centered at zero with the given nonnegative coordinate radius.

The four endpoints are negative and positive copies of the supplied radius. Direct rational negation order certifies
both closed coordinate intervals. -/
@[expose] public def symmetric (radius : Fraction.Rational) (nonnegative : 0 ≤ radius) : Box where
  xLower := -radius
  xUpper := radius
  yLower := -radius
  yUpper := radius
  x_valid := by
    have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct nonnegative
    change -radius ≤ (0 : Fraction.Rational) at reversed
    exact reversed.trans nonnegative
  y_valid := by
    have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct nonnegative
    change -radius ≤ (0 : Fraction.Rational) at reversed
    exact reversed.trans nonnegative

/-- Left child produced by a certified vertical cut.

The lower real endpoint and both imaginary endpoints remain those of the parent. The supplied lower cut bound certifies
the shortened real interval. -/
@[expose] public def verticalLeft (B : Box) (cut : Fraction.Rational)
    (inside : B.xLower ≤ cut ∧ cut ≤ B.xUpper) : Box where
  xLower := B.xLower
  xUpper := cut
  yLower := B.yLower
  yUpper := B.yUpper
  x_valid := inside.1
  y_valid := B.y_valid

/-- Right child produced by a certified vertical cut.

The upper real endpoint and both imaginary endpoints remain those of the parent. The supplied upper cut bound certifies
the shortened real interval. -/
@[expose] public def verticalRight (B : Box) (cut : Fraction.Rational)
    (inside : B.xLower ≤ cut ∧ cut ≤ B.xUpper) : Box where
  xLower := cut
  xUpper := B.xUpper
  yLower := B.yLower
  yUpper := B.yUpper
  x_valid := inside.2
  y_valid := B.y_valid

/-- The left child of a certified vertical cut refines its parent box.

The unchanged endpoints satisfy reflexive bounds; the retained upper cut bound supplies containment of the new real
endpoint. -/
public theorem verticalLeft_refines (B : Box) (cut : Fraction.Rational)
    (inside : B.xLower ≤ cut ∧ cut ≤ B.xUpper) :
    (B.verticalLeft cut inside).Refines B :=
  ⟨le_rfl, inside.2, le_rfl, le_rfl⟩

/-- The right child of a certified vertical cut refines its parent box.

The unchanged endpoints satisfy reflexive bounds; the retained lower cut bound supplies containment of the new real
endpoint. -/
public theorem verticalRight_refines (B : Box) (cut : Fraction.Rational)
    (inside : B.xLower ≤ cut ∧ cut ≤ B.xUpper) :
    (B.verticalRight cut inside).Refines B :=
  ⟨inside.1, le_rfl, le_rfl, le_rfl⟩

/-- Lower child produced by a certified horizontal cut.

Both real endpoints and the lower imaginary endpoint remain those of the parent. The supplied lower cut bound certifies
the shortened imaginary interval. -/
@[expose] public def horizontalLower (B : Box) (cut : Fraction.Rational)
    (inside : B.yLower ≤ cut ∧ cut ≤ B.yUpper) : Box where
  xLower := B.xLower
  xUpper := B.xUpper
  yLower := B.yLower
  yUpper := cut
  x_valid := B.x_valid
  y_valid := inside.1

/-- Upper child produced by a certified horizontal cut.

Both real endpoints and the upper imaginary endpoint remain those of the parent. The supplied upper cut bound certifies
the shortened imaginary interval. -/
@[expose] public def horizontalUpper (B : Box) (cut : Fraction.Rational)
    (inside : B.yLower ≤ cut ∧ cut ≤ B.yUpper) : Box where
  xLower := B.xLower
  xUpper := B.xUpper
  yLower := cut
  yUpper := B.yUpper
  x_valid := B.x_valid
  y_valid := inside.2

/-- The lower child of a certified horizontal cut refines its parent box.

The unchanged endpoints satisfy reflexive bounds; the retained upper cut bound supplies containment of the new imaginary
endpoint. -/
public theorem horizontalLower_refines (B : Box) (cut : Fraction.Rational)
    (inside : B.yLower ≤ cut ∧ cut ≤ B.yUpper) :
    (B.horizontalLower cut inside).Refines B :=
  ⟨le_rfl, le_rfl, le_rfl, inside.2⟩

/-- The upper child of a certified horizontal cut refines its parent box.

The unchanged endpoints satisfy reflexive bounds; the retained lower cut bound supplies containment of the new imaginary
endpoint. -/
public theorem horizontalUpper_refines (B : Box) (cut : Fraction.Rational)
    (inside : B.yLower ≤ cut ∧ cut ≤ B.yUpper) :
    (B.horizontalUpper cut inside).Refines B :=
  ⟨le_rfl, le_rfl, inside.1, le_rfl⟩

set_option genInjectivity false in
/-- Two proper child boxes retain their common parent and a strict real-coordinate separation. -/
public structure SeparatedChildren (parent : Box) where
  /-- The retained left child box. -/ left : Box
  /-- The retained right child box. -/ right : Box
  /-- The left child has positive width and height. -/ leftProper : left.Proper
  /-- The right child has positive width and height. -/ rightProper : right.Proper
  /-- The left child remains inside the same original parent. -/ leftRefines : left.Refines parent
  /-- The right child remains inside the same original parent. -/ rightRefines : right.Refines parent
  /-- Every real coordinate of the left child precedes every real coordinate of the right child. -/ separated :
    left.xUpper < right.xLower

namespace SeparatedChildren

/-- Split a proper box at its midpoint, then retain strict neighbourhoods in its two proper halves.

The original midpoint and each half's inner neighbourhood are computed once.
Strict containment below and above the same dividing coordinate proves the
closed children disjoint, including their boundary points.
-/
public def build (parent : Box) (proper : parent.Proper) : SeparatedChildren parent := by
  let center := parent.midpoint
  have strict := parent.midpoint_strictContains proper
  let cut := center.re
  have bounds : parent.xLower ≤ cut ∧ cut ≤ parent.xUpper := ⟨strict.1.le, strict.2.1.le⟩
  let leftHalf := parent.verticalLeft cut bounds
  let rightHalf := parent.verticalRight cut bounds
  have leftProper : leftHalf.Proper := ⟨strict.1, proper.2⟩
  have rightProper : rightHalf.Proper := ⟨strict.2.1, proper.2⟩
  have leftCenter := leftHalf.midpoint_strictContains leftProper
  have rightCenter := rightHalf.midpoint_strictContains rightProper
  let left := Neighborhood.innerBox leftHalf leftHalf.midpoint leftCenter 1 (by decide)
  let right := Neighborhood.innerBox rightHalf rightHalf.midpoint rightCenter 1 (by decide)
  have leftInterior := Neighborhood.innerBox_strictInterior leftCenter (by decide : (0 : Fraction.Rational) < 1)
  have rightInterior := Neighborhood.innerBox_strictInterior rightCenter (by decide : (0 : Fraction.Rational) < 1)
  exact
    { left := left
      right := right
      leftProper := Neighborhood.innerBox_proper leftCenter (by decide)
      rightProper := Neighborhood.innerBox_proper rightCenter (by decide)
      leftRefines := (Refinement.StrictInterior.refines leftInterior).trans (parent.verticalLeft_refines cut bounds)
      rightRefines := (Refinement.StrictInterior.refines rightInterior).trans (parent.verticalRight_refines cut bounds)
      separated := leftInterior.right.trans rightInterior.left }

/-- Points in opposite retained children are strictly separated in their real coordinates. -/
public theorem points_separated {parent : Box} (children : SeparatedChildren parent)
    {leftPoint rightPoint : Purelib.Data.Gaussian.Basic.Canonical}
    (leftInside : children.left.Contains leftPoint) (rightInside : children.right.Contains rightPoint) :
    leftPoint.re < rightPoint.re :=
  leftInside.2.1.trans_lt (children.separated.trans_le rightInside.1)

end SeparatedChildren

/-- Increasing a symmetric square's nonnegative radius refines it into the original larger square.

Both coordinate intervals retain their original endpoints. Direct order
reversal gives the two lower-endpoint inequalities, and the supplied
radius comparison gives the two upper-endpoint inequalities.
-/
public theorem symmetric_refines {inner outer : Fraction.Rational}
    (innerNonnegative : 0 ≤ inner) (outerNonnegative : 0 ≤ outer) (bound : inner ≤ outer) :
    (symmetric inner innerNonnegative).Refines (symmetric outer outerNonnegative) :=
  ⟨Fraction.Order.Arithmetic.neg_le_neg_direct bound, bound,
    Fraction.Order.Arithmetic.neg_le_neg_direct bound, bound⟩

/-- A point in the original symmetric square has quadrance at most twice the squared radius.

The retained square endpoints bound each coordinate square by the same
radius square. The original Gaussian box bound combines those two scalar
bounds without selecting another point or changing the box.
-/
public theorem normSq_le_symmetric {radius : Fraction.Rational} (nonnegative : 0 ≤ radius)
    {point : Data.Gaussian.Basic.Canonical} (inside : (symmetric radius nonnegative).Contains point) :
    Data.Gaussian.Norm.Basic.normSq point ≤ 2 * radius ^ 2 := by
  have bounded := normSq_le_normSqBound inside
  rewrite [normSqBound, coordinateSqBound_eq_original] at bounded
  change Data.Gaussian.Norm.Basic.normSq point ≤
    2 * max (max ((-radius) ^ 2) (radius ^ 2)) (max ((-radius) ^ 2) (radius ^ 2)) at bounded
  rewrite [show (-radius) ^ 2 = radius ^ 2 by ring1,
    Fraction.Order.Basic.max_self, Fraction.Order.Basic.max_self] at bounded
  exact bounded

end Purelib.Geometry.Rational.Box
