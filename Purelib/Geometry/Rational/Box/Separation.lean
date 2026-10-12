module
public import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
import Mathlib.Order.Basic

/-!
# Separation and overlap of rational boxes

Strict and weak endpoint gaps describe positive separation and disjoint
interiors. Failure of positive separation retains a displayed overlap point,
and coordinate refinements preserve the corresponding original gap.
-/

namespace Purelib.Geometry.Rational.Box

open Purelib
open Purelib.Geometry
open Purelib.Data.Rat

/-- Two closed boxes have a strict gap along at least one coordinate.

The four alternatives retain the endpoint ordering to the left, right, below
or above the other box; a shared edge does not give positive separation. -/
@[expose] public def Separated (left right : Rational.Box) : Prop :=
  left.xUpper < right.xLower ∨ right.xUpper < left.xLower ∨
    left.yUpper < right.yLower ∨ right.yUpper < left.yLower

/-- Decide positive separation by the four strict endpoint comparisons. -/
public instance separatedDecidable (left right : Rational.Box) :
    Decidable (left.Separated right) := by
  unfold Purelib.Geometry.Rational.Box.Separated
  infer_instance

/-- Select the coordinatewise maximum of the two boxes' lower endpoints.

This displayed Gaussian rational lies in both closed boxes whenever no strict
coordinate gap separates them. -/
@[expose] public def overlapPoint (left right : Rational.Box) : Data.Gaussian.Basic.Canonical :=
  ⟨max left.xLower right.xLower, max left.yLower right.yLower⟩

/-- The retained overlap point lies in both boxes when positive separation fails.

Failure of each strict gap bounds the opposite lower endpoint by the upper
endpoint. The coordinatewise maxima then satisfy all eight closed bounds. -/
public theorem contains_overlapPoint_of_not_separated
    {left right : Rational.Box} (notSeparated : ¬left.Separated right) :
    left.Contains (Geometry.Rational.Box.overlapPoint left right) ∧
      right.Contains (Geometry.Rational.Box.overlapPoint left right) := by
  have rightLowerLeLeftUpper : right.xLower ≤ left.xUpper :=
    le_of_not_gt (fun separated => notSeparated (Or.inl separated))
  have leftLowerLeRightUpper : left.xLower ≤ right.xUpper :=
    le_of_not_gt (fun separated =>
      notSeparated (Or.inr (Or.inl separated)))
  have rightBottomLeLeftTop : right.yLower ≤ left.yUpper :=
    le_of_not_gt (fun separated =>
      notSeparated (Or.inr (Or.inr (Or.inl separated))))
  have leftBottomLeRightTop : left.yLower ≤ right.yUpper :=
    le_of_not_gt (fun separated =>
      notSeparated (Or.inr (Or.inr (Or.inr separated))))
  exact
    ⟨⟨Fraction.Order.Basic.le_max_left _ _,
        Fraction.Order.Basic.max_le left.x_valid rightLowerLeLeftUpper,
        Fraction.Order.Basic.le_max_left _ _,
        Fraction.Order.Basic.max_le left.y_valid rightBottomLeLeftTop⟩,
      ⟨Fraction.Order.Basic.le_max_right _ _,
        Fraction.Order.Basic.max_le leftLowerLeRightUpper right.x_valid,
        Fraction.Order.Basic.le_max_right _ _,
        Fraction.Order.Basic.max_le leftBottomLeRightTop right.y_valid⟩⟩

/-- Two boxes have disjoint interiors along at least one coordinate.

The weak endpoint comparisons permit a shared edge. Strict interior
refinements turn the retained weak gap into positive coordinate separation. -/
@[expose] public def InteriorSeparated (left right : Rational.Box) : Prop :=
  left.xUpper ≤ right.xLower ∨ right.xUpper ≤ left.xLower ∨
    left.yUpper ≤ right.yLower ∨ right.yUpper ≤ left.yLower

/-- Interior separation is symmetric in the two boxes. -/
public theorem interiorSeparated_symm {left right : Rational.Box}
    (separated : left.InteriorSeparated right) :
    right.InteriorSeparated left := by
  rcases separated with leftOf | rightOf | below | above
  · exact Or.inr (Or.inl leftOf)
  · exact Or.inl rightOf
  · exact Or.inr (Or.inr (Or.inr below))
  · exact Or.inr (Or.inr (Or.inl above))

/-- Strict interior refinements of interior-disjoint boxes have a positive gap.

The original separating coordinate supplies a weak endpoint comparison;
the two retained strict refinements make that same comparison strict. -/
public theorem InteriorSeparated.strict_refinements
    {left right leftSmall rightSmall : Rational.Box}
    (separated : left.InteriorSeparated right)
    (leftStrict : leftSmall.StrictInterior left)
    (rightStrict : rightSmall.StrictInterior right) :
    leftSmall.Separated rightSmall := by
  rcases separated with leftOf | rightOf | below | above
  · exact Or.inl ((leftStrict.right.trans_le leftOf).trans rightStrict.left)
  · exact Or.inr (Or.inl
      ((rightStrict.right.trans_le rightOf).trans leftStrict.left))
  · exact Or.inr (Or.inr (Or.inl
      ((leftStrict.top.trans_le below).trans rightStrict.bottom)))
  · exact Or.inr (Or.inr (Or.inr
      ((rightStrict.top.trans_le above).trans leftStrict.bottom)))

/-- Coordinate refinement preserves interior separation of two boxes.

The retained subbox endpoint bounds compose with the original weak gap in
the same coordinate and direction. -/
public theorem InteriorSeparated.of_refines
    {left right leftSmall rightSmall : Rational.Box}
    (separated : left.InteriorSeparated right)
    (leftRefines : leftSmall.Refines left)
    (rightRefines : rightSmall.Refines right) :
    leftSmall.InteriorSeparated rightSmall := by
  rcases separated with leftOf | rightOf | below | above
  · exact Or.inl (leftRefines.2.1.trans
      (leftOf.trans rightRefines.1))
  · exact Or.inr (Or.inl (rightRefines.2.1.trans
      (rightOf.trans leftRefines.1)))
  · exact Or.inr (Or.inr (Or.inl (leftRefines.2.2.2.trans
      (below.trans rightRefines.2.2.1))))
  · exact Or.inr (Or.inr (Or.inr (rightRefines.2.2.2.trans
      (above.trans leftRefines.2.2.1))))

/-- Positive coordinate separation is symmetric in the two boxes. -/
public theorem separated_symm {left right : Rational.Box}
    (separated : left.Separated right) : right.Separated left := by
  rcases separated with leftOf | rightOf | below | above
  · exact Or.inr (Or.inl leftOf)
  · exact Or.inl rightOf
  · exact Or.inr (Or.inr (Or.inr below))
  · exact Or.inr (Or.inr (Or.inl above))

/-- Coordinate refinement preserves positive separation of two boxes.

The original strict gap remains between the corresponding retained subbox
endpoints after composing their weak refinement bounds. -/
public theorem Separated.of_refines
    {left right leftSmall rightSmall : Rational.Box}
    (separated : left.Separated right)
    (leftRefines : leftSmall.Refines left)
    (rightRefines : rightSmall.Refines right) :
    leftSmall.Separated rightSmall := by
  rcases separated with leftOf | rightOf | below | above
  · exact Or.inl (leftRefines.2.1.trans_lt
      (leftOf.trans_le rightRefines.1))
  · exact Or.inr (Or.inl (rightRefines.2.1.trans_lt
      (rightOf.trans_le leftRefines.1)))
  · exact Or.inr (Or.inr (Or.inl (leftRefines.2.2.2.trans_lt
      (below.trans_le rightRefines.2.2.1))))
  · exact Or.inr (Or.inr (Or.inr (rightRefines.2.2.2.trans_lt
      (above.trans_le leftRefines.2.2.1))))

/-- Displayed points in positively separated boxes cannot coincide.

The retained strict endpoint gap forces the corresponding coordinate of one
point below the other, contradicting equal displayed coordinates. -/
public theorem Separated.points_ne {left right : Rational.Box} {leftPoint rightPoint :
  Data.Gaussian.Basic.Canonical}
    (separated : left.Separated right)
    (leftInside : left.Contains leftPoint)
    (rightInside : right.Contains rightPoint) : leftPoint ≠ rightPoint := by
  intro equal
  have realEqual := congrArg Data.Gaussian.Basic.Canonical.re equal
  have imagEqual := congrArg Data.Gaussian.Basic.Canonical.im equal
  rcases separated with leftOf | rightOf | below | above
  · have impossible : leftPoint.re < rightPoint.re :=
      leftInside.2.1.trans_lt (leftOf.trans_le rightInside.1)
    rw [realEqual] at impossible
    exact (lt_irrefl _ impossible).elim
  · have impossible : rightPoint.re < leftPoint.re :=
      rightInside.2.1.trans_lt (rightOf.trans_le leftInside.1)
    rw [realEqual] at impossible
    exact (lt_irrefl _ impossible).elim
  · have impossible : leftPoint.im < rightPoint.im :=
      leftInside.2.2.2.trans_lt (below.trans_le rightInside.2.2.1)
    rw [imagEqual] at impossible
    exact (lt_irrefl _ impossible).elim
  · have impossible : rightPoint.im < leftPoint.im :=
      rightInside.2.2.2.trans_lt (above.trans_le leftInside.2.2.1)
    rw [imagEqual] at impossible
    exact (lt_irrefl _ impossible).elim

end Purelib.Geometry.Rational.Box

namespace Purelib.Geometry.Rational.Box.Separation

open Purelib.Geometry.Rational

/-- The retained coordinate-separation predicate for finite box families. -/
public abbrev SourcePersistentRegionOwnershipSeparatedAlias
    (left right : Box) := left.Separated right

end Purelib.Geometry.Rational.Box.Separation
