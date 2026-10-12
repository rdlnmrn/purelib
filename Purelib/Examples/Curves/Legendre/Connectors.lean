module
import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.Data.Fin.Cases
import Purelib.Data.Fin
import Purelib.Data.List.Append
import Purelib.Algebra.NatCast
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Progressive.Chamber.Target
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Legendre.Coefficients.Exact
public import Purelib.Curves.Legendre.Monodromy
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Polynomial
import Purelib.Curves.Legendre.Polynomial.Clearance
import Purelib.Curves.Legendre.Polynomial.Winding
import Purelib.Curves.Legendre.Rouche
import Purelib.Curves.Legendre.Squarefree
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Examples.Curves.Legendre.Crossings.LowerZero
import Purelib.Examples.Curves.Legendre.Crossings.UpperZero
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Translated
import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Winding.Affine.HalfPlane
import Purelib.Polynomial.Winding.Box.Affine
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Rouche.Connection
import Purelib.RootIsolation.FTA.Squarefree.Build
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Owner.Bridge.Rouche
public import Purelib.RootIsolation.Owner.Bridge.Transport
import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.RootIsolation.Progressive.Braid.Projected.Overlap
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.Topology.Knot.Braid.Artin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.Progressive.Braid.Projected.Frame
import Purelib.RootIsolation.Progressive.Chamber.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.Deriving.Repr

section
public section

/-!
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

namespace Purelib.Examples.Curves.Legendre.Connectors

open Purelib.Polynomial.Clearance.Box.Boundary.Translated
open Purelib.Polynomial.Winding
open Purelib.Data.Gaussian
open Purelib.Data.Fin
open Purelib.RootIsolation.Progressive.Braid.Projected.Overlap (ProjectedOverlap)
open Purelib.Polynomial.Clearance.Box.Dominance.Basic (BoundaryNormDominance)

open Purelib.Curves
open Purelib
open Purelib.Data
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Geometry
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Topology

open Purelib.Examples.Curves.Legendre.Crossings

open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)
open Purelib.RootIsolation.Owner.Local.Basic (LocalOwner)
open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)
open Purelib.Polynomial.Dense.Gaussian.Linear
open Purelib.Geometry.Rational.Box.Square

/-- The four vertical connector lines beside the Legendre roots zero and one. -/
inductive Side
  /-- The vertical connector line with real coordinate −1/4. -/ | left
  /-- The vertical connector line with real coordinate 1/4. -/ | right
  /-- The vertical connector line with real coordinate 3/4. -/ | oneLeft
  /-- The vertical connector line with real coordinate 5/4. -/ | oneRight
deriving @[expose] DecidableEq
derive_exposed_repr Side

/-- The real coordinate of a connector side: −1/4, 1/4, 3/4 or 5/4. -/
@[expose] def sideReal : Side ->
  Fraction.Rational
  | .left => -(1 / 4)
  | .right => 1 / 4
  | .oneLeft => 3 / 4
  | .oneRight => 5 / 4

/-- The Legendre parameter on the selected vertical line at the supplied rational height. -/
@[expose] def connectorParameter (side :
  Side) (height : Fraction.Rational) : Gaussian.Basic.Canonical :=
  Legendre.Paths.gaussian (sideReal side) height

/-- The connector parameter has the selected side's real coordinate. -/
@[simp] theorem connectorParameter_re (side :
  Side) (height : Fraction.Rational) :
    (connectorParameter side height).re = sideReal side := rfl

/-- The connector parameter has the supplied imaginary height. -/
@[simp] theorem connectorParameter_im (side :
  Side) (height : Fraction.Rational) :
    (connectorParameter side height).im = height := rfl

/-- The moving-root rectangle of horizontal radius 1/10 and vertical radius 1/2. -/
@[expose] def connectorMovingBox (side :
  Side) (height : Fraction.Rational) : Rational.Box where
  xLower := sideReal side - 1 / 10
  xUpper := sideReal side + 1 / 10
  yLower := height - 1 / 2
  yUpper := height + 1 / 2
  x_valid := by
    apply le_of_lt
    calc
      sideReal side - 1 / 10 < sideReal side := by
        have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 10) (sideReal side)
        have scalarZero : (sideReal side) - 0 = (sideReal side) :=
          by
          rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
            show -(0 : Fraction.Rational) = 0 by decide]
          exact (Fraction.Field.add_comm (sideReal side) 0).trans (Fraction.Field.zero_add
            (sideReal side))
        rewrite [scalarZero] at translated
        exact translated
      _ < sideReal side + 1 / 10 := by
        have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 10) (sideReal side)
        have scalarZero : (sideReal side) + 0 = (sideReal side) :=
          (Fraction.Field.add_comm (sideReal side) 0).trans (Fraction.Field.zero_add
            (sideReal side))
        rewrite [scalarZero] at translated
        exact translated
  y_valid := by
    apply le_of_lt
    calc
      height - 1 / 2 < height := by
        have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 2) height
        have scalarZero : height - 0 = height := by
          rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
            show -(0 : Fraction.Rational) = 0 by decide]
          exact (Fraction.Field.add_comm height 0).trans (Fraction.Field.zero_add height)
        rewrite [scalarZero] at translated
        exact translated
      _ < height + 1 / 2 := by
        have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 2) height
        have scalarZero : height + 0 = height :=
          (Fraction.Field.add_comm height 0).trans (Fraction.Field.zero_add height)
        rewrite [scalarZero] at translated
        exact translated

/-- The moving-root rectangle has strictly positive width and height. -/
theorem connectorMovingBox_proper (side :
  Side) (height : Fraction.Rational) :
    (connectorMovingBox side height).Proper := by
  constructor
  · change sideReal side - 1 / 10 < sideReal side + 1 / 10
    calc
      sideReal side - 1 / 10 < sideReal side := by
        have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 10) (sideReal side)
        have scalarZero : (sideReal side) - 0 = (sideReal side) :=
          by
          rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
            show -(0 : Fraction.Rational) = 0 by decide]
          exact (Fraction.Field.add_comm (sideReal side) 0).trans (Fraction.Field.zero_add
            (sideReal side))
        rewrite [scalarZero] at translated
        exact translated
      _ < sideReal side + 1 / 10 := by
        have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 10) (sideReal side)
        have scalarZero : (sideReal side) + 0 = (sideReal side) :=
          (Fraction.Field.add_comm (sideReal side) 0).trans (Fraction.Field.zero_add
            (sideReal side))
        rewrite [scalarZero] at translated
        exact translated
  · change height - 1 / 2 < height + 1 / 2
    calc
      height - 1 / 2 < height := by
        have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 2) height
        have scalarZero : height - 0 = height := by
          rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
            show -(0 : Fraction.Rational) = 0 by decide]
          exact (Fraction.Field.add_comm height 0).trans (Fraction.Field.zero_add height)
        rewrite [scalarZero] at translated
        exact translated
      _ < height + 1 / 2 := by
        have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 2) height
        have scalarZero : height + 0 = height :=
          (Fraction.Field.add_comm height 0).trans (Fraction.Field.zero_add height)
        rewrite [scalarZero] at translated
        exact translated

/-- The moving-root rectangle strictly contains its original connector parameter. -/
theorem connectorMovingBox_contains (side :
  Side) (height : Fraction.Rational) :
    (connectorMovingBox side height).Contains
      (connectorParameter side height) := by
  constructor
  · change sideReal side - 1 / 10 <= sideReal side
    exact (by
      have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
        (by decide : (0 : Fraction.Rational) < 1 / 10) (sideReal side)
      have scalarZero : (sideReal side) - 0 = (sideReal side) :=
        by
        rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
          show -(0 : Fraction.Rational) = 0 by decide]
        exact (Fraction.Field.add_comm (sideReal side) 0).trans (Fraction.Field.zero_add
          (sideReal side))
      rewrite [scalarZero] at translated
      exact translated :
      sideReal side - 1 / 10 < sideReal side).le
  constructor
  · change sideReal side <= sideReal side + 1 / 10
    exact (by
      have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
        (by decide : (0 : Fraction.Rational) < 1 / 10) (sideReal side)
      have scalarZero : (sideReal side) + 0 = (sideReal side) :=
        (Fraction.Field.add_comm (sideReal side) 0).trans (Fraction.Field.zero_add
          (sideReal side))
      rewrite [scalarZero] at translated
      exact translated :
      sideReal side < sideReal side + 1 / 10).le
  constructor
  · change height - 1 / 2 <= height
    exact (by
      have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
        (by decide : (0 : Fraction.Rational) < 1 / 2) height
      have scalarZero : height - 0 = height := by
        rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
          show -(0 : Fraction.Rational) = 0 by decide]
        exact (Fraction.Field.add_comm height 0).trans (Fraction.Field.zero_add height)
      rewrite [scalarZero] at translated
      exact translated :
      height - 1 / 2 < height).le
  · change height <= height + 1 / 2
    exact (by
      have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
        (by decide : (0 : Fraction.Rational) < 1 / 2) height
      have scalarZero : height + 0 = height :=
        (Fraction.Field.add_comm height 0).trans (Fraction.Field.zero_add height)
      rewrite [scalarZero] at translated
      exact translated :
      height < height + 1 / 2).le

/-- The moving-root rectangle's left boundary lies strictly left of the parameter. -/
theorem connectorMovingBox_left (side :
  Side) (height : Fraction.Rational) :
    (connectorMovingBox side height).xLower < sideReal side := by
  change sideReal side - 1 / 10 < sideReal side
  have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
    (by decide : (0 : Fraction.Rational) < 1 / 10) (sideReal side)
  have scalarZero : (sideReal side) - 0 = (sideReal side) := by
    rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
      show -(0 : Fraction.Rational) = 0 by decide]
    exact (Fraction.Field.add_comm (sideReal side) 0).trans (Fraction.Field.zero_add
      (sideReal side))
  rewrite [scalarZero] at translated
  exact translated

/-- The moving-root rectangle's right boundary lies strictly right of the parameter. -/
theorem connectorMovingBox_right (side :
  Side) (height : Fraction.Rational) :
    sideReal side < (connectorMovingBox side height).xUpper := by
  change sideReal side < sideReal side + 1 / 10
  have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
    (by decide : (0 : Fraction.Rational) < 1 / 10) (sideReal side)
  have scalarZero : (sideReal side) + 0 = (sideReal side) :=
    (Fraction.Field.add_comm (sideReal side) 0).trans (Fraction.Field.zero_add
      (sideReal side))
  rewrite [scalarZero] at translated
  exact translated

/-- The moving-root rectangle's bottom boundary lies strictly below the source height. -/
theorem connectorMovingBox_below (side :
  Side) (height : Fraction.Rational) :
    (connectorMovingBox side height).yLower < height := by
  change height - 1 / 2 < height
  have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
    (by decide : (0 : Fraction.Rational) < 1 / 2) height
  have scalarZero : height - 0 = height := by
    rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
      show -(0 : Fraction.Rational) = 0 by decide]
    exact (Fraction.Field.add_comm height 0).trans (Fraction.Field.zero_add height)
  rewrite [scalarZero] at translated
  exact translated

/-- The moving-root rectangle's top boundary lies strictly above the source height. -/
theorem connectorMovingBox_above (side :
  Side) (height : Fraction.Rational) :
    height < (connectorMovingBox side height).yUpper := by
  change height < height + 1 / 2
  have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
    (by decide : (0 : Fraction.Rational) < 1 / 2) height
  have scalarZero : height + 0 = height :=
    (Fraction.Field.add_comm height 0).trans (Fraction.Field.zero_add height)
  rewrite [scalarZero] at translated
  exact translated

/-- The left connector parameter has real part below zero. -/
theorem leftParameter_left_zero (height : Fraction.Rational) :
    (connectorParameter .left height).re < (Centered.connectorFixedBox
      0).xLower := by
  change (-(1 / 4 : Fraction.Rational)) < -(1 / 16)
  decide

/-- The right connector parameter has positive real part. -/
theorem zero_left_rightParameter (height : Fraction.Rational) :
    (Centered.connectorFixedBox 0).xUpper <
      (connectorParameter .right height).re := by
  change (1 / 16 : Fraction.Rational) < 1 / 4
  decide

/-- The left moving-root box lies strictly left of zero. -/
theorem leftMoving_before_zero (height : Fraction.Rational) :
    (connectorMovingBox .left height).xUpper < (0 : Gaussian.Basic.Canonical).re := by
  change (-(1 / 4 : Fraction.Rational)) + 1 / 10 < 0
  decide

/-- The right moving-root box lies strictly right of zero. -/
theorem zero_before_rightMoving (height : Fraction.Rational) :
    (0 : Gaussian.Basic.Canonical).re < (connectorMovingBox .right height).xLower := by
  change (0 : Fraction.Rational) < 1 / 4 - 1 / 10
  decide

/-- The left moving-root box lies strictly left of one. -/
theorem leftMoving_before_one (height : Fraction.Rational) :
    (connectorMovingBox .left height).xUpper < (1 : Gaussian.Basic.Canonical).re := by
  change (-(1 / 4 : Fraction.Rational)) + 1 / 10 < 1
  decide

/-- The right moving-root box lies strictly left of one. -/
theorem rightMoving_before_one (height : Fraction.Rational) :
    (connectorMovingBox .right height).xUpper < (1 : Gaussian.Basic.Canonical).re := by
  change (1 / 4 : Fraction.Rational) + 1 / 10 < 1
  decide

/-- The moving-root box left of one lies strictly left of one. -/
theorem oneLeftMoving_before_one (height : Fraction.Rational) :
    (connectorMovingBox .oneLeft height).xUpper < (1 : Gaussian.Basic.Canonical).re := by
  change (3 / 4 : Fraction.Rational) + 1 / 10 < 1
  decide

/-- The left connector parameter has real part below one. -/
theorem leftParameter_before_one (height : Fraction.Rational) :
    (connectorParameter .left height).re < (Centered.connectorFixedBox
      1).xLower := by
  change (-(1 / 4 : Fraction.Rational)) < 1 - 1 / 16
  decide

/-- The right connector parameter has real part below one. -/
theorem rightParameter_before_one (height : Fraction.Rational) :
    (connectorParameter .right height).re < (Centered.connectorFixedBox
      1).xLower := by
  change (1 / 4 : Fraction.Rational) < 1 - 1 / 16
  decide

/-- The fixed zero-root box lies strictly left of the fixed one-root box. -/
theorem zeroFixed_before_oneFixed :
    (Centered.connectorFixedBox 0).xUpper < (Centered.connectorFixedBox
      1).xLower := by
  change (1 / 16 : Fraction.Rational) < 1 - 1 / 16
  decide

/-- The fixed zero-root box lies strictly left of one. -/
theorem zeroFixed_before_oneRoot :
    (Centered.connectorFixedBox 0).xUpper < (1 : Gaussian.Basic.Canonical).re := by
  change (1 / 16 : Fraction.Rational) < 1
  decide

/-- The fixed one-root box lies strictly right of zero. -/
theorem zeroRoot_before_oneFixed :
    (0 : Gaussian.Basic.Canonical).re < (Centered.connectorFixedBox 1).xLower := by
  change (0 : Fraction.Rational) < 1 - 1 / 16
  decide

/-- The left moving-root box lies strictly left of the fixed zero-root box. -/
theorem leftMoving_before_zeroFixed (height : Fraction.Rational) :
    (connectorMovingBox .left height).xUpper <
      (Centered.connectorFixedBox 0).xLower := by
  change (-(1 / 4 : Fraction.Rational)) + 1 / 10 < -(1 / 16)
  decide

/-- The right moving-root box lies strictly right of the fixed zero-root box. -/
theorem zeroFixed_before_rightMoving (height : Fraction.Rational) :
    (Centered.connectorFixedBox 0).xUpper <
      (connectorMovingBox .right height).xLower := by
  change (1 / 16 : Fraction.Rational) < 1 / 4 - 1 / 10
  decide

/-- The moving-root box left of one lies strictly right of the fixed zero-root box. -/
theorem zeroFixed_before_oneLeftMoving (height : Fraction.Rational) :
    (Centered.connectorFixedBox 0).xUpper <
      (connectorMovingBox .oneLeft height).xLower := by
  change (1 / 16 : Fraction.Rational) < 3 / 4 - 1 / 10
  decide

/-- The moving-root box right of one lies strictly right of the fixed zero-root box. -/
theorem zeroFixed_before_oneRightMoving (height : Fraction.Rational)
  :
    (Centered.connectorFixedBox 0).xUpper <
      (connectorMovingBox .oneRight height).xLower := by
  change (1 / 16 : Fraction.Rational) < 5 / 4 - 1 / 10
  decide

/-- The moving-root box left of one lies strictly left of the fixed one-root box. -/
theorem oneLeftMoving_before_oneFixed (height : Fraction.Rational) :
    (connectorMovingBox .oneLeft height).xUpper <
      (Centered.connectorFixedBox 1).xLower := by
  change (3 / 4 : Fraction.Rational) + 1 / 10 < 1 - 1 / 16
  decide

/-- The moving-root box right of one lies strictly right of the fixed one-root box. -/
theorem oneFixed_before_oneRightMoving (height : Fraction.Rational) :
    (Centered.connectorFixedBox 1).xUpper <
      (connectorMovingBox .oneRight height).xLower := by
  change (1 + 1 / 16 : Fraction.Rational) < 5 / 4 - 1 / 10
  decide

/-- The connector parameter left of one has real part below one. -/
theorem oneLeftParameter_before_one (height : Fraction.Rational) :
    (connectorParameter .oneLeft height).re <
      (Centered.connectorFixedBox 1).xLower := by
  change (3 / 4 : Fraction.Rational) < 1 - 1 / 16
  decide

/-- The connector parameter right of one has real part above one. -/
theorem one_before_oneRightParameter (height : Fraction.Rational) :
    (Centered.connectorFixedBox 1).xUpper <
      (connectorParameter .oneRight height).re := by
  change (1 + 1 / 16 : Fraction.Rational) < 5 / 4
  decide

/-- The left moving-root box lies strictly left of the fixed one-root box. -/
theorem leftMovingBox_before_oneFixed (height : Fraction.Rational) :
    (connectorMovingBox .left height).xUpper <
      (Centered.connectorFixedBox 1).xLower := by
  change (-(1 / 4 : Fraction.Rational)) + 1 / 10 < 1 - 1 / 16
  decide

/-- The right moving-root box lies strictly left of the fixed one-root box. -/
theorem rightMovingBox_before_oneFixed (height : Fraction.Rational) :
    (connectorMovingBox .right height).xUpper <
      (Centered.connectorFixedBox 1).xLower := by
  change (1 / 4 : Fraction.Rational) + 1 / 10 < 1 - 1 / 16
  decide

/-- The fixed zero-root box and moving-root box are disjoint on every connector side. -/
theorem zero_moving_separated (side :
  Side) (height : Fraction.Rational) :
    (Centered.connectorFixedBox 0).Separated (connectorMovingBox side
      height) := by
  cases side
  · exact Or.inr (Or.inl (leftMoving_before_zeroFixed height))
  · exact Or.inl (zeroFixed_before_rightMoving height)
  · exact Or.inl (zeroFixed_before_oneLeftMoving height)
  · exact Or.inl (zeroFixed_before_oneRightMoving height)

/-- The two fixed root boxes are disjoint. -/
theorem zero_one_separated :
    (Centered.connectorFixedBox 0).Separated (Centered.connectorFixedBox 1) :=
  Or.inl zeroFixed_before_oneFixed

/-- The moving-root box and fixed one-root box are disjoint on every connector side. -/
theorem moving_one_separated (side : Side)
  (height : Fraction.Rational) :
    (connectorMovingBox side height).Separated
      (Centered.connectorFixedBox 1) := by
  cases side
  · exact Or.inl (leftMovingBox_before_oneFixed height)
  · exact Or.inl (rightMovingBox_before_oneFixed height)
  · exact Or.inl (oneLeftMoving_before_oneFixed height)
  · exact Or.inr (Or.inl (oneFixed_before_oneRightMoving height))

/-- Boundary clearance for the moving linear factor on its centered rectangle. -/
@[expose] def movingCenteredClearance (side :
  Side) (height : Fraction.Rational) :
    BoundaryClearance
      (Translated.translatedCoordinate
        (connectorParameter side height))
      (connectorMovingBox side height) :=
  ExplicitLegendreSegment.centeredClearance
    (connectorParameter side height)
    (connectorMovingBox_left side height)
    (connectorMovingBox_right side height)
    (connectorMovingBox_below side height)
    (connectorMovingBox_above side height)

/-- Boundary clearance for the moving factor on the fixed zero-root box. -/
@[expose] def fixedZeroMovingClearance (side :
  Side) (height : Fraction.Rational) :
    BoundaryClearance
      (Translated.translatedCoordinate
        (connectorParameter side height)) (Centered.connectorFixedBox 0)
          := by
  cases side with
  | left =>
    exact ExplicitLegendreSegment.leftClearance _
      (leftParameter_left_zero height)
  | right =>
    exact ExplicitLegendreSegment.rightClearance _
      (zero_left_rightParameter height)
  | oneLeft =>
      exact ExplicitLegendreSegment.rightClearance _
        ((zeroFixed_before_oneLeftMoving height).trans
          (connectorMovingBox_left .oneLeft height))
  | oneRight =>
      exact ExplicitLegendreSegment.rightClearance _
        ((zeroFixed_before_oneRightMoving height).trans
          (connectorMovingBox_left .oneRight height))

/-- Boundary clearance for the zero factor on the moving-root rectangle. -/
@[expose] def movingZeroClearance (side :
  Side) (height : Fraction.Rational) :
    BoundaryClearance (Translated.translatedCoordinate 0)
      (connectorMovingBox side height) := by
  cases side with
  | left =>
    exact ExplicitLegendreSegment.rightClearance 0
      (leftMoving_before_zero height)
  | right =>
    exact ExplicitLegendreSegment.leftClearance 0
      (zero_before_rightMoving height)
  | oneLeft =>
      exact ExplicitLegendreSegment.leftClearance 0
        ((Centered.connectorFixedBox_right 0).trans
          (zeroFixed_before_oneLeftMoving height))
  | oneRight =>
      exact ExplicitLegendreSegment.leftClearance 0
        ((Centered.connectorFixedBox_right 0).trans
          (zeroFixed_before_oneRightMoving height))

/-- Boundary clearance for the one factor on the moving-root rectangle. -/
@[expose] def movingOneClearance (side :
  Side) (height : Fraction.Rational) :
    BoundaryClearance (Translated.translatedCoordinate 1)
      (connectorMovingBox side height) := by
  cases side with
  | left =>
    exact ExplicitLegendreSegment.rightClearance 1
      (leftMoving_before_one height)
  | right =>
    exact ExplicitLegendreSegment.rightClearance 1
      (rightMoving_before_one height)
  | oneLeft =>
    exact ExplicitLegendreSegment.rightClearance 1
      (oneLeftMoving_before_one height)
  | oneRight =>
      exact ExplicitLegendreSegment.leftClearance 1
        ((Centered.connectorFixedBox_right 1).trans
          (oneFixed_before_oneRightMoving height))

/-- Boundary clearance for the moving factor on the fixed one-root box. -/
@[expose] def fixedOneMovingClearance (side :
  Side) (height : Fraction.Rational) :
    BoundaryClearance
      (Translated.translatedCoordinate
        (connectorParameter side height)) (Centered.connectorFixedBox 1)
          := by
  cases side with
  | left =>
    exact ExplicitLegendreSegment.leftClearance _
      (leftParameter_before_one height)
  | right =>
    exact ExplicitLegendreSegment.leftClearance _
      (rightParameter_before_one height)
  | oneLeft =>
    exact ExplicitLegendreSegment.leftClearance _
      (oneLeftParameter_before_one height)
  | oneRight =>
    exact ExplicitLegendreSegment.rightClearance _
      (one_before_oneRightParameter height)

/-- Boundary clearance for the full Legendre polynomial on the fixed zero-root box. -/
@[expose] def zeroClearance (side : Side)
  (height : Fraction.Rational) :
    BoundaryClearance (Legendre.Polynomial.factorsAt
      (connectorParameter side height))
      (Centered.connectorFixedBox 0) := by
  exact Legendre.Polynomial.Clearance.factorsClearance
    (Clearance.Box.Boundary.Translated.centeredSquareSixteenthClearance 0)
    (fixedZeroMovingClearance side height)
    (ExplicitLegendreSegment.rightClearance 1
      zeroFixed_before_oneRoot)

/-- Boundary clearance for the full Legendre polynomial on the moving-root rectangle. -/
@[expose] def movingClearance (side :
  Side) (height : Fraction.Rational) :
    BoundaryClearance (Legendre.Polynomial.factorsAt
      (connectorParameter side height))
      (connectorMovingBox side height) := by
  exact Legendre.Polynomial.Clearance.factorsClearance (movingZeroClearance side height)
    (movingCenteredClearance side height) (movingOneClearance side
      height)

/-- Boundary clearance for the full Legendre polynomial on the fixed one-root box. -/
@[expose] def oneClearance (side : Side)
  (height : Fraction.Rational) :
    BoundaryClearance (Legendre.Polynomial.factorsAt
      (connectorParameter side height))
      (Centered.connectorFixedBox 1) := by
  exact Legendre.Polynomial.Clearance.factorsClearance
    (ExplicitLegendreSegment.leftClearance 0
    zeroRoot_before_oneFixed)
    (fixedOneMovingClearance side height)
      (Clearance.Box.Boundary.Translated.centeredSquareSixteenthClearance 1)

/-- The Legendre polynomial has quadrupled winding four around the fixed zero-root box. -/
theorem zeroWinding (side : Side) (height
  : Fraction.Rational) :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial (connectorParameter side height))
      (Centered.connectorFixedBox 0) = 4 := by
  rw [Legendre.Polynomial.polynomial_eq_factorsAt]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.connectorFixedBox_proper 0)
    (Clearance.Box.Boundary.Translated.centeredSquareSixteenthClearance 0)
    (fixedZeroMovingClearance side height)
    (ExplicitLegendreSegment.rightClearance 1
      zeroFixed_before_oneRoot)
  have fixed : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
      (Centered.connectorFixedBox 0) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate 0
      (Centered.connectorFixedBox_left 0) (Centered.connectorFixedBox_right 0)
      (Centered.connectorFixedBox_below 0) (Centered.connectorFixedBox_above 0)
  have moving : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        (connectorParameter side height)) (Centered.connectorFixedBox 0)
          = 0 := by
    cases side with
    | left =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_left _
          (Centered.connectorFixedBox_proper 0)
          (ExplicitLegendreSegment.leftClearance _
            (leftParameter_left_zero height))
          (leftParameter_left_zero height)
    | right =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_right _
          (Centered.connectorFixedBox_proper 0)
          (ExplicitLegendreSegment.rightClearance _
            (zero_left_rightParameter height))
          (zero_left_rightParameter height)
    | oneLeft =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_right _
          (Centered.connectorFixedBox_proper 0)
          (fixedZeroMovingClearance .oneLeft height)
          ((zeroFixed_before_oneLeftMoving height).trans
            (connectorMovingBox_left .oneLeft height))
    | oneRight =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_right _
          (Centered.connectorFixedBox_proper 0)
          (fixedZeroMovingClearance .oneRight height)
          ((zeroFixed_before_oneRightMoving height).trans
            (connectorMovingBox_left .oneRight height))
  have one : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
      (Centered.connectorFixedBox 0) = 0 :=
    Winding.Affine.HalfPlane.factor_winding_zero_of_right 1 (Centered.connectorFixedBox_proper 0)
      (ExplicitLegendreSegment.rightClearance 1
        zeroFixed_before_oneRoot)
      zeroFixed_before_oneRoot
  rw [fixed, moving, one]
  ring1

/-- The Legendre polynomial has quadrupled winding four around the moving-root box. -/
theorem movingWinding (side : Side)
  (height : Fraction.Rational) :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial (connectorParameter side height))
      (connectorMovingBox side height) = 4 := by
  rw [Legendre.Polynomial.polynomial_eq_factorsAt]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (connectorMovingBox_proper side
    height)
    (movingZeroClearance side height)
    (movingCenteredClearance side height)
    (movingOneClearance side height)
  have zero : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
      (connectorMovingBox side height) = 0 := by
    cases side with
    | left =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_right 0
          (connectorMovingBox_proper .left height)
          (ExplicitLegendreSegment.rightClearance 0
            (leftMoving_before_zero height))
          (leftMoving_before_zero height)
    | right =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_left 0
          (connectorMovingBox_proper .right height)
          (ExplicitLegendreSegment.leftClearance 0
            (zero_before_rightMoving height))
          (zero_before_rightMoving height)
    | oneLeft =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_left 0
          (connectorMovingBox_proper .oneLeft height)
          (movingZeroClearance .oneLeft height)
          ((Centered.connectorFixedBox_right 0).trans
            (zeroFixed_before_oneLeftMoving height))
    | oneRight =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_left 0
          (connectorMovingBox_proper .oneRight height)
          (movingZeroClearance .oneRight height)
          ((Centered.connectorFixedBox_right 0).trans
            (zeroFixed_before_oneRightMoving height))
  have moving : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        (connectorParameter side height))
      (connectorMovingBox side height) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate
      (connectorParameter side height)
      (connectorMovingBox_left side height)
      (connectorMovingBox_right side height)
      (connectorMovingBox_below side height)
      (connectorMovingBox_above side height)
  have one : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
      (connectorMovingBox side height) = 0 := by
    cases side with
    | left =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_right 1
          (connectorMovingBox_proper .left height)
          (movingOneClearance .left height) (leftMoving_before_one
            height)
    | right =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_right 1
          (connectorMovingBox_proper .right height)
          (movingOneClearance .right height)
            (rightMoving_before_one height)
    | oneLeft =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_right 1
          (connectorMovingBox_proper .oneLeft height)
          (movingOneClearance .oneLeft height)
          (oneLeftMoving_before_one height)
    | oneRight =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_left 1
          (connectorMovingBox_proper .oneRight height)
          (movingOneClearance .oneRight height)
          ((Centered.connectorFixedBox_right 1).trans
            (oneFixed_before_oneRightMoving height))
  rw [zero, moving, one]
  ring1

/-- The Legendre polynomial has quadrupled winding four around the fixed one-root box. -/
theorem oneWinding (side : Side) (height :
  Fraction.Rational) :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial (connectorParameter side height))
      (Centered.connectorFixedBox 1) = 4 := by
  rw [Legendre.Polynomial.polynomial_eq_factorsAt]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.connectorFixedBox_proper 1)
    (ExplicitLegendreSegment.leftClearance 0
      zeroRoot_before_oneFixed)
    (fixedOneMovingClearance side height)
    (Clearance.Box.Boundary.Translated.centeredSquareSixteenthClearance 1)
  have zero : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
      (Centered.connectorFixedBox 1) = 0 :=
    Winding.Affine.HalfPlane.factor_winding_zero_of_left 0 (Centered.connectorFixedBox_proper 1)
      (ExplicitLegendreSegment.leftClearance 0
        zeroRoot_before_oneFixed)
      zeroRoot_before_oneFixed
  have moving : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        (connectorParameter side height)) (Centered.connectorFixedBox 1)
          = 0 := by
    cases side with
    | left =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_left _
          (Centered.connectorFixedBox_proper 1)
          (fixedOneMovingClearance .left height)
          (leftParameter_before_one height)
    | right =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_left _
          (Centered.connectorFixedBox_proper 1)
          (fixedOneMovingClearance .right height)
          (rightParameter_before_one height)
    | oneLeft =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_left _
          (Centered.connectorFixedBox_proper 1)
          (fixedOneMovingClearance .oneLeft height)
          (oneLeftParameter_before_one height)
    | oneRight =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_right _
          (Centered.connectorFixedBox_proper 1)
          (fixedOneMovingClearance .oneRight height)
          (one_before_oneRightParameter height)
  have fixed : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
      (Centered.connectorFixedBox 1) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate 1
      (Centered.connectorFixedBox_left 1) (Centered.connectorFixedBox_right 1)
      (Centered.connectorFixedBox_below 1) (Centered.connectorFixedBox_above 1)
  rw [zero, moving, fixed]
  ring1

/-- The retained local owner of the fixed zero root, with its boundary clearance and winding certificate. -/
@[expose] def connectorZeroOwner (side :
  Side) (height : Fraction.Rational) :
    LocalOwner (Legendre.Paths.polynomial (connectorParameter side height))
      :=
  UpperZero.ownerOf (Centered.connectorFixedBox 0)
    (Centered.connectorFixedBox_proper 0)
    (by rw [Legendre.Polynomial.polynomial_eq_factorsAt]; exact zeroClearance side height)
    (zeroWinding side height)

/-- The retained local owner of the moving root, with its original rectangle and winding certificate. -/
@[expose] def connectorMovingOwner (side :
  Side) (height : Fraction.Rational) :
    LocalOwner (Legendre.Paths.polynomial (connectorParameter side height))
      :=
  UpperZero.ownerOf (connectorMovingBox side height)
    (connectorMovingBox_proper side height)
    (by rw [Legendre.Polynomial.polynomial_eq_factorsAt]; exact movingClearance side height)
    (movingWinding side height)

/-- The retained local owner of the fixed one root, with its boundary clearance and winding certificate. -/
@[expose] def connectorOneOwner (side :
  Side) (height : Fraction.Rational) :
    LocalOwner (Legendre.Paths.polynomial (connectorParameter side height))
      :=
  UpperZero.ownerOf (Centered.connectorFixedBox 1)
    (Centered.connectorFixedBox_proper 1)
    (by rw [Legendre.Polynomial.polynomial_eq_factorsAt]; exact oneClearance side height)
    (oneWinding side height)

/-- The three local owners indexed in root order zero, moving parameter, one. -/
@[expose] def connectorOwner (side : Side)
  (height : Fraction.Rational) :
    Fin 3 -> LocalOwner (Legendre.Paths.polynomial (connectorParameter side
      height)) :=
  Data.Fin.cases (connectorZeroOwner side height)
    (fun rest => Data.Fin.cases (connectorMovingOwner side height)
      (fun _ => connectorOneOwner side height) rest)

/-- Distinct connector owner indices have disjoint boxes. -/
theorem connectorOwner_pairwise (side :
  Side) (height : Fraction.Rational) :
    forall left right : Fin 3, left ≠ right ->
      (connectorOwner side height left).box.Separated
        (connectorOwner side height right).box := by
  intro left right different
  rcases Cases.three left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases Cases.three right with rightZero | rightOne | rightTwo <;>
    subst right
  · exact (different rfl).elim
  · exact zero_moving_separated side height
  · exact zero_one_separated
  · exact Rational.Box.separated_symm
      (zero_moving_separated side height)
  · exact (different rfl).elim
  · exact moving_one_separated side height
  · exact Rational.Box.separated_symm zero_one_separated
  · exact Rational.Box.separated_symm
      (moving_one_separated side height)
  · exact (different rfl).elim

/-- The pairwise separated family of the three original connector owners. -/
@[expose] def connectorOwnerFamily (side :
  Side) (height : Fraction.Rational) :
    Owner.Family.Basic.OwnerFamily
      (Legendre.Paths.polynomial (connectorParameter side height)) 3 where
  owner := connectorOwner side height
  pairwiseSeparated := connectorOwner_pairwise side height

/-- Every connector parameter differs from zero, regardless of height. -/
theorem connectorParameter_ne_zero (side :
  Side) (height : Fraction.Rational) :
    connectorParameter side height ≠ 0 := by
  intro equal
  have real := congrArg (fun value : Gaussian.Basic.Canonical => value.re) equal
  cases side
  · change (-(1 / 4 : Fraction.Rational)) = 0 at real
    exact (show (-(1 / 4 : Fraction.Rational)) ≠ 0 by decide) real
  · change (1 / 4 : Fraction.Rational) = 0 at real
    exact (show (1 / 4 : Fraction.Rational) ≠ 0 by decide) real
  · change (3 / 4 : Fraction.Rational) = 0 at real
    exact (show (3 / 4 : Fraction.Rational) ≠ 0 by decide) real
  · change (5 / 4 : Fraction.Rational) = 0 at real
    exact (show (5 / 4 : Fraction.Rational) ≠ 0 by decide) real

/-- Every connector parameter differs from one, regardless of height. -/
theorem connectorParameter_sub_one_ne_zero
    (side : Side) (height : Fraction.Rational) :
    connectorParameter side height - 1 ≠ 0 := by
  intro equal
  have real := congrArg (fun value : Gaussian.Basic.Canonical => value.re) equal
  cases side
  · change (-(1 / 4 : Fraction.Rational)) - 1 = 0 at real
    exact (show (-(1 / 4 : Fraction.Rational)) - 1 ≠ 0 by decide) real
  · change (1 / 4 : Fraction.Rational) - 1 = 0 at real
    exact (show (1 / 4 : Fraction.Rational) - 1 ≠ 0 by decide) real
  · change (3 / 4 : Fraction.Rational) - 1 = 0 at real
    exact (show (3 / 4 : Fraction.Rational) - 1 ≠ 0 by decide) real
  · change (5 / 4 : Fraction.Rational) - 1 = 0 at real
    exact (show (5 / 4 : Fraction.Rational) - 1 ≠ 0 by decide) real

/-- The Legendre polynomial at a connector parameter is squarefree because its three roots are distinct. -/
@[expose] def connectorSquarefree (side :
  Side) (height : Fraction.Rational) :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
      (Legendre.Coefficients.Exact.coefficientTable (connectorParameter side
        height)).polynomial := by
  rw [Legendre.Coefficients.Exact.coefficientTable_polynomial]
  apply Legendre.Squarefree.squarefreeAt
  exact Gaussian.Field.mul_ne_zero_direct
    (Gaussian.Power.pow_ne_zero_direct
      (connectorParameter side height)
      (connectorParameter_ne_zero side height) 2)
    (Gaussian.Power.pow_ne_zero_direct
      (connectorParameter side height - 1)
      (connectorParameter_sub_one_ne_zero side height) 2)

/-- The squarefree cubic isolation request for the displayed connector parameter. -/
@[expose] def connectorIsolationInput (side :
  Side) (height : Fraction.Rational) :
    RootIsolation.FTA.Squarefree.Input
      (Legendre.Coefficients.Exact.coefficientTable (connectorParameter side
        height)).polynomial where
  squarefree := connectorSquarefree side height
  degreeAtLeastTwo := by
    change 2 <= 3
    decide

/-- The chamber formed from the original three connector owners.

Its retained reference maximality comes from the squarefree isolation construction for the same polynomial. -/
@[expose] def connectorChamber (side :
  Side) (height : Fraction.Rational) :
    Progressive.Chamber.Frame.ChamberFrame where
  reference := Legendre.Coefficients.Exact.coefficientTable (connectorParameter side height)
  chamber :=
    { degreeAtLeastTwo := by
        change 2 <= 3
        decide
      squarefree := connectorSquarefree side height
      owners := connectorOwnerFamily side height
      referenceSmall := Legendre.Coefficients.Exact.coefficientTable_allowances_lt _
        (Progressive.Chamber.Target.simpleRootChamberTarget_pos
          (Legendre.Coefficients.Exact.coefficientTable (connectorParameter side height))
          (connectorSquarefree side height)
          (connectorOwnerFamily side height))
      referenceMaximality :=
        (FTA.Squarefree.Build.Box.prove
          (connectorIsolationInput side height)).boxes.maximality }

/-- The connector chamber retains the original parameterized Legendre polynomial. -/
@[simp] theorem connectorChamber_polynomial
    (side : Side) (height : Fraction.Rational) :
    (connectorChamber side height).polynomial =
      Legendre.Paths.polynomial (connectorParameter side height) := rfl

/-- The permutation interchanging the moving and one roots on the line to the right of one. -/
@[expose] def oneRightProjectionOrder :
  Data.Fin.Bijection 3 3 where
  forward :=
    Data.Fin.cases (0)
      (fun rest => Data.Fin.cases (2) (fun _ => 1) rest)
  backward :=
    Data.Fin.cases (0)
      (fun rest => Data.Fin.cases (2) (fun _ => 1) rest)
  backward_forward := by
    intro position
    rcases Cases.three position with positionZero | positionOne |
      positionTwo <;> subst position <;> rfl
  forward_backward := by
    intro position
    rcases Cases.three position with positionZero | positionOne |
      positionTwo <;> subst position <;> rfl

/-- The side-dependent permutation placing the three connector roots in increasing real order. -/
@[expose] def connectorProjectionOrder :
  Side ->
    Data.Fin.Bijection 3 3
  | .left => UpperZero.targetProjectionOrder
  | .right => Data.Fin.Bijection.identity 3
  | .oneLeft => Data.Fin.Bijection.identity 3
  | .oneRight => oneRightProjectionOrder

/-- The original connector owner read through the side's projection permutation. -/
@[expose] def connectorProjectionOwner (side :
  Side) (height : Fraction.Rational)
    (position : Fin 3) :
    LocalOwner (Legendre.Paths.polynomial (connectorParameter side height))
      :=
  connectorOwner side height
    ((connectorProjectionOrder side).forward position)

/-- The projected connector boxes are strictly ordered along the real axis. -/
theorem connectorProjection_xOrdered (side :
  Side) (height : Fraction.Rational) :
    forall left right : Fin 3, left.val < right.val ->
      (connectorProjectionOwner side height left).box.xUpper <
        (connectorProjectionOwner side height right).box.xLower := by
  intro left right order
  cases side with
  | left =>
      rcases Cases.three left with leftZero | leftOne | leftTwo <;>
        subst left <;>
        rcases Cases.three right with rightZero | rightOne | rightTwo <;>
        subst right
      · exact ((by decide : ¬ ((0 : Nat) < 0)) order).elim
      · exact leftMoving_before_zeroFixed height
      · exact leftMovingBox_before_oneFixed height
      · exact ((by decide : ¬ ((1 : Nat) < 0)) order).elim
      · exact ((by decide : ¬ ((1 : Nat) < 1)) order).elim
      · exact zeroFixed_before_oneFixed
      · exact ((by decide : ¬ ((2 : Nat) < 0)) order).elim
      · exact ((by decide : ¬ ((2 : Nat) < 1)) order).elim
      · exact ((by decide : ¬ ((2 : Nat) < 2)) order).elim
  | right =>
      rcases Cases.three left with leftZero | leftOne | leftTwo <;>
        subst left <;>
        rcases Cases.three right with rightZero | rightOne | rightTwo <;>
        subst right
      · exact ((by decide : ¬ ((0 : Nat) < 0)) order).elim
      · exact zeroFixed_before_rightMoving height
      · exact zeroFixed_before_oneFixed
      · exact ((by decide : ¬ ((1 : Nat) < 0)) order).elim
      · exact ((by decide : ¬ ((1 : Nat) < 1)) order).elim
      · exact rightMovingBox_before_oneFixed height
      · exact ((by decide : ¬ ((2 : Nat) < 0)) order).elim
      · exact ((by decide : ¬ ((2 : Nat) < 1)) order).elim
      · exact ((by decide : ¬ ((2 : Nat) < 2)) order).elim
  | oneLeft =>
      rcases Cases.three left with leftZero | leftOne | leftTwo <;>
        subst left <;>
        rcases Cases.three right with rightZero | rightOne | rightTwo <;>
        subst right
      · exact ((by decide : ¬ ((0 : Nat) < 0)) order).elim
      · exact zeroFixed_before_oneLeftMoving height
      · exact zeroFixed_before_oneFixed
      · exact ((by decide : ¬ ((1 : Nat) < 0)) order).elim
      · exact ((by decide : ¬ ((1 : Nat) < 1)) order).elim
      · exact oneLeftMoving_before_oneFixed height
      · exact ((by decide : ¬ ((2 : Nat) < 0)) order).elim
      · exact ((by decide : ¬ ((2 : Nat) < 1)) order).elim
      · exact ((by decide : ¬ ((2 : Nat) < 2)) order).elim
  | oneRight =>
      rcases Cases.three left with leftZero | leftOne | leftTwo <;>
        subst left <;>
        rcases Cases.three right with rightZero | rightOne | rightTwo <;>
        subst right
      · exact ((by decide : ¬ ((0 : Nat) < 0)) order).elim
      · exact zeroFixed_before_oneFixed
      · exact zeroFixed_before_oneRightMoving height
      · exact ((by decide : ¬ ((1 : Nat) < 0)) order).elim
      · exact ((by decide : ¬ ((1 : Nat) < 1)) order).elim
      · exact oneFixed_before_oneRightMoving height
      · exact ((by decide : ¬ ((2 : Nat) < 0)) order).elim
      · exact ((by decide : ¬ ((2 : Nat) < 1)) order).elim
      · exact ((by decide : ¬ ((2 : Nat) < 2)) order).elim

/-- The root-labeled connector frame with the original chamber and its real-axis projection order. -/
@[expose] def connectorFrame (side : Side)
  (height : Fraction.Rational) :
    Legendre.Paths.Frame (connectorParameter side height) where
  chamber := connectorChamber side height
  polynomial_eq := rfl
  labels := Data.Fin.Bijection.identity 3
  owner_contains := by
    intro label
    rcases Cases.three label with labelZero | labelOne | labelTwo
    · subst label
      change (Centered.connectorFixedBox 0).Contains 0
      exact Centered.connectorFixedBox_contains 0
    · subst label
      exact connectorMovingBox_contains side height
    · subst label
      change (Centered.connectorFixedBox 1).Contains 1
      exact Centered.connectorFixedBox_contains 1
  projectionOrder := connectorProjectionOrder side
  projectionOwner := fun position =>
    Owner.Local.Transport.castOwner
      (connectorChamber_polynomial side height).symm
      (connectorProjectionOwner side height position)
  projection_refines := by
    intro position
    change (connectorProjectionOwner side height position).box.Refines
      (connectorOwner side height
        ((connectorProjectionOrder side).forward position)).box
    exact Rational.Box.refines_refl _
  projection_xOrdered := connectorProjection_xOrdered side height

/-! ## One uniform descending stationary cell -/

/-- The exact rational connector descent increment 1/12. -/
@[expose] def stepSize : Fraction.Rational := 1 / 12

/-- The height obtained by subtracting one connector increment. -/
@[expose] def nextHeight (height : Fraction.Rational) :
  Fraction.Rational := height - stepSize

/-- One connector descent strictly decreases the height. -/
theorem nextHeight_lt (height : Fraction.Rational) :
  nextHeight height < height := by
  unfold nextHeight stepSize
  have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
    (by decide : (0 : Fraction.Rational) < 1 / 12) height
  have scalarZero : height - 0 = height := by
    rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
      show -(0 : Fraction.Rational) = 0 by decide]
    exact (Fraction.Field.add_comm height 0).trans (Fraction.Field.zero_add height)
  rewrite [scalarZero] at translated
  exact translated

/-- The common moving-root rectangle between adjacent descent heights.

It retains the horizontal bounds and intersects the two vertical intervals. -/
@[expose] def connectorMovingBridgeBox (side :
  Side) (height : Fraction.Rational) : Rational.Box where
  xLower := sideReal side - 1 / 10
  xUpper := sideReal side + 1 / 10
  yLower := height - 1 / 2
  yUpper := nextHeight height + 1 / 2
  x_valid := by
    exact (connectorMovingBox_proper side height).1.le
  y_valid := by
    apply le_of_lt
    apply Fraction.Order.Arithmetic.lt_of_sub_pos_direct
    rw [show nextHeight height + 1 / 2 - (height - 1 / 2) =
        1 / 2 + 1 / 2 - stepSize by
      unfold nextHeight
      ring1]
    unfold stepSize
    decide

/-- The common moving-root bridge rectangle has positive width and height. -/
theorem connectorMovingBridgeBox_proper
    (side : Side) (height : Fraction.Rational) :
    (connectorMovingBridgeBox side height).Proper := by
  constructor
  · exact (connectorMovingBox_proper side height).1
  · apply Fraction.Order.Arithmetic.lt_of_sub_pos_direct
    change 0 < nextHeight height + 1 / 2 - (height - 1 / 2)
    rw [show nextHeight height + 1 / 2 - (height - 1 / 2) =
        1 / 2 + 1 / 2 - stepSize by
      unfold nextHeight
      ring1]
    unfold stepSize
    decide

/-- The common moving-root bridge rectangle's left boundary lies strictly left of the parameter. -/
theorem connectorMovingBridgeBox_left
    (side : Side) (height : Fraction.Rational) :
    (connectorMovingBridgeBox side height).xLower < sideReal side
      :=
  connectorMovingBox_left side height

/-- The common moving-root bridge rectangle's right boundary lies strictly right of the parameter. -/
theorem connectorMovingBridgeBox_right
    (side : Side) (height : Fraction.Rational) :
    sideReal side < (connectorMovingBridgeBox side height).xUpper
      :=
  connectorMovingBox_right side height

/-- The common moving-root bridge rectangle's bottom boundary lies strictly below the source height. -/
theorem connectorMovingBridgeBox_below
    (side : Side) (height : Fraction.Rational) :
    (connectorMovingBridgeBox side height).yLower < height :=
  connectorMovingBox_below side height

/-- The common moving-root bridge rectangle's top boundary lies strictly above the source height. -/
theorem connectorMovingBridgeBox_above
    (side : Side) (height : Fraction.Rational) :
    height < (connectorMovingBridgeBox side height).yUpper := by
  apply Fraction.Order.Arithmetic.lt_of_sub_pos_direct
  change 0 < nextHeight height + 1 / 2 - height
  rw [show nextHeight height + 1 / 2 - height =
      1 / 2 - stepSize by
    unfold nextHeight
    ring1]
  unfold stepSize
  decide

/-- The moving-root bridge rectangle lies inside the source moving-root rectangle. -/
theorem connectorMovingBridgeBox_refines_source
    (side : Side) (height : Fraction.Rational) :
    (connectorMovingBridgeBox side height).Refines
      (connectorMovingBox side height) := by
  constructor
  · exact le_rfl
  constructor
  · exact le_rfl
  constructor
  · exact le_rfl
  · exact Fraction.Order.Arithmetic.add_le_add_right_direct
      (nextHeight_lt height).le (1 / 2)

/-- The moving-root bridge rectangle lies inside the target moving-root rectangle. -/
theorem connectorMovingBridgeBox_refines_target
    (side : Side) (height : Fraction.Rational) :
    (connectorMovingBridgeBox side height).Refines
      (connectorMovingBox side (nextHeight height)) := by
  constructor
  · exact le_rfl
  constructor
  · exact le_rfl
  constructor
  · exact Fraction.Order.Arithmetic.sub_le_sub_right_direct
      (nextHeight_lt height).le (1 / 2)
  · exact le_rfl

/-- Clearance for the source moving factor on the common bridge rectangle. -/
@[expose] def bridgeMovingCenteredClearance (side :
  Side) (height : Fraction.Rational) :
    BoundaryClearance
      (Translated.translatedCoordinate
        (connectorParameter side height))
      (connectorMovingBridgeBox side height) :=
  ExplicitLegendreSegment.centeredClearance
    (connectorParameter side height)
    (connectorMovingBridgeBox_left side height)
    (connectorMovingBridgeBox_right side height)
    (connectorMovingBridgeBox_below side height)
    (connectorMovingBridgeBox_above side height)

/-- Clearance for the fixed zero factor on the common bridge rectangle. -/
@[expose] def bridgeMovingZeroClearance (side :
  Side) (height : Fraction.Rational) :
    BoundaryClearance (Translated.translatedCoordinate 0)
      (connectorMovingBridgeBox side height) := by
  cases side with
  | left => exact ExplicitLegendreSegment.rightClearance 0 (by
      change (-(1 / 4 : Fraction.Rational)) + 1 / 10 < 0
      decide)
  | right => exact ExplicitLegendreSegment.leftClearance 0 (by
      change (0 : Fraction.Rational) < 1 / 4 - 1 / 10
      decide)
  | oneLeft => exact ExplicitLegendreSegment.leftClearance 0 (by
      change (0 : Fraction.Rational) < 3 / 4 - 1 / 10
      decide)
  | oneRight => exact ExplicitLegendreSegment.leftClearance 0 (by
      change (0 : Fraction.Rational) < 5 / 4 - 1 / 10
      decide)

/-- Clearance for the fixed one factor on the common bridge rectangle. -/
@[expose] def bridgeMovingOneClearance (side :
  Side) (height : Fraction.Rational) :
    BoundaryClearance (Translated.translatedCoordinate 1)
      (connectorMovingBridgeBox side height) := by
  cases side with
  | left => exact ExplicitLegendreSegment.rightClearance 1 (by
      change (-(1 / 4 : Fraction.Rational)) + 1 / 10 < 1
      decide)
  | right => exact ExplicitLegendreSegment.rightClearance 1 (by
      change (1 / 4 : Fraction.Rational) + 1 / 10 < 1
      decide)
  | oneLeft => exact ExplicitLegendreSegment.rightClearance 1 (by
      change (3 / 4 : Fraction.Rational) + 1 / 10 < 1
      decide)
  | oneRight => exact ExplicitLegendreSegment.leftClearance 1 (by
      change (1 : Fraction.Rational) < 5 / 4 - 1 / 10
      decide)

/-- Clearance for the product of all three Legendre factors on the common bridge rectangle. -/
@[expose] def bridgeMovingFactorsClearance (side :
  Side) (height : Fraction.Rational) :
    BoundaryClearance (Legendre.Polynomial.factorsAt
      (connectorParameter side height))
      (connectorMovingBridgeBox side height) := by
  exact Legendre.Polynomial.Clearance.factorsClearance (bridgeMovingZeroClearance side
    height)
    (bridgeMovingCenteredClearance side height)
    (bridgeMovingOneClearance side height)

/-- The source Legendre polynomial has quadrupled winding four on the common moving-root bridge rectangle. -/
theorem bridgeMovingWinding (side : Side)
  (height : Fraction.Rational) :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial (connectorParameter side height))
      (connectorMovingBridgeBox side height) = 4 := by
  rw [Legendre.Polynomial.polynomial_eq_factorsAt]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum
    (connectorMovingBridgeBox_proper side height)
    (bridgeMovingZeroClearance side height)
    (bridgeMovingCenteredClearance side height)
    (bridgeMovingOneClearance side height)
  have zero : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
      (connectorMovingBridgeBox side height) = 0 := by
    cases side with
    | left =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_right 0
          (connectorMovingBridgeBox_proper .left height)
          (ExplicitLegendreSegment.rightClearance 0 (by
            change (-(1 / 4 : Fraction.Rational)) + 1 / 10 < 0
            decide))
          (by
            change (-(1 / 4 : Fraction.Rational)) + 1 / 10 < 0
            decide)
    | right =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_left 0
          (connectorMovingBridgeBox_proper .right height)
          (ExplicitLegendreSegment.leftClearance 0 (by
            change (0 : Fraction.Rational) < 1 / 4 - 1 / 10
            decide))
          (by
            change (0 : Fraction.Rational) < 1 / 4 - 1 / 10
            decide)
    | oneLeft =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_left 0
          (connectorMovingBridgeBox_proper .oneLeft height)
          (bridgeMovingZeroClearance .oneLeft height)
          (by
            change (0 : Fraction.Rational) < 3 / 4 - 1 / 10
            decide)
    | oneRight =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_left 0
          (connectorMovingBridgeBox_proper .oneRight height)
          (bridgeMovingZeroClearance .oneRight height)
          (by
            change (0 : Fraction.Rational) < 5 / 4 - 1 / 10
            decide)
  have moving : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        (connectorParameter side height))
      (connectorMovingBridgeBox side height) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate
      (connectorParameter side height)
      (connectorMovingBridgeBox_left side height)
      (connectorMovingBridgeBox_right side height)
      (connectorMovingBridgeBox_below side height)
      (connectorMovingBridgeBox_above side height)
  have one : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
      (connectorMovingBridgeBox side height) = 0 := by
    cases side with
    | left =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_right 1
          (connectorMovingBridgeBox_proper .left height)
          (bridgeMovingOneClearance .left height) (by
            change (-(1 / 4 : Fraction.Rational)) + 1 / 10 < 1
            decide)
    | right =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_right 1
          (connectorMovingBridgeBox_proper .right height)
          (bridgeMovingOneClearance .right height) (by
            change (1 / 4 : Fraction.Rational) + 1 / 10 < 1
            decide)
    | oneLeft =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_right 1
          (connectorMovingBridgeBox_proper .oneLeft height)
          (bridgeMovingOneClearance .oneLeft height) (by
            change (3 / 4 : Fraction.Rational) + 1 / 10 < 1
            decide)
    | oneRight =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_left 1
          (connectorMovingBridgeBox_proper .oneRight height)
          (bridgeMovingOneClearance .oneRight height) (by
            change (1 : Fraction.Rational) < 5 / 4 - 1 / 10
            decide)
  rw [zero, moving, one]
  ring1

/-- The local moving-root owner on the common rectangle used for one descent bridge. -/
@[expose] def bridgeMovingOwner (side :
  Side) (height : Fraction.Rational) :
    LocalOwner (Legendre.Paths.polynomial (connectorParameter side height))
      :=
  UpperZero.ownerOf (connectorMovingBridgeBox side height)
    (connectorMovingBridgeBox_proper side height)
    (by
      rw [Legendre.Polynomial.polynomial_eq_factorsAt]
      exact bridgeMovingFactorsClearance side height)
    (bridgeMovingWinding side height)

/-- The squared norm of a connector parameter step equals the square of 1/12. -/
theorem connectorStep_displacement (side :
  Side) (height : Fraction.Rational) :
    Norm.Basic.normSq
      (connectorParameter side height -
        connectorParameter side (nextHeight height)) =
          stepSize ^ 2 := by
  cases side <;>
    simp only [connectorParameter, sideReal,
      Legendre.Paths.gaussian, nextHeight, stepSize,
      Norm.Basic.normSq,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im] <;>
    ring1

/-- The moving-factor clearance retained on the fixed zero-root box for one connector step. -/
@[expose] def zeroMovingFactorClearance (side :
  Side) (height : Fraction.Rational) :
    BoundaryClearance
      (Translated.translatedCoordinate
      (connectorParameter side height)) (Centered.connectorFixedBox 0) :=
  fixedZeroMovingClearance side height

/-- The moving-factor clearance retained on the fixed one-root box for one connector step. -/
@[expose] def oneMovingFactorClearance (side :
  Side) (height : Fraction.Rational) :
    BoundaryClearance
      (Translated.translatedCoordinate
      (connectorParameter side height)) (Centered.connectorFixedBox 1) :=
  fixedOneMovingClearance side height

/-- A connector step's squared displacement is below the moving-factor clearance on the zero-root box. -/
theorem zero_displacementSmall (side :
  Side) (height : Fraction.Rational) :
    Norm.Basic.normSq
        (connectorParameter side height -
          connectorParameter side (nextHeight height)) <
      (zeroMovingFactorClearance side height).bound := by
  rw [connectorStep_displacement]
  cases side
  · change stepSize ^ 2 <
      ((-(1 / 16 : Fraction.Rational)) - (-(1 / 4 : Fraction.Rational))) ^ 2
    unfold stepSize
    decide
  · change stepSize ^ 2 <
      ((1 / 4 : Fraction.Rational) - 1 / 16) ^ 2
    unfold stepSize
    decide
  · change stepSize ^ 2 <
      ((3 / 4 : Fraction.Rational) - 1 / 16) ^ 2
    unfold stepSize
    decide
  · change stepSize ^ 2 <
      ((5 / 4 : Fraction.Rational) - 1 / 16) ^ 2
    unfold stepSize
    decide

/-- A connector step's squared displacement is below the moving-factor clearance on the common bridge rectangle. -/
theorem moving_displacementSmall (side :
  Side) (height : Fraction.Rational) :
    Norm.Basic.normSq
        (connectorParameter side height -
          connectorParameter side (nextHeight height)) <
      (bridgeMovingCenteredClearance side height).bound := by
  rw [connectorStep_displacement]
  change stepSize ^ 2 <
    min ((sideReal side - (sideReal side - 1 / 10)) ^ 2)
      (min ((sideReal side + 1 / 10 - sideReal side) ^ 2)
        (min ((height - (height - 1 / 2)) ^ 2)
          ((nextHeight height + 1 / 2 - height) ^ 2)))
  rw [show sideReal side - (sideReal side - 1 / 10) =
      (1 / 10 : Fraction.Rational) by ring1,
    show sideReal side + 1 / 10 - sideReal side =
      (1 / 10 : Fraction.Rational) by ring1,
    show height - (height - 1 / 2) = (1 / 2 : Fraction.Rational) by ring1,
    show nextHeight height + 1 / 2 - height = 1 / 2 - stepSize by
      unfold nextHeight
      ring1]
  unfold stepSize
  decide

/-- A connector step's squared displacement is below the moving-factor clearance on the one-root box. -/
theorem one_displacementSmall (side :
  Side) (height : Fraction.Rational) :
    Norm.Basic.normSq
        (connectorParameter side height -
          connectorParameter side (nextHeight height)) <
      (oneMovingFactorClearance side height).bound := by
  rw [connectorStep_displacement]
  cases side
  · change stepSize ^ 2 <
      ((1 - 1 / 16 : Fraction.Rational) - (-(1 / 4 : Fraction.Rational))) ^ 2
    unfold stepSize
    decide
  · change stepSize ^ 2 <
      ((1 - 1 / 16 : Fraction.Rational) - 1 / 4) ^ 2
    unfold stepSize
    decide
  · change stepSize ^ 2 <
      ((1 - 1 / 16 : Fraction.Rational) - 3 / 4) ^ 2
    unfold stepSize
    decide
  · change stepSize ^ 2 <
      ((5 / 4 : Fraction.Rational) - (1 + 1 / 16)) ^ 2
    unfold stepSize
    decide

/-- The exact polynomial perturbation produced by lowering the connector parameter one step. -/
@[expose] def connectorPerturbation (side :
  Side) (height : Fraction.Rational) :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  Legendre.Polynomial.perturbationAt (connectorParameter side height)
    (connectorParameter side (nextHeight height))

/-- An oriented Rouché certificate for a connector step from the supplied owner and its boundary dominance witness. -/
@[expose] def connectorOrientedRouche (side :
  Side) (height : Fraction.Rational)
    (owner : LocalOwner (Legendre.Paths.polynomial (connectorParameter side
      height)))
    (dominance : BoundaryNormDominance
      (Legendre.Paths.polynomial (connectorParameter side height))
      (connectorPerturbation side height) owner.box) :
    Box.Rouche.Connection.OrientedRouche
      (Legendre.Paths.polynomial (connectorParameter side height))
      (Legendre.Paths.polynomial (connectorParameter side
        (nextHeight height)))
      owner.box where
  perturbation := connectorPerturbation side height
  target_eq_add := Legendre.Polynomial.target_eq_source_add_perturbationAt _ _
  dominance := dominance

/-- The connector perturbation is dominated on the fixed zero-root boundary. -/
@[expose] def connectorZeroDominance (side :
  Side) (height : Fraction.Rational) :
    BoundaryNormDominance
      (Legendre.Paths.polynomial (connectorParameter side height))
      (connectorPerturbation side height)
      (connectorZeroOwner side height).box :=
  Legendre.Rouche.factorMoveDominanceAt _ _
    (Clearance.Box.Boundary.Translated.centeredSquareSixteenthClearance 0)
    (zeroMovingFactorClearance side height)
    (ExplicitLegendreSegment.rightClearance 1
      zeroFixed_before_oneRoot)
    (zero_displacementSmall side height)

/-- The connector perturbation is dominated on the common moving-root boundary. -/
@[expose] def connectorMovingDominance (side :
  Side) (height : Fraction.Rational) :
    BoundaryNormDominance
      (Legendre.Paths.polynomial (connectorParameter side height))
      (connectorPerturbation side height)
      (bridgeMovingOwner side height).box := by
  apply Legendre.Rouche.factorMoveDominanceAt _ _
    (bridgeMovingZeroClearance side height)
    (bridgeMovingCenteredClearance side height)
    (bridgeMovingOneClearance side height)
  exact moving_displacementSmall side height

/-- The connector perturbation is dominated on the fixed one-root boundary. -/
@[expose] def connectorOneDominance (side :
  Side) (height : Fraction.Rational) :
    BoundaryNormDominance
      (Legendre.Paths.polynomial (connectorParameter side height))
      (connectorPerturbation side height)
      (connectorOneOwner side height).box :=
  Legendre.Rouche.factorMoveDominanceAt _ _
    (ExplicitLegendreSegment.leftClearance 0
      zeroRoot_before_oneFixed)
    (oneMovingFactorClearance side height)
    (Clearance.Box.Boundary.Translated.centeredSquareSixteenthClearance 1)
    (one_displacementSmall side height)

/-- The forward Rouché bridge retaining the fixed zero-root owner across one descent step. -/
@[expose] def connectorZeroBridge (side :
  Side) (height : Fraction.Rational) :
    OwnerBridge
      (Legendre.Paths.polynomial (connectorParameter side height))
      (Legendre.Paths.polynomial (connectorParameter side
        (nextHeight height))) :=
  OwnerBridge.ofForward
    (connectorZeroOwner side height)
    (connectorOrientedRouche side height (connectorZeroOwner side
      height)
      (connectorZeroDominance side height))

/-- The forward Rouché bridge retaining the common moving-root rectangle across one descent step. -/
@[expose] def connectorMovingBridge (side :
  Side) (height : Fraction.Rational) :
    OwnerBridge
      (Legendre.Paths.polynomial (connectorParameter side height))
      (Legendre.Paths.polynomial (connectorParameter side
        (nextHeight height))) :=
  OwnerBridge.ofForward
    (bridgeMovingOwner side height)
    (connectorOrientedRouche side height (bridgeMovingOwner side
      height)
      (connectorMovingDominance side height))

/-- The forward Rouché bridge retaining the fixed one-root owner across one descent step. -/
@[expose] def connectorOneBridge (side :
  Side) (height : Fraction.Rational) :
    OwnerBridge
      (Legendre.Paths.polynomial (connectorParameter side height))
      (Legendre.Paths.polynomial (connectorParameter side
        (nextHeight height))) :=
  OwnerBridge.ofForward
    (connectorOneOwner side height)
    (connectorOrientedRouche side height (connectorOneOwner side
      height)
      (connectorOneDominance side height))

/-- The three descent bridges indexed in the original root-label order. -/
@[expose] def connectorBridgeAt (side :
  Side) (height : Fraction.Rational) :
    Fin 3 -> OwnerBridge
      (Legendre.Paths.polynomial (connectorParameter side height))
      (Legendre.Paths.polynomial (connectorParameter side
        (nextHeight height))) :=
  Data.Fin.cases (connectorZeroBridge side height)
    (fun rest => Data.Fin.cases (connectorMovingBridge side height)
      (fun _ => connectorOneBridge side height) rest)

/-- The identity matching between consecutive connector chambers.

Each retained bridge refines its original source and target boxes. -/
@[expose] def connectorChamberOverlap (side :
  Side) (height : Fraction.Rational) :
    Progressive.Chamber.Overlap.ChamberOverlap
      (connectorChamber side height)
      (connectorChamber side (nextHeight height)) where
  matching := Data.Fin.Bijection.identity 3
  bridge := connectorBridgeAt side height
  bridge_refines_left := by
    intro index
    rcases Cases.three index with indexZero | indexOne | indexTwo
    · subst index
      exact Rational.Box.refines_refl _
    · subst index
      exact connectorMovingBridgeBox_refines_source side height
    · subst index
      exact Rational.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rcases Cases.three index with indexZero | indexOne | indexTwo
    · subst index
      exact Rational.Box.refines_refl _
    · subst index
      exact connectorMovingBridgeBox_refines_target side height
    · subst index
      exact Rational.Box.refines_refl _

/-- The stationary projected overlap for one connector step, preserving the original root order. -/
@[expose] def connectorProjectedOverlap (side :
  Side) (height : Fraction.Rational) :
    ProjectedOverlap
      (connectorFrame side height).projected
      (connectorFrame side (nextHeight height)).projected :=
  .stationary (connectorChamberOverlap side height) (by
    intro position
    change (connectorProjectionOrder side).forward position =
      (connectorProjectionOrder side).forward position
    rfl)

/-- One connector step contributes no braid letters. -/
@[simp] theorem connectorProjectedOverlap_word
    (side : Side) (height : Fraction.Rational) :
    (connectorProjectedOverlap side height).word = [] := rfl

/-- The minimum of the six retained left and right clearance bounds for one connector step. -/
@[expose] def connectorSheetBound (side :
  Side) (height : Fraction.Rational) : Fraction.Rational :=
  min (connectorZeroBridge side height).leftClearance.bound
    (min (connectorZeroBridge side height).rightClearance.bound
      (min (connectorMovingBridge side height).leftClearance.bound
        (min (connectorMovingBridge side height).rightClearance.bound
          (min (connectorOneBridge side height).leftClearance.bound
            (connectorOneBridge side height).rightClearance.bound))))

/-- The common connector sheet bound is positive. -/
theorem connectorSheetBound_positive (side :
  Side) (height : Fraction.Rational) :
    0 < connectorSheetBound side height := by
  unfold connectorSheetBound
  exact Fraction.Order.Basic.lt_min (connectorZeroBridge side height).leftClearance.positive
    (Fraction.Order.Basic.lt_min (connectorZeroBridge side height).rightClearance.positive
      (Fraction.Order.Basic.lt_min (connectorMovingBridge side height).leftClearance.positive
        (Fraction.Order.Basic.lt_min (connectorMovingBridge side
          height).rightClearance.positive
          (Fraction.Order.Basic.lt_min (connectorOneBridge side
            height).leftClearance.positive
            (connectorOneBridge side height).rightClearance.positive))))

/-- A single positive bound below every retained bridge clearance at both ends of a connector step. -/
@[expose] def connectorSheetClearance (side :
  Side) (height : Fraction.Rational) :
    Legendre.Paths.BridgeClearance (connectorFrame side height)
      (connectorFrame side (nextHeight height))
      (connectorChamberOverlap side height) where
  bound := connectorSheetBound side height
  positive := connectorSheetBound_positive side height
  leftLower := by
    intro index
    rcases Cases.three index with indexZero | indexOne | indexTwo
    · subst index
      exact Fraction.Order.Basic.min_le_left _ _
    · subst index
      exact (Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))
    · subst index
      exact (Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans
          ((Fraction.Order.Basic.min_le_right _ _).trans
            ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))))
  rightLower := by
    intro index
    rcases Cases.three index with indexZero | indexOne | indexTwo
    · subst index
      exact (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)
    · subst index
      exact (Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans
          ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)))
    · subst index
      exact (Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans
          ((Fraction.Order.Basic.min_le_right _ _).trans
            ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _))))

/-- The vertical parameter segment from the original height to the next descent height. -/
@[expose] def connectorGeometry (side :
  Side) (height : Fraction.Rational) :
    Legendre.Paths.AxisSegment (connectorParameter side height)
      (connectorParameter side (nextHeight height)) :=
  .vertical (sideReal side) height (nextHeight height)

/-- The vertical connector segment avoids zero and one with squared-distance lower bound 1/16. -/
@[expose] def connectorGeometrySafe (side :
  Side) (height : Fraction.Rational) :
    Legendre.Paths.AxisSegment.Safe (connectorGeometry side height) where
  avoidsZero :=
    { bound := 1 / 16
      positive := by decide
      lower := by
        cases side
        · change (1 / 16 : Fraction.Rational) <= (-(1 / 4) - 0) ^ 2
          decide
        · change (1 / 16 : Fraction.Rational) <= (1 / 4 - 0) ^ 2
          decide
        · change (1 / 16 : Fraction.Rational) <= (3 / 4 - 0) ^ 2
          decide
        · change (1 / 16 : Fraction.Rational) <= (5 / 4 - 0) ^ 2
          decide }
  avoidsOne :=
    { bound := 1 / 16
      positive := by decide
      lower := by
        cases side
        · change (1 / 16 : Fraction.Rational) <= (-(1 / 4) - 1) ^ 2
          decide
        · change (1 / 16 : Fraction.Rational) <= (1 / 4 - 1) ^ 2
          decide
        · change (1 / 16 : Fraction.Rational) <= (3 / 4 - 1) ^ 2
          decide
        · change (1 / 16 : Fraction.Rational) <= (5 / 4 - 1) ^ 2
          decide }

/-- One certified vertical descent by the rational height 1/12.

The segment retains its safe geometry, stationary projected overlap and common sheet clearance. -/
@[expose] def connectorSegment (side :
  Side) (height : Fraction.Rational) :
    Legendre.Paths.Segment (connectorFrame side height)
      (connectorFrame side (nextHeight height)) :=
  Legendre.Paths.Segment.ofProjectedOverlap (connectorGeometry side height)
    (connectorGeometrySafe side height)
    (connectorProjectedOverlap side height)
    (connectorSheetClearance side height)

/-- A descending connector segment has no crossings. -/
@[simp] theorem connectorSegment_crossings
    (side : Side) (height : Fraction.Rational) :
    (connectorSegment side height).crossings = [] := rfl

/-! ## Stationary changes from the crossing frames -/

/-- The polynomials agree at the upper left crossing-to-connector interface. -/
theorem topLeftPolynomial_eq :
    UpperZero.targetChamber.polynomial = (connectorChamber .left
      2).polynomial := by
  rw [UpperZero.targetChamber_polynomial,
    connectorChamber_polynomial]
  rfl

/-- The polynomials agree at the lower left crossing-to-connector interface. -/
theorem bottomLeftPolynomial_eq :
    (connectorChamber .left (-2)).polynomial =
      LowerZero.lowerLeftChamber.polynomial := by
  rw [connectorChamber_polynomial,
    LowerZero.lowerLeftChamber_polynomial]
  rfl

/-- The polynomials agree at the lower right crossing-to-connector interface. -/
theorem bottomRightPolynomial_eq :
    LowerZero.lowerRightChamber.polynomial =
      (connectorChamber .right (-2)).polynomial := by
  rw [LowerZero.lowerRightChamber_polynomial,
    connectorChamber_polynomial]
  rfl

/-- The polynomials agree at the upper right crossing-to-connector interface. -/
theorem topRightPolynomial_eq :
    (connectorChamber .right 2).polynomial =
      UpperZero.sourceChamber.polynomial := by
  rw [connectorChamber_polynomial,
    UpperZero.sourceChamber_polynomial]
  rfl

/-- The reflexive local-owner bridge from the upper crossing frame to the connector frame, transported along the
original polynomial equality. -/
@[expose] def topLeftBridge (index : Fin 3) :
  OwnerBridge
    UpperZero.targetChamber.polynomial (connectorChamber .left
      2).polynomial :=
  @OwnerBridge.cast
    (connectorChamber .left 2).polynomial
      UpperZero.targetChamber.polynomial
    (connectorChamber .left 2).polynomial
    (connectorChamber .left 2).polynomial
    topLeftPolynomial_eq.symm rfl
    (OwnerBridge.reflexive
      (connectorOwner .left 2 index))

/-- The reflexive local-owner bridge from the connector frame to the lower crossing frame, transported along the
original polynomial equality. -/
@[expose] def bottomLeftBridge (index : Fin 3) :
  OwnerBridge
    (connectorChamber .left (-2)).polynomial
      LowerZero.lowerLeftChamber.polynomial :=
  @OwnerBridge.cast
    (connectorChamber .left (-2)).polynomial
    (connectorChamber .left (-2)).polynomial
    (connectorChamber .left (-2)).polynomial
      LowerZero.lowerLeftChamber.polynomial
    rfl bottomLeftPolynomial_eq
    (OwnerBridge.reflexive
      (connectorOwner .left (-2) index))

/-- The reflexive local-owner bridge from the lower crossing frame to the connector frame, transported along the
original polynomial equality. -/
@[expose] def bottomRightBridge (index : Fin 3) :
  OwnerBridge
    LowerZero.lowerRightChamber.polynomial
      (connectorChamber .right (-2)).polynomial :=
  @OwnerBridge.cast
    (connectorChamber .right (-2)).polynomial
      LowerZero.lowerRightChamber.polynomial
    (connectorChamber .right (-2)).polynomial
    (connectorChamber .right (-2)).polynomial
    bottomRightPolynomial_eq.symm rfl
    (OwnerBridge.reflexive
      (connectorOwner .right (-2) index))

/-- The reflexive local-owner bridge from the connector frame to the upper crossing frame, transported along the
original polynomial equality. -/
@[expose] def topRightBridge (index : Fin 3) :
  OwnerBridge
    (connectorChamber .right 2).polynomial
      UpperZero.sourceChamber.polynomial :=
  @OwnerBridge.cast
    (connectorChamber .right 2).polynomial
    (connectorChamber .right 2).polynomial
    (connectorChamber .right 2).polynomial
      UpperZero.sourceChamber.polynomial
    rfl topRightPolynomial_eq
    (OwnerBridge.reflexive
      (connectorOwner .right 2 index))

/-- The upper left transition bridge retains the original connector-owner box. -/
@[simp] theorem topLeftBridge_box (index : Fin 3) :
    (topLeftBridge index).box = (connectorOwner .left 2 index).box
      := by
  unfold topLeftBridge
  exact OwnerBridge.cast_box _ _ _

/-- The lower left transition bridge retains the original connector-owner box. -/
@[simp] theorem bottomLeftBridge_box (index : Fin 3) :
    (bottomLeftBridge index).box =
      (connectorOwner .left (-2) index).box := by
  unfold bottomLeftBridge
  exact OwnerBridge.cast_box _ _ _

/-- The lower right transition bridge retains the original connector-owner box. -/
@[simp] theorem bottomRightBridge_box (index : Fin 3) :
    (bottomRightBridge index).box =
      (connectorOwner .right (-2) index).box := by
  unfold bottomRightBridge
  exact OwnerBridge.cast_box _ _ _

/-- The upper right transition bridge retains the original connector-owner box. -/
@[simp] theorem topRightBridge_box (index : Fin 3) :
    (topRightBridge index).box = (connectorOwner .right 2
      index).box := by
  unfold topRightBridge
  exact OwnerBridge.cast_box _ _ _

/-- The identity-matched chamber overlap from the upper crossing frame to the connector frame.

Each bridge retains the original connector box and its refinement into the crossing box. -/
@[expose] def topLeftOverlap :
  Progressive.Chamber.Overlap.ChamberOverlap
    UpperZero.targetChamber (connectorChamber .left 2) where
  matching := Data.Fin.Bijection.identity 3
  bridge := topLeftBridge
  bridge_refines_left := by
    intro index
    rcases Cases.three index with indexZero | indexOne | indexTwo
    · subst index
      rw [topLeftBridge_box]
      exact ⟨by decide, by decide, by decide, by decide⟩
    · subst index
      rw [topLeftBridge_box]
      exact ⟨by decide, by decide, by decide, by decide⟩
    · subst index
      rw [topLeftBridge_box]
      exact ⟨by decide, by decide, by decide, by decide⟩
  bridge_refines_right := by
    intro index
    rw [topLeftBridge_box]
    exact Rational.Box.refines_refl _

/-- The identity-matched chamber overlap from the connector frame to the lower crossing frame.

Each bridge retains the original connector box and its refinement into the crossing box. -/
@[expose] def bottomLeftOverlap :
  Progressive.Chamber.Overlap.ChamberOverlap
    (connectorChamber .left (-2)) LowerZero.lowerLeftChamber where
  matching := Data.Fin.Bijection.identity 3
  bridge := bottomLeftBridge
  bridge_refines_left := by
    intro index
    rw [bottomLeftBridge_box]
    exact Rational.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rcases Cases.three index with indexZero | indexOne | indexTwo
    · subst index
      rw [bottomLeftBridge_box]
      exact ⟨by decide, by decide, by decide, by decide⟩
    · subst index
      rw [bottomLeftBridge_box]
      exact ⟨by decide, by decide, by decide, by decide⟩
    · subst index
      rw [bottomLeftBridge_box]
      exact ⟨by decide, by decide, by decide, by decide⟩

/-- The identity-matched chamber overlap from the lower crossing frame to the connector frame.

Each bridge retains the original connector box and its refinement into the crossing box. -/
@[expose] def bottomRightOverlap :
  Progressive.Chamber.Overlap.ChamberOverlap
    LowerZero.lowerRightChamber (connectorChamber .right (-2))
      where
  matching := Data.Fin.Bijection.identity 3
  bridge := bottomRightBridge
  bridge_refines_left := by
    intro index
    rcases Cases.three index with indexZero | indexOne | indexTwo
    · subst index
      rw [bottomRightBridge_box]
      exact ⟨by decide, by decide, by decide, by decide⟩
    · subst index
      rw [bottomRightBridge_box]
      exact ⟨by decide, by decide, by decide, by decide⟩
    · subst index
      rw [bottomRightBridge_box]
      exact ⟨by decide, by decide, by decide, by decide⟩
  bridge_refines_right := by
    intro index
    rw [bottomRightBridge_box]
    exact Rational.Box.refines_refl _

/-- The identity-matched chamber overlap from the connector frame to the upper crossing frame.

Each bridge retains the original connector box and its refinement into the crossing box. -/
@[expose] def topRightOverlap :
  Progressive.Chamber.Overlap.ChamberOverlap
    (connectorChamber .right 2) UpperZero.sourceChamber where
  matching := Data.Fin.Bijection.identity 3
  bridge := topRightBridge
  bridge_refines_left := by
    intro index
    rw [topRightBridge_box]
    exact Rational.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rcases Cases.three index with indexZero | indexOne | indexTwo
    · subst index
      rw [topRightBridge_box]
      exact ⟨by decide, by decide, by decide, by decide⟩
    · subst index
      rw [topRightBridge_box]
      exact ⟨by decide, by decide, by decide, by decide⟩
    · subst index
      rw [topRightBridge_box]
      exact ⟨by decide, by decide, by decide, by decide⟩

/-- The upper left overlap selects the original transition bridge at every index. -/
@[simp] theorem topLeftOverlap_bridge (index : Fin 3) :
    topLeftOverlap.bridge index = topLeftBridge index := rfl

/-- The lower left overlap selects the original transition bridge at every index. -/
@[simp] theorem bottomLeftOverlap_bridge (index : Fin 3) :
    bottomLeftOverlap.bridge index = bottomLeftBridge index := rfl

/-- The lower right overlap selects the original transition bridge at every index. -/
@[simp] theorem bottomRightOverlap_bridge (index : Fin 3) :
    bottomRightOverlap.bridge index = bottomRightBridge index :=
      rfl

/-- The upper right overlap selects the original transition bridge at every index. -/
@[simp] theorem topRightOverlap_bridge (index : Fin 3) :
    topRightOverlap.bridge index = topRightBridge index := rfl

/-- The left clearance bound of the upper left bridge equals the original connector-owner bound. -/
@[simp] theorem topLeftBridge_leftClearance_bound (index : Fin 3) :
    (topLeftBridge index).leftClearance.bound =
      (connectorOwner .left 2 index).clearance.bound := by
  unfold topLeftBridge
  rw [OwnerBridge.cast_leftClearance_bound]
  rfl

/-- The right clearance bound of the upper left bridge equals the original connector-owner bound. -/
@[simp] theorem topLeftBridge_rightClearance_bound (index : Fin 3) :
    (topLeftBridge index).rightClearance.bound =
      (connectorOwner .left 2 index).clearance.bound := by
  unfold topLeftBridge
  rw [OwnerBridge.cast_rightClearance_bound]
  rfl

/-- The left clearance bound of the upper right bridge equals the original connector-owner bound. -/
@[simp] theorem topRightBridge_leftClearance_bound (index : Fin 3) :
    (topRightBridge index).leftClearance.bound =
      (connectorOwner .right 2 index).clearance.bound := by
  unfold topRightBridge
  rw [OwnerBridge.cast_leftClearance_bound]
  rfl

/-- The right clearance bound of the upper right bridge equals the original connector-owner bound. -/
@[simp] theorem topRightBridge_rightClearance_bound (index : Fin 3) :
    (topRightBridge index).rightClearance.bound =
      (connectorOwner .right 2 index).clearance.bound := by
  unfold topRightBridge
  rw [OwnerBridge.cast_rightClearance_bound]
  rfl

/-- The left clearance bound of the upper left overlap equals the original connector-owner bound. -/
@[simp] theorem topLeftOverlap_leftClearance_bound (index : Fin 3) :
    (topLeftOverlap.bridge index).leftClearance.bound =
      (connectorOwner .left 2 index).clearance.bound := by
  rw [topLeftOverlap_bridge, topLeftBridge_leftClearance_bound]

/-- The right clearance bound of the upper left overlap equals the original connector-owner bound. -/
@[simp] theorem topLeftOverlap_rightClearance_bound (index : Fin 3) :
    (topLeftOverlap.bridge index).rightClearance.bound =
      (connectorOwner .left 2 index).clearance.bound := by
  rw [topLeftOverlap_bridge, topLeftBridge_rightClearance_bound]

/-- The left clearance bound of the lower left overlap equals the original connector-owner bound. -/
@[simp] theorem bottomLeftOverlap_leftClearance_bound (index : Fin 3)
  :
    (bottomLeftOverlap.bridge index).leftClearance.bound =
      (connectorOwner .left (-2) index).clearance.bound := by
  rw [bottomLeftOverlap_bridge]
  unfold bottomLeftBridge
  rw [OwnerBridge.cast_leftClearance_bound]
  rfl

/-- The right clearance bound of the lower left overlap equals the original connector-owner bound. -/
@[simp] theorem bottomLeftOverlap_rightClearance_bound (index : Fin
  3) :
    (bottomLeftOverlap.bridge index).rightClearance.bound =
      (connectorOwner .left (-2) index).clearance.bound := by
  rw [bottomLeftOverlap_bridge]
  unfold bottomLeftBridge
  rw [OwnerBridge.cast_rightClearance_bound]
  rfl

/-- The left clearance bound of the lower right overlap equals the original connector-owner bound. -/
@[simp] theorem bottomRightOverlap_leftClearance_bound (index : Fin
  3) :
    (bottomRightOverlap.bridge index).leftClearance.bound =
      (connectorOwner .right (-2) index).clearance.bound := by
  rw [bottomRightOverlap_bridge]
  unfold bottomRightBridge
  rw [OwnerBridge.cast_leftClearance_bound]
  rfl

/-- The right clearance bound of the lower right overlap equals the original connector-owner bound. -/
@[simp] theorem bottomRightOverlap_rightClearance_bound (index : Fin
  3) :
    (bottomRightOverlap.bridge index).rightClearance.bound =
      (connectorOwner .right (-2) index).clearance.bound := by
  rw [bottomRightOverlap_bridge]
  unfold bottomRightBridge
  rw [OwnerBridge.cast_rightClearance_bound]
  rfl

/-- The left clearance bound of the upper right overlap equals the original connector-owner bound. -/
@[simp] theorem topRightOverlap_leftClearance_bound (index : Fin 3) :
    (topRightOverlap.bridge index).leftClearance.bound =
      (connectorOwner .right 2 index).clearance.bound := by
  rw [topRightOverlap_bridge, topRightBridge_leftClearance_bound]

/-- The right clearance bound of the upper right overlap equals the original connector-owner bound. -/
@[simp] theorem topRightOverlap_rightClearance_bound (index : Fin 3)
  :
    (topRightOverlap.bridge index).rightClearance.bound =
      (connectorOwner .right 2 index).clearance.bound := by
  rw [topRightOverlap_bridge, topRightBridge_rightClearance_bound]

/-- The stationary projected overlap from the upper crossing frame to the connector frame, preserving the real-axis root
order. -/
@[expose] def topLeftProjectedOverlap :
  ProjectedOverlap
    UpperZero.targetFrame.projected (connectorFrame .left
      2).projected :=
  .stationary topLeftOverlap (by
    intro position
    change (connectorProjectionOrder .left).forward position =
      (connectorProjectionOrder .left).forward position
    rfl)

/-- The stationary projected overlap from the connector frame to the lower crossing frame, preserving the real-axis root
order. -/
@[expose] def bottomLeftProjectedOverlap :
    ProjectedOverlap
      (connectorFrame .left (-2)).projected
        LowerZero.lowerLeftFrame.projected :=
  .stationary bottomLeftOverlap (by
    intro position
    change (connectorProjectionOrder .left).forward position =
      (connectorProjectionOrder .left).forward position
    rfl)

/-- The stationary projected overlap from the lower crossing frame to the connector frame, preserving the real-axis root
order. -/
@[expose] def bottomRightProjectedOverlap :
    ProjectedOverlap
      LowerZero.lowerRightFrame.projected (connectorFrame .right
        (-2)).projected :=
  .stationary bottomRightOverlap (by
    intro position
    change (connectorProjectionOrder .right).forward position =
      (connectorProjectionOrder .right).forward position
    rfl)

/-- The stationary projected overlap from the connector frame to the upper crossing frame, preserving the real-axis root
order. -/
@[expose] def topRightProjectedOverlap :
  ProjectedOverlap
    (connectorFrame .right 2).projected
      UpperZero.sourceFrame.projected :=
  .stationary topRightOverlap (by
    intro position
    change (connectorProjectionOrder .right).forward position =
      (connectorProjectionOrder .right).forward position
    rfl)

/-- The minimum of the three original connector-owner clearance bounds. -/
@[expose] def transitionSheetBound (side :
  Side) (height : Fraction.Rational) : Fraction.Rational :=
  min (connectorZeroOwner side height).clearance.bound
    (min (connectorMovingOwner side height).clearance.bound
      (connectorOneOwner side height).clearance.bound)

/-- The common bound for a stationary frame change is positive. -/
theorem transitionSheetBound_positive (side :
  Side) (height : Fraction.Rational) :
    0 < transitionSheetBound side height := by
  unfold transitionSheetBound
  exact Fraction.Order.Basic.lt_min (connectorZeroOwner side height).clearance.positive
    (Fraction.Order.Basic.lt_min (connectorMovingOwner side height).clearance.positive
      (connectorOneOwner side height).clearance.positive)

/-- The common stationary-transition bound is below each original connector-owner clearance. -/
theorem transitionSheetBound_le (side :
  Side) (height : Fraction.Rational)
    (index : Fin 3) :
    transitionSheetBound side height <=
      (connectorOwner side height index).clearance.bound := by
  rcases Cases.three index with indexZero | indexOne | indexTwo
  · subst index
    exact Fraction.Order.Basic.min_le_left _ _
  · subst index
    exact (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)
  · subst index
    exact (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)

/-- The positive sheet clearance from the upper crossing frame to the connector frame, bounded by each retained
local-owner clearance. -/
@[expose] def topLeftSheetClearance :
    Legendre.Paths.BridgeClearance UpperZero.targetFrame
      (connectorFrame .left 2)
      topLeftOverlap where
  bound := transitionSheetBound .left 2
  positive := transitionSheetBound_positive .left 2
  leftLower := by
    intro index
    rw [topLeftOverlap_leftClearance_bound]
    exact transitionSheetBound_le .left 2 index
  rightLower := by
    intro index
    rw [topLeftOverlap_rightClearance_bound]
    exact transitionSheetBound_le .left 2 index

/-- The positive sheet clearance from the connector frame to the lower crossing frame, bounded by each retained
local-owner clearance. -/
@[expose] def bottomLeftSheetClearance :
    Legendre.Paths.BridgeClearance (connectorFrame .left (-2))
      LowerZero.lowerLeftFrame
      bottomLeftOverlap where
  bound := transitionSheetBound .left (-2)
  positive := transitionSheetBound_positive .left (-2)
  leftLower := by
    intro index
    rw [bottomLeftOverlap_leftClearance_bound]
    exact transitionSheetBound_le .left (-2) index
  rightLower := by
    intro index
    rw [bottomLeftOverlap_rightClearance_bound]
    exact transitionSheetBound_le .left (-2) index

/-- The positive sheet clearance from the lower crossing frame to the connector frame, bounded by each retained
local-owner clearance. -/
@[expose] def bottomRightSheetClearance :
    Legendre.Paths.BridgeClearance LowerZero.lowerRightFrame
      (connectorFrame .right (-2))
      bottomRightOverlap where
  bound := transitionSheetBound .right (-2)
  positive := transitionSheetBound_positive .right (-2)
  leftLower := by
    intro index
    rw [bottomRightOverlap_leftClearance_bound]
    exact transitionSheetBound_le .right (-2) index
  rightLower := by
    intro index
    rw [bottomRightOverlap_rightClearance_bound]
    exact transitionSheetBound_le .right (-2) index

/-- The positive sheet clearance from the connector frame to the upper crossing frame, bounded by each retained
local-owner clearance. -/
@[expose] def topRightSheetClearance :
    Legendre.Paths.BridgeClearance (connectorFrame .right 2)
      UpperZero.sourceFrame
      topRightOverlap where
  bound := transitionSheetBound .right 2
  positive := transitionSheetBound_positive .right 2
  leftLower := by
    intro index
    rw [topRightOverlap_leftClearance_bound]
    exact transitionSheetBound_le .right 2 index
  rightLower := by
    intro index
    rw [topRightOverlap_rightClearance_bound]
    exact transitionSheetBound_le .right 2 index

/-- The constant vertical parameter segment at the selected side and height. -/
@[expose] def stationaryGeometry (side :
  Side) (height : Fraction.Rational) :
    Legendre.Paths.AxisSegment (connectorParameter side height)
      (connectorParameter side height) :=
  .vertical (sideReal side) height height

/-- The constant connector segment avoids both critical parameters with bound 1/16. -/
@[expose] def stationaryGeometrySafe (side :
  Side) (height : Fraction.Rational) :
    Legendre.Paths.AxisSegment.Safe (stationaryGeometry side height) where
  avoidsZero :=
    { bound := 1 / 16
      positive := by decide
      lower := by
        cases side
        · change (1 / 16 : Fraction.Rational) <= (-(1 / 4) - 0) ^ 2
          decide
        · change (1 / 16 : Fraction.Rational) <= (1 / 4 - 0) ^ 2
          decide
        · change (1 / 16 : Fraction.Rational) <= (3 / 4 - 0) ^ 2
          decide
        · change (1 / 16 : Fraction.Rational) <= (5 / 4 - 0) ^ 2
          decide }
  avoidsOne :=
    { bound := 1 / 16
      positive := by decide
      lower := by
        cases side
        · change (1 / 16 : Fraction.Rational) <= (-(1 / 4) - 1) ^ 2
          decide
        · change (1 / 16 : Fraction.Rational) <= (1 / 4 - 1) ^ 2
          decide
        · change (1 / 16 : Fraction.Rational) <= (3 / 4 - 1) ^ 2
          decide
        · change (1 / 16 : Fraction.Rational) <= (5 / 4 - 1) ^ 2
          decide }

/-- The stationary frame-change segment from the upper crossing frame to the connector frame.

Its parameter is constant and its original owner bridges retain a common positive sheet bound. -/
@[expose] def topLeftTransition : Legendre.Paths.Segment
  UpperZero.targetFrame (connectorFrame .left 2) :=
  Legendre.Paths.Segment.ofProjectedOverlap (stationaryGeometry .left 2)
    (stationaryGeometrySafe .left 2) topLeftProjectedOverlap
    topLeftSheetClearance

/-- The stationary frame-change segment from the connector frame to the lower crossing frame.

Its parameter is constant and its original owner bridges retain a common positive sheet bound. -/
@[expose] def bottomLeftTransition :
    Legendre.Paths.Segment (connectorFrame .left (-2))
      LowerZero.lowerLeftFrame :=
  Legendre.Paths.Segment.ofProjectedOverlap (stationaryGeometry .left (-2))
    (stationaryGeometrySafe .left (-2)) bottomLeftProjectedOverlap
    bottomLeftSheetClearance

/-- The stationary frame-change segment from the lower crossing frame to the connector frame.

Its parameter is constant and its original owner bridges retain a common positive sheet bound. -/
@[expose] def bottomRightTransition :
    Legendre.Paths.Segment LowerZero.lowerRightFrame
      (connectorFrame .right (-2)) :=
  Legendre.Paths.Segment.ofProjectedOverlap (stationaryGeometry .right (-2))
    (stationaryGeometrySafe .right (-2))
      bottomRightProjectedOverlap
    bottomRightSheetClearance

/-- The stationary frame-change segment from the connector frame to the upper crossing frame.

Its parameter is constant and its original owner bridges retain a common positive sheet bound. -/
@[expose] def topRightTransition : Legendre.Paths.Segment
  (connectorFrame .right 2) UpperZero.sourceFrame :=
  Legendre.Paths.Segment.ofProjectedOverlap (stationaryGeometry .right 2)
    (stationaryGeometrySafe .right 2) topRightProjectedOverlap
    topRightSheetClearance

/-- The upper left stationary frame change has no crossings. -/
@[simp] theorem topLeftTransition_crossings :
    topLeftTransition.crossings = [] := rfl

/-- The lower left stationary frame change has no crossings. -/
@[simp] theorem bottomLeftTransition_crossings :
    bottomLeftTransition.crossings = [] := rfl

/-- The lower right stationary frame change has no crossings. -/
@[simp] theorem bottomRightTransition_crossings :
    bottomRightTransition.crossings = [] := rfl

/-- The upper right stationary frame change has no crossings. -/
@[simp] theorem topRightTransition_crossings :
    topRightTransition.crossings = [] := rfl

/-! ## Forty-eight-cell side paths -/

/-- The height after a specified number of exact 1/12 descents. -/
@[expose] def descendHeight : Nat -> Fraction.Rational ->
  Fraction.Rational
  | 0, height => height
  | count + 1, height => descendHeight count
    (nextHeight height)

/-- The recursively retained path of certified vertical descent segments.

Its endpoint is the frame at the recursively computed final height. -/
@[expose] def descendingPath (side : Side)
  :
    (count : Nat) -> (height : Fraction.Rational) ->
      Legendre.Paths.Path (connectorFrame side height)
        (connectorFrame side (descendHeight count height))
  | 0, height => .nil (connectorFrame side height)
  | count + 1, height =>
      .cons (connectorSegment side height)
        (descendingPath side count (nextHeight
          height))

/-- The retained descending path has exactly the requested number of steps. -/
@[simp] theorem descendingPath_stepCount
    (side : Side) (count : Nat) (height : Fraction.Rational) :
    (descendingPath side count height).stepCount = count := by
  induction count generalizing height with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [descendingPath, Legendre.Paths.Path.stepCount]
      exact congrArg (fun value : Nat => value + 1)
        (inductionHypothesis (nextHeight height))

/-- Every finite descending connector path has the empty braid word. -/
@[simp] theorem descendingPath_word
    (side : Side) (count : Nat) (height : Fraction.Rational) :
    (descendingPath side count height).word = [] := by
  induction count generalizing height with
  | zero => rfl
  | succ count inductionHypothesis =>
      change (descendingPath side count (nextHeight height)).word
        = []
      exact inductionHypothesis (nextHeight height)

/-- Repeated connector descent subtracts the count times the exact step size. -/
theorem descendHeight_eq (count : Nat) (height : Fraction.Rational) :
    descendHeight count height =
      height - (count : Fraction.Rational) * stepSize := by
  induction count generalizing height with
  | zero =>
      change height = height - (0 : Fraction.Rational) * stepSize
      rewrite [MulZeroClass.zero_mul, Fraction.Arithmetic.sub_eq_add_neg_direct,
        show -(0 : Fraction.Rational) = 0 by decide]
      exact ((Fraction.Field.add_comm height 0).trans (Fraction.Field.zero_add height)).symm
  | succ count inductionHypothesis =>
      rw [descendHeight, inductionHypothesis]
      unfold nextHeight
      rw [Nat.cast_succ]
      ring1

/-- Forty-eight descents take height two to height minus two. -/
theorem descendHeight_fortyEight :
  descendHeight 48 2 = -2 := by
  rw [descendHeight_eq]
  unfold stepSize
  have castFortyEight : ((48 : Nat) : Fraction.Rational) =
      (4 : Fraction.Rational) * (12 : Fraction.Rational) := by
    rw [show (48 : Nat) = 4 * 12 by decide, Algebra.NatCast.mul]
    decide
  rw [castFortyEight]
  calc
    (2 : Fraction.Rational) - (4 * 12) * (1 / 12) =
        (2 : Fraction.Rational) - 4 * (12 * (1 / 12)) := by ring1
    _ = (2 : Fraction.Rational) - 4 * 1 := by
      rw [show (12 : Fraction.Rational) * (1 / 12) = 1 by decide]
    _ = (-(2 : Fraction.Rational)) := by ring1

/-- Transport a connector path along equality of its final heights, retaining its initial frame and path data. -/
@[expose] def castConnectorPathFinish {start :
  Gaussian.Basic.Canonical} {left : Legendre.Paths.Frame start}
    {side : Side} {source target : Fraction.Rational}
    (same : source = target)
    (path : Legendre.Paths.Path left (connectorFrame side source)) :
    Legendre.Paths.Path left (connectorFrame side target) := by
  subst target
  exact path

/-- Transport of the final connector height preserves the step count. -/
@[simp] theorem castConnectorPathFinish_stepCount
    {start : Gaussian.Basic.Canonical} {left : Legendre.Paths.Frame start}
    {side : Side} {source target : Fraction.Rational}
    (same : source = target)
    (path : Legendre.Paths.Path left (connectorFrame side source)) :
    (castConnectorPathFinish same path).stepCount = path.stepCount := by
  subst target
  rfl

/-- Transport of the final connector height preserves the braid word. -/
@[simp] theorem castConnectorPathFinish_word
    {start : Gaussian.Basic.Canonical} {left : Legendre.Paths.Frame start}
    {side : Side} {source target : Fraction.Rational}
    (same : source = target)
    (path : Legendre.Paths.Path left (connectorFrame side source)) :
    (castConnectorPathFinish same path).word = path.word := by
  subst target
  rfl

/-- The complete forty-eight-step connector descent from height two to minus two. -/
@[expose] def sideDescent (side : Side) :
    Legendre.Paths.Path (connectorFrame side 2) (connectorFrame
      side (-2)) :=
  castConnectorPathFinish descendHeight_fortyEight
    (descendingPath side 48 2)

/-- A complete connector descent has forty-eight steps. -/
@[simp] theorem sideDescent_stepCount (side :
  Side) :
    (sideDescent side).stepCount = 48 := by
  rw [sideDescent, castConnectorPathFinish_stepCount,
    descendingPath_stepCount]

/-- A complete connector descent has the empty braid word. -/
@[simp] theorem sideDescent_word (side :
  Side) :
    (sideDescent side).word = [] := by
  rw [sideDescent, castConnectorPathFinish_word,
    descendingPath_word]

/-- The certified ascent from minus two to two obtained by reversing the retained side descent. -/
@[expose] def sideAscent (side : Side) :
    Legendre.Paths.Path (connectorFrame side (-2)) (connectorFrame
      side 2) :=
  (sideDescent side).reverse

/-- A complete connector ascent has the empty braid word. -/
@[simp] theorem sideAscent_word (side :
  Side) :
    (sideAscent side).word = [] := by
  rw [sideAscent, Legendre.Paths.Path.word_reverse,
    sideDescent_word]
  rfl

/-! ## The closed standard loop around zero -/

/-- The path from the upper crossing's left frame to the lower crossing's left frame.

It retains both stationary frame transitions around the complete side descent. -/
@[expose] def leftConnector : Legendre.Paths.Path
  UpperZero.targetFrame LowerZero.lowerLeftFrame :=
  .cons topLeftTransition
    ((sideDescent .left).append
      (.cons bottomLeftTransition (.nil LowerZero.lowerLeftFrame)))

/-- The complete left connector has the empty braid word. -/
@[simp] theorem leftConnector_word :
  leftConnector.word = [] := by
  rw [leftConnector]
  simp only [-eq_self, -iff_self, Legendre.Paths.Path.word, topLeftTransition_crossings,
    Legendre.Paths.Path.word_append, sideDescent_word,
      bottomLeftTransition_crossings,
    Append.append_nil]

  rfl

/-- The path from the lower crossing's right frame to the upper crossing's right frame.

It retains both stationary frame transitions around the reversed side descent. -/
@[expose] def rightConnector : Legendre.Paths.Path
  LowerZero.lowerRightFrame UpperZero.sourceFrame :=
  .cons bottomRightTransition
    ((sideAscent .right).append
      (.cons topRightTransition (.nil UpperZero.sourceFrame)))

/-- The complete right connector has the empty braid word. -/
@[simp] theorem rightConnector_word :
  rightConnector.word = [] := by
  rw [rightConnector]
  simp only [-eq_self, -iff_self, Legendre.Paths.Path.word, bottomRightTransition_crossings,
    Legendre.Paths.Path.word_append, sideAscent_word,
      topRightTransition_crossings,
    Append.append_nil]

  rfl

/-- The closed Legendre path based at 1/4 + 2i.

Two certified positive crossings are joined by the original stationary left and right connector paths. -/
@[expose] def zeroLoopPath : Legendre.Paths.Path
  UpperZero.sourceFrame UpperZero.sourceFrame :=
  UpperZero.path.append
    (leftConnector.append (LowerZero.lowerPath.append
      rightConnector))

/-- The closed connector path has exactly the displayed braid word around zero. -/
@[simp] theorem zeroLoopPath_word :
  zeroLoopPath.word =
    Legendre.Monodromy.zeroBraid := by
  rw [zeroLoopPath, Legendre.Paths.Path.word_append, Legendre.Paths.Path.word_append,
    Legendre.Paths.Path.word_append,
    UpperZero.path_word, leftConnector_word,
      LowerZero.lowerPath_word, rightConnector_word]
  rfl

/-- The braid word of the retained zero loop is equivalent to the displayed zero braid. -/
theorem zeroLoopWord : Knot.Braid.Artin.Equivalent
  zeroLoopPath.word
    Legendre.Monodromy.zeroBraid := by
  rw [zeroLoopPath_word]
  exact .refl _

end Purelib.Examples.Curves.Legendre.Connectors

end
