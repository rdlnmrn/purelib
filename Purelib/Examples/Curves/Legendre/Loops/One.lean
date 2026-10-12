module
import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.Data.Fin.Cases
import Purelib.Data.Fin
import Purelib.Data.List.Append
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Progressive.Chamber.Target
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Legendre.Coefficients.Exact
import Purelib.Curves.Legendre.Conventions
import Purelib.Curves.Legendre.Monodromy
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Polynomial
import Purelib.Curves.Legendre.Polynomial.Clearance
import Purelib.Curves.Legendre.Polynomial.Winding
import Purelib.Curves.Legendre.Rouche
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Examples.Curves.Legendre.Connectors
import Purelib.Examples.Curves.Legendre.Crossings.UpperZero
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Translated
import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Polynomial.Winding.Affine.HalfPlane
import Purelib.Polynomial.Winding.Box.Affine
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Rouche.Connection
import Purelib.RootIsolation.FTA.Squarefree.Build
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Owner.Bridge.Rouche
import Purelib.RootIsolation.Owner.Bridge.Transport
import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.RootIsolation.Progressive.Braid.Projected.Overlap
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.Topology.Knot.Braid.Artin
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Separation
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
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

namespace Purelib.Examples.Curves.Legendre.Loops.One

open Purelib.Polynomial.Clearance.Box.Boundary.Translated
open Purelib.Polynomial.Winding
open Purelib.Data.Gaussian
open Purelib.Data.Fin
open Purelib.RootIsolation.Progressive.Braid.Projected.Overlap (ProjectedOverlap)
open Purelib.Polynomial.Clearance.Box.Dominance.Basic (BoundaryNormDominance)

open Purelib.Curves
open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Geometry
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Topology

open Purelib.Examples.Curves.Legendre
open Purelib.Examples.Curves.Legendre.Crossings

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)
open Purelib.RootIsolation.Owner.Local.Basic (LocalOwner)
open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)
open Purelib.Polynomial.Dense.Gaussian.Linear
open Purelib.Geometry.Rational.Box.Square

/-- The upper or lower horizontal crossing level of the rectangle around one. -/
inductive Level
  /-- The horizontal crossing level at height two. -/ | upper
  /-- The horizontal crossing level at height minus two. -/ | lower
deriving @[expose] DecidableEq
derive_exposed_repr Level

/-- The left or right endpoint position of a horizontal crossing around one. -/
inductive Position
  /-- The crossing endpoint with real coordinate three quarters. -/ | left
  /-- The crossing endpoint with real coordinate five quarters. -/ | right
deriving @[expose] DecidableEq
derive_exposed_repr Position

/-- The crossing height, two on the upper edge and minus two on the lower edge. -/
@[expose] def levelHeight : Level -> Fraction.Rational
  | .upper => 2
  | .lower => -2

/-- The connector side at real coordinate three quarters or five quarters. -/
@[expose] def connectorSide : Position -> Connectors.Side
  | .left => .oneLeft
  | .right => .oneRight

/-- The Legendre parameter at the selected crossing level and endpoint. -/
@[expose] def crossingParameter (level : Level) (position : Position) : Gaussian.Basic.Canonical :=
  Connectors.connectorParameter (connectorSide position) (levelHeight level)

/-- The crossing parameter has the real coordinate of its original connector side. -/
@[simp] theorem crossingParameter_re (level : Level) (position : Position) :
    (crossingParameter level position).re = Connectors.sideReal (connectorSide position) :=
  rfl

/-- The crossing parameter has the selected crossing height. -/
@[simp] theorem crossingParameter_im (level : Level) (position : Position) :
    (crossingParameter level position).im = levelHeight level := rfl

/-! ## Broad crossing owners -/

/-- The broad moving-root box covering both endpoints of a horizontal crossing.

Its horizontal interval is [−1, 2] and its vertical radius is one around the selected height. -/
@[expose] def crossingMovingBox (level : Level) : Rational.Box where
  xLower := -1
  xUpper := 2
  yLower := levelHeight level - 1
  yUpper := levelHeight level + 1
  x_valid := by decide
  y_valid := by cases level <;> decide

/-- The broad crossing rectangle has positive width and height. -/
theorem crossingMovingBox_proper (level : Level) :
    (crossingMovingBox level).Proper := by
  constructor
  · change (-1 : Fraction.Rational) < 2
    decide
  · cases level <;> decide

/-- The broad crossing rectangle contains both original moving-root endpoints. -/
theorem crossingMovingBox_contains (level : Level) (position : Position) :
    (crossingMovingBox level).Contains
      (crossingParameter level position) := by
  cases level <;> cases position <;> decide

/-- The moving linear factor has boundary clearance on the broad crossing rectangle. -/
@[expose] def crossingMovingCenteredClearance (level : Level) (position : Position) :
    BoundaryClearance
      (Translated.translatedCoordinate
        (crossingParameter level position)) (crossingMovingBox level) :=
  ExplicitLegendreSegment.centeredClearance (crossingParameter level position)
    (by cases level <;> cases position <;> decide)
    (by cases level <;> cases position <;> decide)
    (by cases level <;> cases position <;> decide)
    (by cases level <;> cases position <;> decide)

/-- The moving factor has clearance on the fixed zero-root box at each crossing endpoint. -/
@[expose] def movingOnZeroBoxClearance (level : Level) (position : Position) :
    BoundaryClearance
      (Translated.translatedCoordinate
        (crossingParameter level position)) (Centered.connectorFixedBox 0) := by
  cases level with
  | upper =>
    exact ExplicitLegendreSegment.aboveClearance _ (by cases position <;> decide)
  | lower =>
    exact ExplicitLegendreSegment.belowClearance _ (by cases position <;> decide)

/-- The moving factor has clearance on the fixed one-root box at each crossing endpoint. -/
@[expose] def movingOnOneBoxClearance (level : Level) (position : Position) :
    BoundaryClearance
      (Translated.translatedCoordinate
        (crossingParameter level position)) (Centered.connectorFixedBox 1) := by
  cases level with
  | upper =>
    exact ExplicitLegendreSegment.aboveClearance _ (by cases position <;> decide)
  | lower =>
    exact ExplicitLegendreSegment.belowClearance _ (by cases position <;> decide)

/-- The fixed zero factor has clearance on the broad moving-root box. -/
@[expose] def zeroOnMovingBoxClearance (level : Level) :
    BoundaryClearance (Translated.translatedCoordinate 0)
      (crossingMovingBox level) := by
  cases level with
  | upper => exact ExplicitLegendreSegment.belowClearance 0 (by decide)
  | lower => exact ExplicitLegendreSegment.aboveClearance 0 (by decide)

/-- The fixed one factor has clearance on the broad moving-root box. -/
@[expose] def oneOnMovingBoxClearance (level : Level) :
    BoundaryClearance (Translated.translatedCoordinate 1)
      (crossingMovingBox level) := by
  cases level with
  | upper => exact ExplicitLegendreSegment.belowClearance 1 (by decide)
  | lower => exact ExplicitLegendreSegment.aboveClearance 1 (by decide)

/-- The three-factor Legendre polynomial has clearance on the fixed zero-root box. -/
@[expose] def crossingZeroFactorsClearance (level : Level) (position : Position) :
    BoundaryClearance (Legendre.Polynomial.factorsAt (crossingParameter level position))
      (Centered.connectorFixedBox 0) :=
  Legendre.Polynomial.Clearance.factorsClearance (Clearance.Box.Boundary.Translated.centeredSquareSixteenthClearance 0)
    (movingOnZeroBoxClearance level position)
    (ExplicitLegendreSegment.rightClearance 1
      Connectors.zeroFixed_before_oneRoot)

/-- The three-factor Legendre polynomial has clearance on the broad moving-root box. -/
@[expose] def crossingMovingFactorsClearance (level : Level) (position : Position) :
    BoundaryClearance (Legendre.Polynomial.factorsAt (crossingParameter level position))
      (crossingMovingBox level) :=
  Legendre.Polynomial.Clearance.factorsClearance (zeroOnMovingBoxClearance level)
    (crossingMovingCenteredClearance level position)
    (oneOnMovingBoxClearance level)

/-- The three-factor Legendre polynomial has clearance on the fixed one-root box. -/
@[expose] def crossingOneFactorsClearance (level : Level) (position : Position) :
    BoundaryClearance (Legendre.Polynomial.factorsAt (crossingParameter level position))
      (Centered.connectorFixedBox 1) :=
  Legendre.Polynomial.Clearance.factorsClearance
    (ExplicitLegendreSegment.leftClearance 0
    Connectors.zeroRoot_before_oneFixed)
    (movingOnOneBoxClearance level position) (Clearance.Box.Boundary.Translated.centeredSquareSixteenthClearance 1)

/-- The Legendre polynomial has quadrupled winding four around the fixed zero-root box. -/
theorem crossingZeroWinding (level : Level) (position : Position) :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial (crossingParameter level position))
      (Centered.connectorFixedBox 0) = 4 := by
  rw [Legendre.Polynomial.polynomial_eq_factorsAt]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.connectorFixedBox_proper 0)
    (Clearance.Box.Boundary.Translated.centeredSquareSixteenthClearance 0) (movingOnZeroBoxClearance level position)
    (ExplicitLegendreSegment.rightClearance 1
      Connectors.zeroFixed_before_oneRoot)
  have zero : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
      (Centered.connectorFixedBox 0) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate 0
      (Centered.connectorFixedBox_left 0) (Centered.connectorFixedBox_right 0)
      (Centered.connectorFixedBox_below 0) (Centered.connectorFixedBox_above 0)
  have moving : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        (crossingParameter level position)) (Centered.connectorFixedBox 0) = 0 := by
    cases level with
    | upper =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_above _
          (Centered.connectorFixedBox_proper 0)
          (movingOnZeroBoxClearance .upper position)
          (by cases position <;> decide)
    | lower =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_below _
          (Centered.connectorFixedBox_proper 0)
          (movingOnZeroBoxClearance .lower position)
          (by cases position <;> decide)
  have one : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
      (Centered.connectorFixedBox 0) = 0 :=
    Winding.Affine.HalfPlane.factor_winding_zero_of_right 1 (Centered.connectorFixedBox_proper 0)
      (ExplicitLegendreSegment.rightClearance 1
        Connectors.zeroFixed_before_oneRoot) Connectors.zeroFixed_before_oneRoot
  rw [zero, moving, one]
  ring1

/-- The Legendre polynomial has quadrupled winding four around the broad moving-root box. -/
theorem crossingMovingWinding (level : Level) (position : Position) :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial (crossingParameter level position))
      (crossingMovingBox level) = 4 := by
  rw [Legendre.Polynomial.polynomial_eq_factorsAt]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (crossingMovingBox_proper level)
    (zeroOnMovingBoxClearance level)
    (crossingMovingCenteredClearance level position)
    (oneOnMovingBoxClearance level)
  have zero : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
      (crossingMovingBox level) = 0 := by
    cases level with
    | upper =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_below 0
          (crossingMovingBox_proper .upper) (zeroOnMovingBoxClearance .upper)
          (by decide)
    | lower =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_above 0
          (crossingMovingBox_proper .lower) (zeroOnMovingBoxClearance .lower)
          (by decide)
  have moving : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        (crossingParameter level position)) (crossingMovingBox level) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate _
      (by cases level <;> cases position <;> decide)
      (by cases level <;> cases position <;> decide)
      (by cases level <;> cases position <;> decide)
      (by cases level <;> cases position <;> decide)
  have one : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
      (crossingMovingBox level) = 0 := by
    cases level with
    | upper =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_below 1
          (crossingMovingBox_proper .upper) (oneOnMovingBoxClearance .upper)
          (by decide)
    | lower =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_above 1
          (crossingMovingBox_proper .lower) (oneOnMovingBoxClearance .lower)
          (by decide)
  rw [zero, moving, one]
  ring1

/-- The Legendre polynomial has quadrupled winding four around the fixed one-root box. -/
theorem crossingOneWinding (level : Level) (position : Position) :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial (crossingParameter level position))
      (Centered.connectorFixedBox 1) = 4 := by
  rw [Legendre.Polynomial.polynomial_eq_factorsAt]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.connectorFixedBox_proper 1)
    (ExplicitLegendreSegment.leftClearance 0
      Connectors.zeroRoot_before_oneFixed)
    (movingOnOneBoxClearance level position) (Clearance.Box.Boundary.Translated.centeredSquareSixteenthClearance 1)
  have zero : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
      (Centered.connectorFixedBox 1) = 0 :=
    Winding.Affine.HalfPlane.factor_winding_zero_of_left 0 (Centered.connectorFixedBox_proper 1)
      (ExplicitLegendreSegment.leftClearance 0
        Connectors.zeroRoot_before_oneFixed) Connectors.zeroRoot_before_oneFixed
  have moving : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        (crossingParameter level position)) (Centered.connectorFixedBox 1) = 0 := by
    cases level with
    | upper =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_above _
          (Centered.connectorFixedBox_proper 1)
          (movingOnOneBoxClearance .upper position)
          (by cases position <;> decide)
    | lower =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_below _
          (Centered.connectorFixedBox_proper 1)
          (movingOnOneBoxClearance .lower position)
          (by cases position <;> decide)
  have one : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
      (Centered.connectorFixedBox 1) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate 1
      (Centered.connectorFixedBox_left 1) (Centered.connectorFixedBox_right 1)
      (Centered.connectorFixedBox_below 1) (Centered.connectorFixedBox_above 1)
  rw [zero, moving, one]
  ring1

/-- The original fixed-zero local owner for a crossing endpoint. -/
@[expose] def crossingZeroOwner (level : Level) (position : Position) :
    LocalOwner (Legendre.Paths.polynomial (crossingParameter level position)) :=
  UpperZero.ownerOf (Centered.connectorFixedBox 0)
    (Centered.connectorFixedBox_proper 0)
    (by
        rw [Legendre.Polynomial.polynomial_eq_factorsAt];
        exact crossingZeroFactorsClearance level position)
    (crossingZeroWinding level position)

/-- The broad moving-root local owner for a crossing endpoint. -/
@[expose] def crossingMovingOwner (level : Level) (position : Position) :
    LocalOwner (Legendre.Paths.polynomial (crossingParameter level position)) :=
  UpperZero.ownerOf (crossingMovingBox level) (crossingMovingBox_proper level)
    (by
        rw [Legendre.Polynomial.polynomial_eq_factorsAt];
        exact crossingMovingFactorsClearance level position)
    (crossingMovingWinding level position)

/-- The original fixed-one local owner for a crossing endpoint. -/
@[expose] def crossingOneOwner (level : Level) (position : Position) :
    LocalOwner (Legendre.Paths.polynomial (crossingParameter level position)) :=
  UpperZero.ownerOf (Centered.connectorFixedBox 1)
    (Centered.connectorFixedBox_proper 1)
    (by
        rw [Legendre.Polynomial.polynomial_eq_factorsAt];
        exact crossingOneFactorsClearance level position)
    (crossingOneWinding level position)

/-- The moving factor has clearance on its narrow sample box at a crossing endpoint. -/
@[expose] def sampleMovingCenteredClearance (level : Level) (position : Position) :
    BoundaryClearance
      (Translated.translatedCoordinate
        (crossingParameter level position))
      (Centered.sampleBox (crossingParameter level position)) :=
  ExplicitLegendreSegment.centeredClearance _
    (by cases level <;> cases position <;> decide)
    (by cases level <;> cases position <;> decide)
    (by cases level <;> cases position <;> decide)
    (by cases level <;> cases position <;> decide)

/-- The fixed zero factor has clearance on the narrow moving-root sample box. -/
@[expose] def zeroOnSampleMovingClearance (level : Level) (position : Position) :
    BoundaryClearance (Translated.translatedCoordinate 0)
      (Centered.sampleBox (crossingParameter level position)) := by
  cases level with
  | upper =>
    exact ExplicitLegendreSegment.belowClearance 0 (by cases position <;> decide)
  | lower =>
    exact ExplicitLegendreSegment.aboveClearance 0 (by cases position <;> decide)

/-- The fixed one factor has clearance on the narrow moving-root sample box. -/
@[expose] def oneOnSampleMovingClearance (level : Level) (position : Position) :
    BoundaryClearance (Translated.translatedCoordinate 1)
      (Centered.sampleBox (crossingParameter level position)) := by
  cases level with
  | upper =>
    exact ExplicitLegendreSegment.belowClearance 1 (by cases position <;> decide)
  | lower =>
    exact ExplicitLegendreSegment.aboveClearance 1 (by cases position <;> decide)

/-- The Legendre polynomial has quadrupled winding four on the narrow moving-root sample box. -/
theorem crossingSampleMovingWinding (level : Level) (position : Position) :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial (crossingParameter level position))
      (Centered.sampleBox (crossingParameter level position)) = 4 := by
  rw [Legendre.Polynomial.polynomial_eq_factorsAt]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.sampleBox_proper _)
    (zeroOnSampleMovingClearance level position)
    (sampleMovingCenteredClearance level position)
    (oneOnSampleMovingClearance level position)
  have zero : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
      (Centered.sampleBox (crossingParameter level position)) = 0 := by
    cases level with
    | upper =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_below 0 (Centered.sampleBox_proper _)
          (zeroOnSampleMovingClearance .upper position)
          (by cases position <;> decide)
    | lower =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_above 0 (Centered.sampleBox_proper _)
          (zeroOnSampleMovingClearance .lower position)
          (by cases position <;> decide)
  have moving : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        (crossingParameter level position))
      (Centered.sampleBox (crossingParameter level position)) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate _
      (by cases level <;> cases position <;> decide)
      (by cases level <;> cases position <;> decide)
      (by cases level <;> cases position <;> decide)
      (by cases level <;> cases position <;> decide)
  have one : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
      (Centered.sampleBox (crossingParameter level position)) = 0 := by
    cases level with
    | upper =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_below 1 (Centered.sampleBox_proper _)
          (oneOnSampleMovingClearance .upper position)
          (by cases position <;> decide)
    | lower =>
        exact Winding.Affine.HalfPlane.factor_winding_zero_of_above 1 (Centered.sampleBox_proper _)
          (oneOnSampleMovingClearance .lower position)
          (by cases position <;> decide)
  rw [zero, moving, one]
  ring1

/-- The narrow sample-box local owner of the moving crossing root. -/
@[expose] def crossingSampleMovingOwner (level : Level) (position : Position) :
    LocalOwner (Legendre.Paths.polynomial (crossingParameter level position)) :=
  UpperZero.ownerOf (Centered.sampleBox (crossingParameter level
    position)) (Centered.sampleBox_proper _)
    (by
      rw [Legendre.Polynomial.polynomial_eq_factorsAt]
      exact Legendre.Polynomial.Clearance.factorsClearance (zeroOnSampleMovingClearance level position)
        (sampleMovingCenteredClearance level position)
        (oneOnSampleMovingClearance level position))
    (crossingSampleMovingWinding level position)

/-- The three crossing owners with the narrow sample box for the moving root. -/
@[expose] def crossingSampleOwner (level : Level) (position : Position) :
    Fin 3 -> LocalOwner (Legendre.Paths.polynomial (crossingParameter level position)) :=
  Data.Fin.casesDependent (size := 2) (motive := fun _ => LocalOwner (Legendre.Paths.polynomial
    (crossingParameter level position))) (crossingZeroOwner level position) (fun following =>
    Data.Fin.casesDependent (size := 1) (motive := fun _ => LocalOwner (Legendre.Paths.polynomial
      (crossingParameter level position))) (crossingSampleMovingOwner level position) (fun last =>
      Data.Fin.casesDependent (size := 0) (motive := fun _ => LocalOwner (Legendre.Paths.polynomial
        (crossingParameter level position))) (crossingOneOwner level position)
        (fun impossible => False.elim (Nat.not_lt_zero impossible.val impossible.isLt)) last) following)

/-- The three crossing owners with the broad box for the moving root. -/
@[expose] def crossingOwner (level : Level) (position : Position) :
    Fin 3 -> LocalOwner (Legendre.Paths.polynomial (crossingParameter level position)) :=
  Data.Fin.casesDependent (size := 2) (motive := fun _ => LocalOwner (Legendre.Paths.polynomial
    (crossingParameter level position)))
    (crossingZeroOwner level position) (fun second =>
      Data.Fin.casesDependent (size := 1) (motive := fun _ => LocalOwner (Legendre.Paths.polynomial
        (crossingParameter level position)))
        (crossingMovingOwner level position) (fun third =>
          Data.Fin.casesDependent (size := 0) (motive := fun _ => LocalOwner
            (Legendre.Paths.polynomial (crossingParameter level position)))
            (crossingOneOwner level position)
            (fun impossible => False.elim (Nat.not_lt_zero impossible.val impossible.isLt)) third) second)
/-- Distinct crossing-owner labels retain separated boxes. -/
theorem crossingOwner_pairwise (level : Level) (position : Position) :
    forall left right : Fin 3, left ≠ right ->
      (crossingOwner level position left).box.Separated
        (crossingOwner level position right).box := by
  intro left right different
  rcases Cases.three left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases Cases.three right with rightZero | rightOne | rightTwo <;>
    subst right <;>
    first | exact (different rfl).elim |
      cases level <;> cases position <;> decide

/-- The pairwise separated family of the original three broad crossing owners. -/
@[expose] def crossingOwnerFamily (level : Level) (position : Position) :
    Owner.Family.Basic.OwnerFamily
      (Legendre.Paths.polynomial (crossingParameter level position)) 3 where
  owner := crossingOwner level position
  pairwiseSeparated := crossingOwner_pairwise level position

/-- The crossing chamber retaining its broad root owners and original squarefree isolation maximality. -/
@[expose] def crossingChamber (level : Level) (position : Position) :
    Progressive.Chamber.Frame.ChamberFrame where
  reference := Legendre.Coefficients.Exact.coefficientTable (crossingParameter level position)
  chamber :=
    { degreeAtLeastTwo := by
        change 2 <= 3
        decide
      squarefree := Connectors.connectorSquarefree (connectorSide position)
        (levelHeight level)
      owners := crossingOwnerFamily level position
      referenceSmall := Legendre.Coefficients.Exact.coefficientTable_allowances_lt _
        (Progressive.Chamber.Target.simpleRootChamberTarget_pos
          (Legendre.Coefficients.Exact.coefficientTable (crossingParameter level position))
          (Connectors.connectorSquarefree (connectorSide position) (levelHeight level))
          (crossingOwnerFamily level position))
      referenceMaximality :=
        (FTA.Squarefree.Build.Box.prove
          (Connectors.connectorIsolationInput (connectorSide position)
            (levelHeight level))).boxes.maximality }

/-- The crossing chamber retains the original parameterized Legendre polynomial. -/
@[simp] theorem crossingChamber_polynomial (level : Level)
    (position : Position) :
    (crossingChamber level position).polynomial =
      Legendre.Paths.polynomial (crossingParameter level position) := rfl

/-- The narrow crossing sample owner read through the connector's original projection permutation. -/
@[expose] def crossingProjectionOwner (level : Level) (position : Position)
    (order : Fin 3) :
    LocalOwner (Legendre.Paths.polynomial (crossingParameter level position)) :=
  crossingSampleOwner level position
    ((Connectors.connectorProjectionOrder (connectorSide position)).forward order)

/-- The crossing frame combining broad chamber owners and narrow ordered projection owners. -/
@[expose] def crossingFrame (level : Level) (position : Position) :
    Legendre.Paths.Frame (crossingParameter level position) where
  chamber := crossingChamber level position
  polynomial_eq := rfl
  labels := Data.Fin.Bijection.identity 3
  owner_contains := by
    intro label
    rcases Cases.three label with labelZero | labelOne | labelTwo <;>
      subst label
    · exact Centered.connectorFixedBox_contains 0
    · exact crossingMovingBox_contains level position
    · exact Centered.connectorFixedBox_contains 1
  projectionOrder := Connectors.connectorProjectionOrder (connectorSide position)
  projectionOwner := fun order =>
    Owner.Local.Transport.castOwner
      (crossingChamber_polynomial level position).symm
      (crossingProjectionOwner level position order)
  projection_refines := by
    intro order
    rcases Cases.three order with orderZero | orderOne | orderTwo <;>
      subst order <;> cases level <;> cases position <;>
      exact ⟨by decide, by decide, by decide, by decide⟩
  projection_xOrdered := by
    intro left right ordered
    rcases Cases.three left with leftZero | leftOne | leftTwo
    · subst left
      rcases Cases.three right with rightZero | rightOne | rightTwo
      · subst right
        change (0 : Nat) < 0 at ordered
        exact False.elim ((by decide : ¬ (0 : Nat) < 0) ordered)
      · subst right
        change (0 : Nat) < 1 at ordered
        cases level <;> cases position <;> decide
      · subst right
        change (0 : Nat) < 2 at ordered
        cases level <;> cases position <;> decide
    · subst left
      rcases Cases.three right with rightZero | rightOne | rightTwo
      · subst right
        change (1 : Nat) < 0 at ordered
        exact False.elim ((by decide : ¬ (1 : Nat) < 0) ordered)
      · subst right
        change (1 : Nat) < 1 at ordered
        exact False.elim ((by decide : ¬ (1 : Nat) < 1) ordered)
      · subst right
        change (1 : Nat) < 2 at ordered
        cases level <;> cases position <;> decide
    · subst left
      rcases Cases.three right with rightZero | rightOne | rightTwo
      · subst right
        change (2 : Nat) < 0 at ordered
        exact False.elim ((by decide : ¬ (2 : Nat) < 0) ordered)
      · subst right
        change (2 : Nat) < 1 at ordered
        exact False.elim ((by decide : ¬ (2 : Nat) < 1) ordered)
      · subst right
        change (2 : Nat) < 2 at ordered
        exact False.elim ((by decide : ¬ (2 : Nat) < 2) ordered)

/-! ## The two positive upper half-twists -/

/-- The crossing frame retains the connector's exact projection permutation.

The law projects the generic frame before specializing its endpoint geometry.
-/
private theorem crossingFrame_projection_order (level : Level) (position : Position) (order : Fin 3) :
    (crossingFrame level position).projected.ownerIndex order =
      (Connectors.connectorProjectionOrder (connectorSide position)).forward order := rfl

/-- The crossing starts on the right at the upper level and on the left at the lower level. -/
@[expose] def crossingSourcePosition : Level -> Position
  | .upper => .right
  | .lower => .left

/-- The crossing ends on the left at the upper level and on the right at the lower level. -/
@[expose] def crossingTargetPosition : Level -> Position
  | .upper => .left
  | .lower => .right

/-- The original parameter at the start of the directed crossing. -/
@[expose] def crossingSourceParameter (level : Level) : Gaussian.Basic.Canonical :=
  crossingParameter level (crossingSourcePosition level)

/-- The original parameter at the end of the directed crossing. -/
@[expose] def crossingTargetParameter (level : Level) : Gaussian.Basic.Canonical :=
  crossingParameter level (crossingTargetPosition level)

/-- The retained broad frame at the start of the directed crossing. -/
@[expose] def oneCrossingSourceFrame (level : Level) :
    Legendre.Paths.Frame (crossingSourceParameter level) :=
  crossingFrame level (crossingSourcePosition level)

/-- The retained broad frame at the end of the directed crossing. -/
@[expose] def oneCrossingTargetFrame (level : Level) :
    Legendre.Paths.Frame (crossingTargetParameter level) :=
  crossingFrame level (crossingTargetPosition level)

/-- The exact polynomial perturbation between the directed crossing endpoints. -/
@[expose] def crossingPerturbation (level : Level) :
  CoefficientPolynomial :=
  Legendre.Polynomial.perturbationAt (crossingSourceParameter level)
    (crossingTargetParameter level)

/-- The target crossing polynomial equals the source polynomial plus its retained perturbation. -/
theorem crossingTarget_eq_add (level : Level) :
    Legendre.Paths.polynomial (crossingTargetParameter level) =
      Legendre.Paths.polynomial (crossingSourceParameter level) +
        crossingPerturbation level :=
  Legendre.Polynomial.target_eq_source_add_perturbationAt _ _

/-- The oriented Rouché certificate determined by the crossing perturbation and a supplied owner dominance witness. -/
@[expose] def crossingOrientedRouche (level : Level)
    (owner : LocalOwner (Legendre.Paths.polynomial (crossingSourceParameter level)))
    (dominance : BoundaryNormDominance
      (Legendre.Paths.polynomial (crossingSourceParameter level))
      (crossingPerturbation level) owner.box) :
    Box.Rouche.Connection.OrientedRouche
      (Legendre.Paths.polynomial (crossingSourceParameter level))
      (Legendre.Paths.polynomial (crossingTargetParameter level)) owner.box where
  perturbation := crossingPerturbation level
  target_eq_add := crossingTarget_eq_add level
  dominance := dominance

/-- The squared crossing displacement is smaller than the moving-factor clearance on the zero-root box. -/
theorem crossingZeroDisplacementSmall (level : Level) :
    Norm.Basic.normSq
        (crossingSourceParameter level - crossingTargetParameter level) <
      (movingOnZeroBoxClearance level
        (crossingSourcePosition level)).bound := by
  cases level <;> decide

/-- The squared crossing displacement is smaller than the moving-factor clearance on the broad moving-root box. -/
theorem crossingMovingDisplacementSmall (level : Level) :
    Norm.Basic.normSq
        (crossingSourceParameter level - crossingTargetParameter level) <
      (crossingMovingCenteredClearance level
        (crossingSourcePosition level)).bound := by
  cases level <;> decide

/-- The squared crossing displacement is smaller than the moving-factor clearance on the one-root box. -/
theorem crossingOneDisplacementSmall (level : Level) :
    Norm.Basic.normSq
        (crossingSourceParameter level - crossingTargetParameter level) <
      (movingOnOneBoxClearance level
        (crossingSourcePosition level)).bound := by
  cases level <;> decide

/-- The crossing perturbation is dominated on the fixed zero-root boundary. -/
@[expose] def crossingZeroDominance (level : Level) :
    BoundaryNormDominance
      (Legendre.Paths.polynomial (crossingSourceParameter level))
      (crossingPerturbation level)
      (crossingZeroOwner level (crossingSourcePosition level)).box :=
  Legendre.Rouche.factorMoveDominanceAt _ _ (Clearance.Box.Boundary.Translated.centeredSquareSixteenthClearance 0)
    (movingOnZeroBoxClearance level (crossingSourcePosition level))
    (ExplicitLegendreSegment.rightClearance 1
      Connectors.zeroFixed_before_oneRoot)
    (crossingZeroDisplacementSmall level)

/-- The crossing perturbation is dominated on the broad moving-root boundary. -/
@[expose] def crossingMovingDominance (level : Level) :
    BoundaryNormDominance
      (Legendre.Paths.polynomial (crossingSourceParameter level))
      (crossingPerturbation level)
      (crossingMovingOwner level (crossingSourcePosition level)).box :=
  Legendre.Rouche.factorMoveDominanceAt _ _ (zeroOnMovingBoxClearance level)
    (crossingMovingCenteredClearance level (crossingSourcePosition level))
    (oneOnMovingBoxClearance level)
    (crossingMovingDisplacementSmall level)

/-- The crossing perturbation is dominated on the fixed one-root boundary. -/
@[expose] def crossingOneDominance (level : Level) :
    BoundaryNormDominance
      (Legendre.Paths.polynomial (crossingSourceParameter level))
      (crossingPerturbation level)
      (crossingOneOwner level (crossingSourcePosition level)).box :=
  Legendre.Rouche.factorMoveDominanceAt _ _ (ExplicitLegendreSegment.leftClearance 0
    Connectors.zeroRoot_before_oneFixed)
    (movingOnOneBoxClearance level (crossingSourcePosition level))
    (Clearance.Box.Boundary.Translated.centeredSquareSixteenthClearance 1) (crossingOneDisplacementSmall level)

/-- The forward Rouché bridge retaining the zero-root owner across the crossing. -/
@[expose] def crossingZeroBridge (level : Level) : OwnerBridge
    (Legendre.Paths.polynomial (crossingSourceParameter level))
    (Legendre.Paths.polynomial (crossingTargetParameter level)) :=
  OwnerBridge.ofForward
    (crossingZeroOwner level (crossingSourcePosition level))
    (crossingOrientedRouche level _ (crossingZeroDominance level))

/-- The forward Rouché bridge retaining the broad moving-root owner across the crossing. -/
@[expose] def crossingMovingBridge (level : Level) : OwnerBridge
    (Legendre.Paths.polynomial (crossingSourceParameter level))
    (Legendre.Paths.polynomial (crossingTargetParameter level)) :=
  OwnerBridge.ofForward
    (crossingMovingOwner level (crossingSourcePosition level))
    (crossingOrientedRouche level _ (crossingMovingDominance level))

/-- The forward Rouché bridge retaining the one-root owner across the crossing. -/
@[expose] def crossingOneBridge (level : Level) : OwnerBridge
    (Legendre.Paths.polynomial (crossingSourceParameter level))
    (Legendre.Paths.polynomial (crossingTargetParameter level)) :=
  OwnerBridge.ofForward
    (crossingOneOwner level (crossingSourcePosition level))
    (crossingOrientedRouche level _ (crossingOneDominance level))

/-- The three crossing bridges in the original root-label order. -/
@[expose] def crossingBridgeAt (level : Level) :
    Fin 3 -> OwnerBridge
      (Legendre.Paths.polynomial (crossingSourceParameter level))
      (Legendre.Paths.polynomial (crossingTargetParameter level)) :=
  Data.Fin.casesDependent (size := 2) (motive := fun _ => OwnerBridge (Legendre.Paths.polynomial
    (crossingSourceParameter level)) (Legendre.Paths.polynomial (crossingTargetParameter level)))
    (crossingZeroBridge level) (fun second =>
      Data.Fin.casesDependent (size := 1) (motive := fun _ => OwnerBridge (Legendre.Paths.polynomial
        (crossingSourceParameter level)) (Legendre.Paths.polynomial (crossingTargetParameter level)))
        (crossingMovingBridge level) (fun third =>
          Data.Fin.casesDependent (size := 0) (motive := fun _ => OwnerBridge
            (Legendre.Paths.polynomial (crossingSourceParameter level)) (Legendre.Paths.polynomial
            (crossingTargetParameter level)))
            (crossingOneBridge level)
            (fun impossible => False.elim (Nat.not_lt_zero impossible.val impossible.isLt)) third) second)
/-- The identity-matched crossing chamber overlap retaining the original three owner boxes. -/
@[expose] def crossingChamberOverlap (level : Level) :
    Progressive.Chamber.Overlap.ChamberOverlap
      (oneCrossingSourceFrame level).chamber
      (oneCrossingTargetFrame level).chamber where
  matching := Data.Fin.Bijection.identity 3
  bridge := crossingBridgeAt level
  bridge_refines_left := by
    intro index
    rcases Cases.three index with indexZero | indexOne | indexTwo <;>
      subst index <;> exact Rational.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rcases Cases.three index with indexZero | indexOne | indexTwo <;>
      subst index <;> exact Rational.Box.refines_refl _

/-- The height-separated crossing geometry realizes the positive upper braid generator. -/
theorem crossingGeometry (level : Level) :
    Progressive.Braid.Projected.Overlap.CrossingGeometry
      (oneCrossingSourceFrame level).projected
      (oneCrossingTargetFrame level).projected
      (crossingChamberOverlap level)
      Legendre.Conventions.upperPositive where
  heightSeparated := by
    cases level
    · change (1 / 16 : Fraction.Rational) < 1
      decide
    · change (-1 : Fraction.Rational) < -(1 / 16)
      decide

/-- The projected crossing overlap with its original chamber bridges and positive upper generator. -/
@[expose] def crossingProjectedOverlap (level : Level) :
    ProjectedOverlap
      (oneCrossingSourceFrame level).projected
      (oneCrossingTargetFrame level).projected :=
  .crossing (crossingChamberOverlap level)
    Legendre.Conventions.upperPositive (crossingGeometry level) (by
      intro order
      rcases Cases.three order with orderZero | orderOne | orderTwo <;>
        subst order <;> cases level <;> rfl)

/-- The projected crossing contributes exactly one positive upper generator. -/
@[simp] theorem crossingProjectedOverlap_word (level : Level) :
    (crossingProjectedOverlap level).word =
      [Legendre.Conventions.upperPositive] := rfl

/-- The minimum of the six left and right owner-bridge clearance bounds across the crossing. -/
@[expose] def crossingSheetBound (level : Level) : Fraction.Rational :=
  min (crossingZeroBridge level).leftClearance.bound
    (min (crossingZeroBridge level).rightClearance.bound
      (min (crossingMovingBridge level).leftClearance.bound
        (min (crossingMovingBridge level).rightClearance.bound
          (min (crossingOneBridge level).leftClearance.bound
            (crossingOneBridge level).rightClearance.bound))))

/-- The common crossing sheet bound is positive. -/
theorem crossingSheetBound_positive (level : Level) :
    0 < crossingSheetBound level := by
  unfold crossingSheetBound
  exact Fraction.Order.Basic.lt_min (crossingZeroBridge level).leftClearance.positive
    (Fraction.Order.Basic.lt_min (crossingZeroBridge level).rightClearance.positive
      (Fraction.Order.Basic.lt_min (crossingMovingBridge level).leftClearance.positive
        (Fraction.Order.Basic.lt_min (crossingMovingBridge level).rightClearance.positive
          (Fraction.Order.Basic.lt_min (crossingOneBridge level).leftClearance.positive
            (crossingOneBridge level).rightClearance.positive))))

/-- The positive common bound below every original bridge clearance at both crossing endpoints. -/
@[expose] def crossingSheetClearance (level : Level) :
    Legendre.Paths.BridgeClearance (oneCrossingSourceFrame level)
      (oneCrossingTargetFrame level) (crossingChamberOverlap level) where
  bound := crossingSheetBound level
  positive := crossingSheetBound_positive level
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

/-- The directed horizontal crossing segment at height two or minus two. -/
@[expose] def crossingAxis : (level : Level) ->
    Legendre.Paths.AxisSegment (crossingSourceParameter level)
      (crossingTargetParameter level)
  | .upper => .horizontal (5 / 4) (3 / 4) 2
  | .lower => .horizontal (3 / 4) (5 / 4) (-2)

/-- The horizontal crossing segment avoids zero and one with squared-distance lower bound one. -/
@[expose] def crossingAxisSafe (level : Level) : Legendre.Paths.AxisSegment.Safe (crossingAxis level) := by
  cases level
  · exact
      { avoidsZero := { bound := 1, positive := by decide, lower := by decide }
        avoidsOne := { bound := 1, positive := by decide, lower := by decide } }
  · exact
      { avoidsZero := { bound := 1, positive := by decide, lower := by decide }
        avoidsOne := { bound := 1, positive := by decide, lower := by decide } }

/-- The certified crossing segment retaining its original geometry, projected overlap and sheet bound. -/
@[expose] def crossingSegment (level : Level) :
    Legendre.Paths.Segment (oneCrossingSourceFrame level) (oneCrossingTargetFrame level) :=
  Legendre.Paths.Segment.ofProjectedOverlap (crossingAxis level) (crossingAxisSafe level)
    (crossingProjectedOverlap level) (crossingSheetClearance level)

/-- The certified crossing segment contributes exactly one positive upper generator. -/
@[simp] theorem crossingSegment_crossings (level : Level) :
    (crossingSegment level).crossings =
      [Legendre.Conventions.upperPositive] := rfl

/-- The one-segment path for the directed horizontal crossing. -/
@[expose] def crossingPath (level : Level) :
    Legendre.Paths.Path (oneCrossingSourceFrame level) (oneCrossingTargetFrame level) :=
  .cons (crossingSegment level) (.nil _)

/-- The directed crossing path has the singleton positive upper braid word. -/
@[simp] theorem crossingPath_word (level : Level) :
    (crossingPath level).word =
      [Legendre.Conventions.upperPositive] := rfl

/-! ## Stationary transitions to the uniform connector frames -/

/-- The narrow connector and broad crossing chambers retain the same polynomial. -/
theorem narrowBroadPolynomial_eq (level : Level) (position : Position) :
    (Connectors.connectorChamber (connectorSide position)
      (levelHeight level)).polynomial =
      (crossingChamber level position).polynomial := by
  rw [Connectors.connectorChamber_polynomial, crossingChamber_polynomial]
  rfl

/-- The reflexive bridge from a narrow connector owner to the corresponding broad crossing owner. -/
@[expose] def narrowBroadBridge (level : Level) (position : Position)
    (index : Fin 3) : OwnerBridge
      (Connectors.connectorChamber (connectorSide position)
        (levelHeight level)).polynomial
      (crossingChamber level position).polynomial :=
  @OwnerBridge.cast
    (Connectors.connectorChamber (connectorSide position)
      (levelHeight level)).polynomial
    (Connectors.connectorChamber (connectorSide position)
      (levelHeight level)).polynomial
    (Connectors.connectorChamber (connectorSide position)
      (levelHeight level)).polynomial
    (crossingChamber level position).polynomial rfl
    (narrowBroadPolynomial_eq level position)
    (OwnerBridge.reflexive
      (Connectors.connectorOwner (connectorSide position) (levelHeight level) index))

/-- The narrow-to-broad bridge retains the original connector-owner box. -/
@[simp] theorem narrowBroadBridge_box (level : Level) (position : Position)
    (index : Fin 3) :
    (narrowBroadBridge level position index).box =
      (Connectors.connectorOwner (connectorSide position) (levelHeight level) index).box :=
  OwnerBridge.cast_box _ _ _

/-- The left bridge clearance equals the original narrow connector-owner clearance. -/
@[simp] theorem narrowBroadBridge_leftClearance_bound
    (level : Level) (position : Position) (index : Fin 3) :
    (narrowBroadBridge level position index).leftClearance.bound =
      (Connectors.connectorOwner (connectorSide position)
        (levelHeight level) index).clearance.bound := by
  unfold narrowBroadBridge
  rw [OwnerBridge.cast_leftClearance_bound]
  rfl

/-- The right bridge clearance equals the original narrow connector-owner clearance. -/
@[simp] theorem narrowBroadBridge_rightClearance_bound
    (level : Level) (position : Position) (index : Fin 3) :
    (narrowBroadBridge level position index).rightClearance.bound =
      (Connectors.connectorOwner (connectorSide position)
        (levelHeight level) index).clearance.bound := by
  unfold narrowBroadBridge
  rw [OwnerBridge.cast_rightClearance_bound]
  rfl

/-- The identity-matched overlap from the narrow connector chamber to the broad crossing chamber. -/
@[expose] def narrowBroadOverlap (level : Level) (position : Position) :
    Progressive.Chamber.Overlap.ChamberOverlap
      (Connectors.connectorChamber (connectorSide position) (levelHeight level))
      (crossingChamber level position) where
  matching := Data.Fin.Bijection.identity 3
  bridge := narrowBroadBridge level position
  bridge_refines_left := by
    intro index
    rw [narrowBroadBridge_box]
    exact Rational.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rw [narrowBroadBridge_box]
    rcases Cases.three index with indexZero | indexOne | indexTwo <;>
      subst index
    · exact Rational.Box.refines_refl _
    · cases level <;> cases position <;>
        exact ⟨by decide, by decide, by decide, by decide⟩
    · exact Rational.Box.refines_refl _

/-- The narrow-to-broad overlap retains its original owner bridge at every label. -/
@[simp] theorem narrowBroadOverlap_bridge (level : Level)
    (position : Position) (index : Fin 3) :
    (narrowBroadOverlap level position).bridge index =
      narrowBroadBridge level position index := rfl

/-- The overlap's left clearance equals the original narrow connector-owner clearance. -/
@[simp] theorem narrowBroadOverlap_leftClearance_bound
    (level : Level) (position : Position) (index : Fin 3) :
    ((narrowBroadOverlap level position).bridge index).leftClearance.bound =
      (Connectors.connectorOwner (connectorSide position)
        (levelHeight level) index).clearance.bound := by
  rw [narrowBroadOverlap_bridge, narrowBroadBridge_leftClearance_bound]

/-- The overlap's right clearance equals the original narrow connector-owner clearance. -/
@[simp] theorem narrowBroadOverlap_rightClearance_bound
    (level : Level) (position : Position) (index : Fin 3) :
    ((narrowBroadOverlap level position).bridge index).rightClearance.bound =
      (Connectors.connectorOwner (connectorSide position)
        (levelHeight level) index).clearance.bound := by
  rw [narrowBroadOverlap_bridge, narrowBroadBridge_rightClearance_bound]

/-- The stationary projected overlap from the narrow connector frame to the broad crossing frame. -/
@[expose] def narrowBroadProjectedOverlap (level : Level) (position : Position) :
    ProjectedOverlap
      (Connectors.connectorFrame (connectorSide position) (levelHeight level)).projected
      (crossingFrame level position).projected :=
  .stationary (narrowBroadOverlap level position) (by
    intro order
    rcases Cases.three order with orderZero | orderOne | orderTwo <;>
      subst order <;> cases position <;> rfl)

/-- The narrow-to-broad projected overlap has the empty braid word. -/
@[simp] theorem narrowBroadProjectedOverlap_word
    (level : Level) (position : Position) :
    (narrowBroadProjectedOverlap level position).word = [] := rfl

/-- The common sheet bound retained from the original connector owners for each narrow-to-broad transition. -/
@[expose] def narrowBroadSheetClearance : (level : Level) -> (position : Position) ->
    Legendre.Paths.BridgeClearance
      (Connectors.connectorFrame (connectorSide position) (levelHeight level))
      (crossingFrame level position) (narrowBroadOverlap level position)
  | .upper, .left =>
      { bound := Connectors.transitionSheetBound .oneLeft 2
        positive := Connectors.transitionSheetBound_positive .oneLeft 2
        leftLower := by
          intro index
          rw [narrowBroadOverlap_leftClearance_bound]
          exact Connectors.transitionSheetBound_le .oneLeft 2 index
        rightLower := by
          intro index
          rw [narrowBroadOverlap_rightClearance_bound]
          exact Connectors.transitionSheetBound_le .oneLeft 2 index }
  | .upper, .right =>
      { bound := Connectors.transitionSheetBound .oneRight 2
        positive := Connectors.transitionSheetBound_positive .oneRight 2
        leftLower := by
          intro index
          rw [narrowBroadOverlap_leftClearance_bound]
          exact Connectors.transitionSheetBound_le .oneRight 2 index
        rightLower := by
          intro index
          rw [narrowBroadOverlap_rightClearance_bound]
          exact Connectors.transitionSheetBound_le .oneRight 2 index }
  | .lower, .left =>
      { bound := Connectors.transitionSheetBound .oneLeft (-2)
        positive := Connectors.transitionSheetBound_positive .oneLeft (-2)
        leftLower := by
          intro index
          rw [narrowBroadOverlap_leftClearance_bound]
          exact Connectors.transitionSheetBound_le .oneLeft (-2) index
        rightLower := by
          intro index
          rw [narrowBroadOverlap_rightClearance_bound]
          exact Connectors.transitionSheetBound_le .oneLeft (-2) index }
  | .lower, .right =>
      { bound := Connectors.transitionSheetBound .oneRight (-2)
        positive := Connectors.transitionSheetBound_positive .oneRight (-2)
        leftLower := by
          intro index
          rw [narrowBroadOverlap_leftClearance_bound]
          exact Connectors.transitionSheetBound_le .oneRight (-2) index
        rightLower := by
          intro index
          rw [narrowBroadOverlap_rightClearance_bound]
          exact Connectors.transitionSheetBound_le .oneRight (-2) index }

/-- The constant-parameter transition from the narrow connector frame to the broad crossing frame. -/
@[expose] def narrowToBroadTransition (level : Level) (position : Position) :
    Legendre.Paths.Segment
      (Connectors.connectorFrame (connectorSide position) (levelHeight level))
      (crossingFrame level position) :=
  Legendre.Paths.Segment.ofProjectedOverlap
    (Connectors.stationaryGeometry (connectorSide position) (levelHeight level))
    (Connectors.stationaryGeometrySafe (connectorSide position) (levelHeight level))
    (narrowBroadProjectedOverlap level position)
    (narrowBroadSheetClearance level position)

/-- The narrow-to-broad frame transition has no crossings. -/
@[simp] theorem narrowToBroadTransition_crossings
    (level : Level) (position : Position) :
    (narrowToBroadTransition level position).crossings = [] := rfl

/-- The broad-to-narrow frame transition obtained by reversing the retained narrow-to-broad transition. -/
@[expose] def broadToNarrowTransition (level : Level) (position : Position) :
    Legendre.Paths.Segment (crossingFrame level position)
      (Connectors.connectorFrame (connectorSide position) (levelHeight level)) :=
  (narrowToBroadTransition level position).reverse

/-- The broad-to-narrow frame transition has no crossings. -/
@[simp] theorem broadToNarrowTransition_crossings
    (level : Level) (position : Position) :
    (broadToNarrowTransition level position).crossings = [] := by
  rw [broadToNarrowTransition, Legendre.Paths.Segment.reverse_crossings,
    narrowToBroadTransition_crossings]
  rfl

/-- The one-segment path from the narrow connector frame to the broad crossing frame. -/
@[expose] def narrowToBroadPath (level : Level) (position : Position) :
    Legendre.Paths.Path (Connectors.connectorFrame (connectorSide position) (levelHeight level))
      (crossingFrame level position) :=
  .cons (narrowToBroadTransition level position) (.nil _)

/-- The narrow-to-broad path has the empty braid word. -/
@[simp] theorem narrowToBroadPath_word (level : Level) (position : Position) :
    (narrowToBroadPath level position).word = [] := rfl

/-- The one-segment path from the broad crossing frame to the narrow connector frame. -/
@[expose] def broadToNarrowPath (level : Level) (position : Position) :
    Legendre.Paths.Path (crossingFrame level position)
      (Connectors.connectorFrame (connectorSide position) (levelHeight level)) :=
  .cons (broadToNarrowTransition level position) (.nil _)

/-- The broad-to-narrow path has the empty braid word. -/
@[simp] theorem broadToNarrowPath_word (level : Level) (position : Position) :
    (broadToNarrowPath level position).word = [] := by
  rw [broadToNarrowPath]
  simp only [Legendre.Paths.Path.word, broadToNarrowTransition_crossings, Data.List.Append.append_nil, -eq_self,
    -iff_self]
  rfl

/-! ## The closed local rectangle around one -/

/-- The upper-left path from the broad crossing frame to the narrow connector frame. -/
@[expose] def topLeftBroadToNarrowPath :
    Legendre.Paths.Path (crossingFrame .upper .left) (Connectors.connectorFrame .oneLeft 2) := by
  exact broadToNarrowPath .upper .left

/-- The upper-left frame-change path has the empty braid word. -/
@[simp] theorem topLeftBroadToNarrowPath_word :
    topLeftBroadToNarrowPath.word = [] := by
  exact broadToNarrowPath_word .upper .left

/-- The lower-left path from the narrow connector frame to the broad crossing frame. -/
@[expose] def bottomLeftNarrowToBroadPath :
    Legendre.Paths.Path (Connectors.connectorFrame .oneLeft (-2)) (crossingFrame .lower .left) := by
  exact narrowToBroadPath .lower .left

/-- The lower-left frame-change path has the empty braid word. -/
@[simp] theorem bottomLeftNarrowToBroadPath_word :
    bottomLeftNarrowToBroadPath.word = [] := by
  exact narrowToBroadPath_word .lower .left

/-- The lower-right path from the broad crossing frame to the narrow connector frame. -/
@[expose] def bottomRightBroadToNarrowPath :
    Legendre.Paths.Path (crossingFrame .lower .right) (Connectors.connectorFrame .oneRight (-2)) := by
  exact broadToNarrowPath .lower .right

/-- The lower-right frame-change path has the empty braid word. -/
@[simp] theorem bottomRightBroadToNarrowPath_word :
    bottomRightBroadToNarrowPath.word = [] := by
  exact broadToNarrowPath_word .lower .right

/-- The upper-right path from the narrow connector frame to the broad crossing frame. -/
@[expose] def topRightNarrowToBroadPath :
    Legendre.Paths.Path (Connectors.connectorFrame .oneRight 2) (crossingFrame .upper .right) := by
  exact narrowToBroadPath .upper .right

/-- The upper-right frame-change path has the empty braid word. -/
@[simp] theorem topRightNarrowToBroadPath_word :
    topRightNarrowToBroadPath.word = [] := by
  exact narrowToBroadPath_word .upper .right

/-- The lower horizontal crossing path from left to right around one. -/
@[expose] def lowerCrossingPath :
    Legendre.Paths.Path (crossingFrame .lower .left) (crossingFrame .lower .right) := by
  exact crossingPath .lower

/-- The lower crossing path contributes the positive upper braid generator. -/
@[simp] theorem lowerCrossingPath_word : lowerCrossingPath.word =
    [Legendre.Conventions.upperPositive] := by
  exact crossingPath_word .lower

/-- The upper horizontal crossing path from right to left around one. -/
@[expose] def upperCrossingPath :
    Legendre.Paths.Path (crossingFrame .upper .right) (crossingFrame .upper .left) := by
  exact crossingPath .upper

/-- The upper crossing path contributes the positive upper braid generator. -/
@[simp] theorem upperCrossingPath_word : upperCrossingPath.word =
    [Legendre.Conventions.upperPositive] := by
  exact crossingPath_word .upper

/-- The closed local rectangular path around one based at its upper-left broad frame.

It retains both original horizontal crossings, the uniform vertical connectors and all four stationary frame changes. -/
@[expose] def localOneLoop : Legendre.Paths.Path (crossingFrame .upper .left)
    (crossingFrame .upper .left) :=
  topLeftBroadToNarrowPath.append
    ((Connectors.sideDescent .oneLeft).append
      (bottomLeftNarrowToBroadPath.append
        (lowerCrossingPath.append
          (bottomRightBroadToNarrowPath.append
            ((Connectors.sideAscent .oneRight).append
              (topRightNarrowToBroadPath.append upperCrossingPath))))))

/-- The local rectangular loop has two consecutive positive upper braid generators. -/
@[simp] theorem localOneLoop_word : localOneLoop.word =
    [Legendre.Conventions.upperPositive,
      Legendre.Conventions.upperPositive] := by
  rw [localOneLoop, Legendre.Paths.Path.word_append, Legendre.Paths.Path.word_append, Legendre.Paths.Path.word_append,
    Legendre.Paths.Path.word_append, Legendre.Paths.Path.word_append, Legendre.Paths.Path.word_append,
      Legendre.Paths.Path.word_append,
    topLeftBroadToNarrowPath_word, Connectors.sideDescent_word,
    bottomLeftNarrowToBroadPath_word, lowerCrossingPath_word,
    bottomRightBroadToNarrowPath_word, Connectors.sideAscent_word,
    topRightNarrowToBroadPath_word, upperCrossingPath_word]
  rfl

/-! ## No-crossing approach from the common base -/

/-- The exact polynomial perturbation from the common base parameter to the upper-left one-loop endpoint. -/
@[expose] def approachPerturbation : CoefficientPolynomial :=
  Legendre.Polynomial.perturbationAt UpperZero.sourceParameter (crossingParameter .upper
    .left)

/-- The approach target polynomial equals the common-base polynomial plus the retained perturbation. -/
theorem approachTarget_eq_add :
    Legendre.Paths.polynomial (crossingParameter .upper .left) =
      Legendre.Paths.polynomial UpperZero.sourceParameter + approachPerturbation :=
  Legendre.Polynomial.target_eq_source_add_perturbationAt _ _

/-- The oriented Rouché certificate for approach from the common base, using a supplied retained owner and dominance
witness. -/
@[expose] def approachOrientedRouche
    (owner : LocalOwner (Legendre.Paths.polynomial
      UpperZero.sourceParameter))
    (dominance : BoundaryNormDominance
      (Legendre.Paths.polynomial UpperZero.sourceParameter) approachPerturbation owner.box) :
    Box.Rouche.Connection.OrientedRouche
      (Legendre.Paths.polynomial UpperZero.sourceParameter)
      (Legendre.Paths.polynomial (crossingParameter .upper .left)) owner.box where
  perturbation := approachPerturbation
  target_eq_add := approachTarget_eq_add
  dominance := dominance

/-- The approach perturbation is dominated on the original common-base zero-root box. -/
@[expose] def approachZeroDominance : BoundaryNormDominance
    (Legendre.Paths.polynomial UpperZero.sourceParameter) approachPerturbation
      UpperZero.sourceZeroOwner.box :=
  Legendre.Rouche.factorMoveDominanceAt UpperZero.sourceParameter (crossingParameter .upper
    .left)
    (ExplicitLegendreSegment.centeredClearance 0 (by decide) (by decide) (by decide)
      (by decide))
    (ExplicitLegendreSegment.aboveClearance
      UpperZero.sourceParameter UpperZero.source_above_fixedZero)
    (ExplicitLegendreSegment.rightClearance 1 (by decide)) (by decide)

/-- The approach perturbation is dominated on the original common-base moving-root box. -/
@[expose] def approachMovingDominance : BoundaryNormDominance
    (Legendre.Paths.polynomial UpperZero.sourceParameter) approachPerturbation
      UpperZero.sourceMovingOwner.box :=
  Legendre.Rouche.factorMoveDominanceAt UpperZero.sourceParameter (crossingParameter .upper
    .left)
    (ExplicitLegendreSegment.belowClearance 0 (by decide))
    (ExplicitLegendreSegment.centeredClearance
      UpperZero.sourceParameter UpperZero.source_in_movingBox.1
      UpperZero.source_in_movingBox.2.1
        UpperZero.source_in_movingBox.2.2.1
      UpperZero.source_in_movingBox.2.2.2)
    (ExplicitLegendreSegment.belowClearance 1 (by decide)) (by decide)

/-- The approach perturbation is dominated on the original common-base one-root box. -/
@[expose] def approachOneDominance : BoundaryNormDominance
    (Legendre.Paths.polynomial UpperZero.sourceParameter) approachPerturbation
      UpperZero.sourceOneOwner.box :=
  Legendre.Rouche.factorMoveDominanceAt UpperZero.sourceParameter (crossingParameter .upper
    .left)
    (ExplicitLegendreSegment.leftClearance 0 (by decide))
    (ExplicitLegendreSegment.aboveClearance
      UpperZero.sourceParameter UpperZero.source_above_fixedOne)
    (ExplicitLegendreSegment.centeredClearance 1 (by decide) (by decide) (by decide)
      (by decide))
    (by decide)

/-- The forward approach bridge retaining the common-base zero-root owner. -/
@[expose] def approachZeroBridge : OwnerBridge
    (Legendre.Paths.polynomial UpperZero.sourceParameter)
    (Legendre.Paths.polynomial (crossingParameter .upper .left)) :=
  OwnerBridge.ofForward UpperZero.sourceZeroOwner
    (approachOrientedRouche UpperZero.sourceZeroOwner approachZeroDominance)

/-- The forward approach bridge retaining the common-base moving-root owner. -/
@[expose] def approachMovingBridge : OwnerBridge
    (Legendre.Paths.polynomial UpperZero.sourceParameter)
    (Legendre.Paths.polynomial (crossingParameter .upper .left)) :=
  OwnerBridge.ofForward UpperZero.sourceMovingOwner
    (approachOrientedRouche UpperZero.sourceMovingOwner approachMovingDominance)

/-- The forward approach bridge retaining the common-base one-root owner. -/
@[expose] def approachOneBridge : OwnerBridge
    (Legendre.Paths.polynomial UpperZero.sourceParameter)
    (Legendre.Paths.polynomial (crossingParameter .upper .left)) :=
  OwnerBridge.ofForward UpperZero.sourceOneOwner
    (approachOrientedRouche UpperZero.sourceOneOwner approachOneDominance)

/-- The three approach bridges in the original root-label order. -/
@[expose] def approachBridgeAt : Fin 3 -> OwnerBridge
    (Legendre.Paths.polynomial UpperZero.sourceParameter)
    (Legendre.Paths.polynomial (crossingParameter .upper .left)) :=
  Data.Fin.casesDependent (size := 2) (motive := fun _ => OwnerBridge (Legendre.Paths.polynomial
    UpperZero.sourceParameter) (Legendre.Paths.polynomial (crossingParameter .upper .left)))
    (approachZeroBridge) (fun second =>
      Data.Fin.casesDependent (size := 1) (motive := fun _ => OwnerBridge (Legendre.Paths.polynomial
        UpperZero.sourceParameter) (Legendre.Paths.polynomial (crossingParameter .upper
        .left)))
        (approachMovingBridge) (fun third =>
          Data.Fin.casesDependent (size := 0) (motive := fun _ => OwnerBridge
            (Legendre.Paths.polynomial UpperZero.sourceParameter) (Legendre.Paths.polynomial
            (crossingParameter .upper .left)))
            (approachOneBridge)
            (fun impossible => False.elim (Nat.not_lt_zero impossible.val impossible.isLt)) third) second)
/-- The identity-matched chamber overlap from the common base to the upper-left one-loop chamber. -/
@[expose] def approachChamberOverlap : Progressive.Chamber.Overlap.ChamberOverlap
    UpperZero.sourceChamber (crossingChamber .upper .left) where
  matching := Data.Fin.Bijection.identity 3
  bridge := approachBridgeAt
  bridge_refines_left := by
    intro index
    rcases Cases.three index with indexZero | indexOne | indexTwo <;>
      subst index <;> exact Rational.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rcases Cases.three index with indexZero | indexOne | indexTwo <;>
      subst index <;>
      exact ⟨by decide, by decide, by decide, by decide⟩

/-- The stationary projected overlap from the common base to the one-loop endpoint. -/
@[expose] def approachProjectedOverlap : ProjectedOverlap
    UpperZero.sourceFrame.projected (crossingFrame .upper .left).projected :=
  .stationary approachChamberOverlap (by
    intro order
    rw [UpperZero.sourceFrame_projection_order, crossingFrame_projection_order]
    rfl)

/-- The projected approach overlap contributes no braid letters. -/
@[simp] theorem approachProjectedOverlap_word :
    approachProjectedOverlap.word = [] := rfl

/-- The minimum of the six original approach-bridge clearance bounds. -/
@[expose] def approachSheetBound : Fraction.Rational :=
  min approachZeroBridge.leftClearance.bound
    (min approachZeroBridge.rightClearance.bound
      (min approachMovingBridge.leftClearance.bound
        (min approachMovingBridge.rightClearance.bound
          (min approachOneBridge.leftClearance.bound
            approachOneBridge.rightClearance.bound))))

/-- The common approach sheet bound is positive. -/
theorem approachSheetBound_positive : 0 < approachSheetBound := by
  unfold approachSheetBound
  exact Fraction.Order.Basic.lt_min approachZeroBridge.leftClearance.positive
    (Fraction.Order.Basic.lt_min approachZeroBridge.rightClearance.positive
      (Fraction.Order.Basic.lt_min approachMovingBridge.leftClearance.positive
        (Fraction.Order.Basic.lt_min approachMovingBridge.rightClearance.positive
          (Fraction.Order.Basic.lt_min approachOneBridge.leftClearance.positive
            approachOneBridge.rightClearance.positive))))

/-- The retained positive common clearance bound for the approach bridges at both endpoints. -/
@[expose] def approachSheetClearance :
    Legendre.Paths.BridgeClearance UpperZero.sourceFrame (crossingFrame .upper .left)
      approachChamberOverlap where
  bound := approachSheetBound
  positive := approachSheetBound_positive
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

/-- The horizontal approach segment from 1/4 + 2i to 3/4 + 2i. -/
@[expose] def approachAxis : Legendre.Paths.AxisSegment UpperZero.sourceParameter
    (crossingParameter .upper .left) :=
  .horizontal (1 / 4) (3 / 4) 2

/-- The approach segment avoids both critical parameters with squared-distance lower bound one. -/
@[expose] def approachAxisSafe : Legendre.Paths.AxisSegment.Safe approachAxis where
  avoidsZero := { bound := 1, positive := by decide, lower := by decide }
  avoidsOne := { bound := 1, positive := by decide, lower := by decide }

/-- The certified approach segment retaining the original common-base bridges and clearances. -/
@[expose] def approachSegment : Legendre.Paths.Segment UpperZero.sourceFrame (crossingFrame
  .upper .left) :=
  Legendre.Paths.Segment.ofProjectedOverlap approachAxis approachAxisSafe
    approachProjectedOverlap approachSheetClearance

/-- The approach segment has no crossings. -/
@[simp] theorem approachSegment_crossings : approachSegment.crossings = [] :=
  rfl

/-- The one-segment approach path from the common base frame to the upper-left one-loop frame. -/
@[expose] def approachPath : Legendre.Paths.Path UpperZero.sourceFrame (crossingFrame .upper
  .left) :=
  .cons approachSegment (.nil _)

/-- The approach path has the empty braid word. -/
@[simp] theorem approachPath_word : approachPath.word = [] := rfl

/-! ## The common-base standard one loop -/

/-- The closed loop around one based at the same frame as the loop around zero.

It follows the approach, traverses the original local rectangle and reverses the same approach path. -/
@[expose] def oneLoopPath : Legendre.Paths.Path UpperZero.sourceFrame
  UpperZero.sourceFrame :=
  approachPath.append (localOneLoop.append approachPath.reverse)

/-- The common-base loop around one has two consecutive positive upper braid generators. -/
@[simp] theorem oneLoopPath_word : oneLoopPath.word =
    [Legendre.Conventions.upperPositive,
      Legendre.Conventions.upperPositive] := by
  rw [oneLoopPath, Legendre.Paths.Path.word_append, Legendre.Paths.Path.word_append, approachPath_word,
    localOneLoop_word, Legendre.Paths.Path.word_reverse, approachPath_word]
  rfl

/-- The common-base loop's braid word is equivalent to the displayed standard braid around one. -/
theorem oneLoopWord : Knot.Braid.Artin.Equivalent oneLoopPath.word
    Legendre.Monodromy.oneBraid := by
  rw [oneLoopPath_word]
  exact .refl _

/-- The retained pair of standard loops around zero and one at their common original base frame. -/
@[expose] def standardLoops : Legendre.Monodromy.StandardLoops UpperZero.sourceFrame where
  zeroPath := Connectors.zeroLoopPath
  onePath := oneLoopPath
  zeroWord := Connectors.zeroLoopWord
  oneWord := oneLoopWord

end Purelib.Examples.Curves.Legendre.Loops.One

end
