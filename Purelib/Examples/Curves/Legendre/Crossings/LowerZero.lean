module
import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Translated
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Fin.Cases
import Purelib.Data.Fin
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Progressive.Chamber.Target
import Purelib.Curves.Legendre.Coefficients.Exact
import Purelib.Curves.Legendre.Conventions
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Polynomial
import Purelib.Curves.Legendre.Polynomial.Clearance
import Purelib.Curves.Legendre.Polynomial.Winding
import Purelib.Curves.Legendre.Rouche
import Purelib.Curves.Legendre.Squarefree
import Purelib.Data.Fin.Bijection.Basic
public import Purelib.Examples.Curves.Legendre.Crossings.UpperZero
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Winding.Box.Affine
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Rouche.Connection
import Purelib.RootIsolation.FTA.Squarefree.Build
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Owner.Bridge.Rouche
import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.RootIsolation.Progressive.Braid.Projected.Overlap
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
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

section
public section

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

namespace Purelib.Examples.Curves.Legendre.Crossings.LowerZero

open Purelib.Polynomial.Winding
open Purelib.Data.Fin
open Purelib.Polynomial.Clearance.Box.Dominance.Basic (BoundaryNormDominance)

open Purelib.Curves
open Purelib
open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Geometry
open Purelib.Polynomial
open Purelib.RootIsolation

open Purelib.Examples.Curves.Legendre.Crossings

open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)
open Purelib.RootIsolation.Owner.Local.Basic (LocalOwner)
open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)
open Purelib.Polynomial.Dense.Gaussian.Linear
open Purelib.Geometry.Rational.Box.Square

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Legendre.Paths (GaussianPolynomial)
open Purelib.Polynomial.Clearance.Box.Boundary.Translated.ExplicitLegendreSegment (aboveClearance belowClearance
  centeredClearance leftClearance rightClearance)

/-- The left parameter `-1/4 - 2i` of the lower Legendre crossing. -/
@[expose] def lowerLeftParameter : Gaussian :=
  Legendre.Paths.gaussian (-(1 / 4)) (-2)
/-- The right parameter `1/4 - 2i` of the lower Legendre crossing. -/
@[expose] def lowerRightParameter : Gaussian :=
  Legendre.Paths.gaussian (1 / 4) (-2)

/-- The Legendre polynomial at the lower left parameter equals its three displayed linear factors. -/
theorem lowerLeft_polynomial_eq_factors :
    Legendre.Paths.polynomial lowerLeftParameter = Legendre.Polynomial.factorsAt
      lowerLeftParameter := by
  decide

/-- The Legendre polynomial at the lower right parameter equals its three displayed linear factors. -/
theorem lowerRight_polynomial_eq_factors :
    Legendre.Paths.polynomial lowerRightParameter = Legendre.Polynomial.factorsAt
      lowerRightParameter := by
  decide

/-- The moving-root box with horizontal bounds minus one and one and vertical bounds minus three and minus one. -/
@[expose] def lowerMovingBox : Rational.Box
  where
  xLower := -1
  xUpper := 1
  yLower := -3
  yUpper := -1
  x_valid := by decide
  y_valid := by decide

/-- The lower moving-root box has strictly ordered coordinate bounds. -/
theorem lowerMovingBox_proper :
  lowerMovingBox.Proper := by
  constructor <;> decide

/-! ## Six exact lower owners -/

/-- Boundary clearance for the fixed root zero at the lower left parameter.

The product certificate retains the three original linear-factor clearances on the selected owner box. -/
@[expose] def lowerLeftZeroClearance :
    BoundaryClearance (Legendre.Paths.polynomial
      lowerLeftParameter) (Centered.realAxisSquareSixteenth 0)
      := by
  rw [lowerLeft_polynomial_eq_factors]
  exact Legendre.Polynomial.Clearance.factorsClearance
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (belowClearance lowerLeftParameter (by decide))
    (rightClearance 1 (by decide))

/-- Boundary clearance for the moving root at the lower left parameter.

The product certificate retains the three original linear-factor clearances on the selected owner box. -/
@[expose] def lowerLeftMovingClearance :
    BoundaryClearance (Legendre.Paths.polynomial
      lowerLeftParameter) lowerMovingBox := by
  rw [lowerLeft_polynomial_eq_factors]
  exact Legendre.Polynomial.Clearance.factorsClearance
    (aboveClearance 0 (by decide))
    (centeredClearance lowerLeftParameter
      (by decide) (by decide) (by decide) (by decide))
    (aboveClearance 1 (by decide))

/-- Boundary clearance for the fixed root one at the lower left parameter.

The product certificate retains the three original linear-factor clearances on the selected owner box. -/
@[expose] def lowerLeftOneClearance :
    BoundaryClearance (Legendre.Paths.polynomial
      lowerLeftParameter) (Centered.realAxisSquareSixteenth 1)
      := by
  rw [lowerLeft_polynomial_eq_factors]
  exact Legendre.Polynomial.Clearance.factorsClearance
    (leftClearance 0 (by decide))
    (belowClearance lowerLeftParameter (by decide))
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))

/-- Boundary clearance for the fixed root zero at the lower right parameter.

The product certificate retains the three original linear-factor clearances on the selected owner box. -/
@[expose] def lowerRightZeroClearance :
    BoundaryClearance (Legendre.Paths.polynomial
      lowerRightParameter) (Centered.realAxisSquareSixteenth 0)
      := by
  rw [lowerRight_polynomial_eq_factors]
  exact Legendre.Polynomial.Clearance.factorsClearance
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (belowClearance lowerRightParameter (by decide))
    (rightClearance 1 (by decide))

/-- Boundary clearance for the moving root at the lower right parameter.

The product certificate retains the three original linear-factor clearances on the selected owner box. -/
@[expose] def lowerRightMovingClearance :
    BoundaryClearance (Legendre.Paths.polynomial
      lowerRightParameter) lowerMovingBox := by
  rw [lowerRight_polynomial_eq_factors]
  exact Legendre.Polynomial.Clearance.factorsClearance
    (aboveClearance 0 (by decide))
    (centeredClearance lowerRightParameter
      (by decide) (by decide) (by decide) (by decide))
    (aboveClearance 1 (by decide))

/-- Boundary clearance for the fixed root one at the lower right parameter.

The product certificate retains the three original linear-factor clearances on the selected owner box. -/
@[expose] def lowerRightOneClearance :
    BoundaryClearance (Legendre.Paths.polynomial
      lowerRightParameter) (Centered.realAxisSquareSixteenth 1)
      := by
  rw [lowerRight_polynomial_eq_factors]
  exact Legendre.Polynomial.Clearance.factorsClearance
    (leftClearance 0 (by decide))
    (belowClearance lowerRightParameter (by decide))
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))

/-- The quadrupled winding on the the fixed root zero owner box at the lower left parameter is four. -/
theorem lowerLeftZeroWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial lowerLeftParameter)
        (Centered.realAxisSquareSixteenth 0) = 4 := by
  rw [lowerLeft_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.realAxisSquareSixteenth_proper
    0)
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (belowClearance lowerLeftParameter (by decide))
    (rightClearance 1 (by decide))
  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
        (Centered.realAxisSquareSixteenth 0) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate 0
      (by decide) (by decide) (by decide) (by decide)
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        lowerLeftParameter)
        (Centered.realAxisSquareSixteenth 0) = 0 := by decide
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
        (Centered.realAxisSquareSixteenth 0) = 0 := by
    decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The quadrupled winding on the the moving root owner box at the lower left parameter is four. -/
theorem lowerLeftMovingWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial lowerLeftParameter)
        lowerMovingBox = 4 := by
  rw [lowerLeft_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum lowerMovingBox_proper
    (aboveClearance 0 (by decide))
    (centeredClearance lowerLeftParameter
      (by decide) (by decide) (by decide) (by decide))
    (aboveClearance 1 (by decide))
  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
        lowerMovingBox = 0 := by
    decide
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        lowerLeftParameter)
        lowerMovingBox = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate
      lowerLeftParameter (by decide) (by decide) (by decide) (by decide)
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
        lowerMovingBox = 0 := by
    decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The quadrupled winding on the the fixed root one owner box at the lower left parameter is four. -/
theorem lowerLeftOneWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial lowerLeftParameter)
        (Centered.realAxisSquareSixteenth 1) = 4 := by
  rw [lowerLeft_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.realAxisSquareSixteenth_proper
    1)
    (leftClearance 0 (by decide))
    (belowClearance lowerLeftParameter (by decide))
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))
  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
        (Centered.realAxisSquareSixteenth 1) = 0 := by
    decide
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        lowerLeftParameter)
        (Centered.realAxisSquareSixteenth 1) = 0 := by decide
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
        (Centered.realAxisSquareSixteenth 1) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate 1
      (by decide) (by decide) (by decide) (by decide)
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The quadrupled winding on the the fixed root zero owner box at the lower right parameter is four. -/
theorem lowerRightZeroWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial lowerRightParameter)
        (Centered.realAxisSquareSixteenth 0) = 4 := by
  rw [lowerRight_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.realAxisSquareSixteenth_proper
    0)
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (belowClearance lowerRightParameter (by decide))
    (rightClearance 1 (by decide))
  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
        (Centered.realAxisSquareSixteenth 0) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate 0
      (by decide) (by decide) (by decide) (by decide)
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        lowerRightParameter)
        (Centered.realAxisSquareSixteenth 0) = 0 := by decide
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
        (Centered.realAxisSquareSixteenth 0) = 0 := by
    decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The quadrupled winding on the the moving root owner box at the lower right parameter is four. -/
theorem lowerRightMovingWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial lowerRightParameter)
        lowerMovingBox = 4 := by
  rw [lowerRight_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum lowerMovingBox_proper
    (aboveClearance 0 (by decide))
    (centeredClearance lowerRightParameter
      (by decide) (by decide) (by decide) (by decide))
    (aboveClearance 1 (by decide))
  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
        lowerMovingBox = 0 := by
    decide
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        lowerRightParameter)
        lowerMovingBox = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate
      lowerRightParameter (by decide) (by decide) (by decide) (by decide)
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
        lowerMovingBox = 0 := by
    decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The quadrupled winding on the the fixed root one owner box at the lower right parameter is four. -/
theorem lowerRightOneWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial lowerRightParameter)
        (Centered.realAxisSquareSixteenth 1) = 4 := by
  rw [lowerRight_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.realAxisSquareSixteenth_proper
    1)
    (leftClearance 0 (by decide))
    (belowClearance lowerRightParameter (by decide))
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))
  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
        (Centered.realAxisSquareSixteenth 1) = 0 := by
    decide
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        lowerRightParameter)
        (Centered.realAxisSquareSixteenth 1) = 0 := by decide
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
        (Centered.realAxisSquareSixteenth 1) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate 1
      (by decide) (by decide) (by decide) (by decide)
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The quadrupled winding on the sample box around the fixed root zero at the lower left parameter is four. -/
theorem lowerLeftSampleZeroWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial lowerLeftParameter)
        (Centered.sampleBox 0) = 4 := by
  rw [lowerLeft_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.sampleBox_proper 0)
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (leftClearance lowerLeftParameter (by decide))
    (rightClearance 1 (by decide))

  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0) (Centered.sampleBox 0) = 4
        :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate 0
      (by decide) (by decide) (by decide) (by decide)
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        lowerLeftParameter)
        (Centered.sampleBox 0) = 0 := by decide
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1) (Centered.sampleBox 0) = 0
        := by
    decide

  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The quadrupled winding on the sample box around the moving root at the lower left parameter is four. -/
theorem lowerLeftSampleMovingWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial lowerLeftParameter)
        (Centered.sampleBox lowerLeftParameter) = 4 := by
  rw [lowerLeft_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.sampleBox_proper
    lowerLeftParameter)
    (rightClearance 0 (by decide))
    (centeredClearance lowerLeftParameter
      (by decide) (by decide) (by decide) (by decide))
    (rightClearance 1 (by decide))

  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
        (Centered.sampleBox lowerLeftParameter) = 0 := by decide
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        lowerLeftParameter)
        (Centered.sampleBox lowerLeftParameter) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate
      lowerLeftParameter (by decide) (by decide) (by decide) (by decide)
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
        (Centered.sampleBox lowerLeftParameter) = 0 := by decide

  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The quadrupled winding on the sample box around the fixed root one at the lower left parameter is four. -/
theorem lowerLeftSampleOneWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial lowerLeftParameter)
        (Centered.sampleBox 1) = 4 := by
  rw [lowerLeft_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.sampleBox_proper 1)
    (leftClearance 0 (by decide))
    (leftClearance lowerLeftParameter (by decide))
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))

  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0) (Centered.sampleBox 1) = 0
        := by
    decide
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        lowerLeftParameter)
        (Centered.sampleBox 1) = 0 := by decide
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1) (Centered.sampleBox 1) = 4
        :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate 1
      (by decide) (by decide) (by decide) (by decide)

  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The quadrupled winding on the sample box around the fixed root zero at the lower right parameter is four. -/
theorem lowerRightSampleZeroWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial lowerRightParameter)
        (Centered.sampleBox 0) = 4 := by
  rw [lowerRight_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.sampleBox_proper 0)
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (rightClearance lowerRightParameter (by decide))
    (rightClearance 1 (by decide))

  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0) (Centered.sampleBox 0) = 4
        :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate 0
      (by decide) (by decide) (by decide) (by decide)
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        lowerRightParameter)
        (Centered.sampleBox 0) = 0 := by decide
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1) (Centered.sampleBox 0) = 0
        := by
    decide

  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The quadrupled winding on the sample box around the moving root at the lower right parameter is four. -/
theorem lowerRightSampleMovingWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial lowerRightParameter)
        (Centered.sampleBox lowerRightParameter) = 4 := by
  rw [lowerRight_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.sampleBox_proper
    lowerRightParameter)
    (leftClearance 0 (by decide))
    (centeredClearance lowerRightParameter
      (by decide) (by decide) (by decide) (by decide))
    (rightClearance 1 (by decide))

  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
        (Centered.sampleBox lowerRightParameter) = 0 := by
          decide
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        lowerRightParameter)
        (Centered.sampleBox lowerRightParameter) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate
      lowerRightParameter (by decide) (by decide) (by decide) (by decide)
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
        (Centered.sampleBox lowerRightParameter) = 0 := by
          decide

  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The quadrupled winding on the sample box around the fixed root one at the lower right parameter is four. -/
theorem lowerRightSampleOneWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial lowerRightParameter)
        (Centered.sampleBox 1) = 4 := by
  rw [lowerRight_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.sampleBox_proper 1)
    (leftClearance 0 (by decide))
    (leftClearance lowerRightParameter (by decide))
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))

  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0) (Centered.sampleBox 1) = 0
        := by
    decide
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        lowerRightParameter)
        (Centered.sampleBox 1) = 0 := by decide
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1) (Centered.sampleBox 1) = 4
        :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate 1
      (by decide) (by decide) (by decide) (by decide)

  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The retained local owner of the fixed root zero at the lower left parameter.

Its original proper box, positive boundary clearance and winding-one witness specify the same isolated root. -/
@[expose] def lowerLeftZeroOwner :
  LocalOwner (Legendre.Paths.polynomial lowerLeftParameter) :=
  UpperZero.ownerOf (Centered.realAxisSquareSixteenth 0)
    (Centered.realAxisSquareSixteenth_proper 0)
    lowerLeftZeroClearance
    lowerLeftZeroWinding

/-- The retained local owner of the moving root at the lower left parameter.

Its original proper box, positive boundary clearance and winding-one witness specify the same isolated root. -/
@[expose] def lowerLeftMovingOwner :
  LocalOwner (Legendre.Paths.polynomial lowerLeftParameter) :=
  UpperZero.ownerOf lowerMovingBox
    lowerMovingBox_proper
    lowerLeftMovingClearance
    lowerLeftMovingWinding

/-- The retained local owner of the fixed root one at the lower left parameter.

Its original proper box, positive boundary clearance and winding-one witness specify the same isolated root. -/
@[expose] def lowerLeftOneOwner :
  LocalOwner (Legendre.Paths.polynomial lowerLeftParameter) :=
  UpperZero.ownerOf (Centered.realAxisSquareSixteenth 1)
    (Centered.realAxisSquareSixteenth_proper 1)
    lowerLeftOneClearance
    lowerLeftOneWinding

/-- The retained local owner of the fixed root zero at the lower right parameter.

Its original proper box, positive boundary clearance and winding-one witness specify the same isolated root. -/
@[expose] def lowerRightZeroOwner :
  LocalOwner (Legendre.Paths.polynomial lowerRightParameter) :=
  UpperZero.ownerOf (Centered.realAxisSquareSixteenth 0)
    (Centered.realAxisSquareSixteenth_proper 0)
    lowerRightZeroClearance
    lowerRightZeroWinding

/-- The retained local owner of the moving root at the lower right parameter.

Its original proper box, positive boundary clearance and winding-one witness specify the same isolated root. -/
@[expose] def lowerRightMovingOwner :
  LocalOwner (Legendre.Paths.polynomial lowerRightParameter) :=
  UpperZero.ownerOf lowerMovingBox
    lowerMovingBox_proper
    lowerRightMovingClearance
    lowerRightMovingWinding

/-- The retained local owner of the fixed root one at the lower right parameter.

Its original proper box, positive boundary clearance and winding-one witness specify the same isolated root. -/
@[expose] def lowerRightOneOwner :
  LocalOwner (Legendre.Paths.polynomial lowerRightParameter) :=
  UpperZero.ownerOf (Centered.realAxisSquareSixteenth 1)
    (Centered.realAxisSquareSixteenth_proper 1)
    lowerRightOneClearance
    lowerRightOneWinding

/-- The smaller sample-box owner of the fixed root zero at the lower left parameter. -/
@[expose] def lowerLeftSampleZero :
  LocalOwner (Legendre.Paths.polynomial lowerLeftParameter) := by
  apply UpperZero.ownerOf (Centered.sampleBox 0)
    (Centered.sampleBox_proper 0)
  · rw [lowerLeft_polynomial_eq_factors]
    exact Legendre.Polynomial.Clearance.lowerSampleZeroClearance lowerLeftParameter
      (by decide)
  · exact lowerLeftSampleZeroWinding

/-- The smaller sample-box owner of the moving root at the lower left parameter. -/
@[expose] def lowerLeftSampleMoving :
  LocalOwner (Legendre.Paths.polynomial lowerLeftParameter) := by
  apply UpperZero.ownerOf (Centered.sampleBox
    lowerLeftParameter)
    (Centered.sampleBox_proper lowerLeftParameter)
  · rw [lowerLeft_polynomial_eq_factors]
    exact Legendre.Polynomial.Clearance.lowerSampleMovingClearance
      lowerLeftParameter (by decide) (by decide)
  · exact lowerLeftSampleMovingWinding

/-- The smaller sample-box owner of the fixed root one at the lower left parameter. -/
@[expose] def lowerLeftSampleOne :
  LocalOwner (Legendre.Paths.polynomial lowerLeftParameter) := by
  apply UpperZero.ownerOf (Centered.sampleBox 1)
    (Centered.sampleBox_proper 1)
  · rw [lowerLeft_polynomial_eq_factors]
    exact Legendre.Polynomial.Clearance.lowerSampleOneClearance lowerLeftParameter
      (by decide)
  · exact lowerLeftSampleOneWinding

/-- The smaller sample-box owner of the fixed root zero at the lower right parameter. -/
@[expose] def lowerRightSampleZero :
  LocalOwner (Legendre.Paths.polynomial lowerRightParameter) := by
  apply UpperZero.ownerOf (Centered.sampleBox 0)
    (Centered.sampleBox_proper 0)
  · rw [lowerRight_polynomial_eq_factors]
    exact Legendre.Polynomial.Clearance.lowerRightSampleZeroClearance
      lowerRightParameter (by decide)
  · exact lowerRightSampleZeroWinding

/-- The smaller sample-box owner of the moving root at the lower right parameter. -/
@[expose] def lowerRightSampleMoving :
  LocalOwner (Legendre.Paths.polynomial lowerRightParameter) := by
  apply UpperZero.ownerOf (Centered.sampleBox
    lowerRightParameter)
    (Centered.sampleBox_proper lowerRightParameter)
  · rw [lowerRight_polynomial_eq_factors]
    exact Legendre.Polynomial.Clearance.lowerRightSampleMovingClearance
      lowerRightParameter
      (by decide) (by decide)
  · exact lowerRightSampleMovingWinding

/-- The smaller sample-box owner of the fixed root one at the lower right parameter. -/
@[expose] def lowerRightSampleOne :
  LocalOwner (Legendre.Paths.polynomial lowerRightParameter) := by
  apply UpperZero.ownerOf (Centered.sampleBox 1)
    (Centered.sampleBox_proper 1)
  · rw [lowerRight_polynomial_eq_factors]
    exact Legendre.Polynomial.Clearance.lowerSampleOneClearance lowerRightParameter
      (by decide)
  · exact lowerRightSampleOneWinding

/-- The three lower left owners, ordered as zero, moving root and one. -/
@[expose] def lowerLeftOwner : Fin 3 ->
  LocalOwner (Legendre.Paths.polynomial lowerLeftParameter) :=
  Data.Fin.cases (lowerLeftZeroOwner)
    (fun rest => Data.Fin.cases (lowerLeftMovingOwner)
      (fun _ => lowerLeftOneOwner) rest)

/-- The three lower right owners, ordered as zero, moving root and one. -/
@[expose] def lowerRightOwner : Fin 3 ->
  LocalOwner (Legendre.Paths.polynomial lowerRightParameter) :=
  Data.Fin.cases (lowerRightZeroOwner)
    (fun rest => Data.Fin.cases (lowerRightMovingOwner)
      (fun _ => lowerRightOneOwner) rest)

/-- Distinct lower left owner indices have separated boxes. -/
theorem lowerLeftOwner_pairwise : forall left right : Fin 3,
  left ≠ right ->
    (lowerLeftOwner left).box.Separated
      (lowerLeftOwner right).box := by
  intro left right different
  rcases Cases.three left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases Cases.three right with rightZero | rightOne | rightTwo <;>
    subst right <;>
    first | exact (different rfl).elim | decide

/-- Distinct lower right owner indices have separated boxes. -/
theorem lowerRightOwner_pairwise : forall left right : Fin
  3, left ≠ right ->
    (lowerRightOwner left).box.Separated
      (lowerRightOwner right).box := by
  intro left right different
  rcases Cases.three left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases Cases.three right with rightZero | rightOne | rightTwo <;>
    subst right <;>
    first | exact (different rfl).elim | decide

/-- The three pairwise-separated local owners at the lower left parameter. -/
@[expose] def lowerLeftOwnerFamily :
    Owner.Family.Basic.OwnerFamily
      (Legendre.Paths.polynomial lowerLeftParameter) 3 where
  owner := lowerLeftOwner
  pairwiseSeparated := lowerLeftOwner_pairwise

/-- The three pairwise-separated local owners at the lower right parameter. -/
@[expose] def lowerRightOwnerFamily :
    Owner.Family.Basic.OwnerFamily
      (Legendre.Paths.polynomial lowerRightParameter) 3 where
  owner := lowerRightOwner
  pairwiseSeparated := lowerRightOwner_pairwise

/-! ## Exact lower chambers and projected frames -/

/-- The exact coefficient-table polynomial at the lower left parameter is squarefree. -/
@[expose] def lowerLeftSquarefree :
  Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
    (Legendre.Coefficients.Exact.coefficientTable lowerLeftParameter).polynomial :=
      by
  rw [Legendre.Coefficients.Exact.coefficientTable_polynomial]
  exact Legendre.Squarefree.squarefreeAt lowerLeftParameter
    (by decide)

/-- The exact coefficient-table polynomial at the lower right parameter is squarefree. -/
@[expose] def lowerRightSquarefree :
  Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
    (Legendre.Coefficients.Exact.coefficientTable lowerRightParameter).polynomial :=
      by
  rw [Legendre.Coefficients.Exact.coefficientTable_polynomial]
  exact Legendre.Squarefree.squarefreeAt lowerRightParameter
    (by decide)

/-- The squarefree isolation input at the lower left parameter, retaining its degree-at-least-two proof. -/
@[expose] def lowerLeftIsolationInput :
    RootIsolation.FTA.Squarefree.Input (Legendre.Coefficients.Exact.coefficientTable
      lowerLeftParameter).polynomial where
  squarefree := lowerLeftSquarefree
  degreeAtLeastTwo := by decide

/-- The squarefree isolation input at the lower right parameter, retaining its degree-at-least-two proof. -/
@[expose] def lowerRightIsolationInput :
    RootIsolation.FTA.Squarefree.Input (Legendre.Coefficients.Exact.coefficientTable
      lowerRightParameter).polynomial where
  squarefree := lowerRightSquarefree
  degreeAtLeastTwo := by decide

/-- The exact root chamber at the lower left parameter.

The original coefficient table, separated owner family, coefficient allowance bound and finite isolation maximality
certificate are retained together. -/
@[expose] def lowerLeftChamber :
  Progressive.Chamber.Frame.ChamberFrame where
  reference := Legendre.Coefficients.Exact.coefficientTable lowerLeftParameter
  chamber :=
    { degreeAtLeastTwo := by decide
      squarefree := lowerLeftSquarefree
      owners := lowerLeftOwnerFamily
      referenceSmall := Legendre.Coefficients.Exact.coefficientTable_allowances_lt _
        (Progressive.Chamber.Target.simpleRootChamberTarget_pos
          (Legendre.Coefficients.Exact.coefficientTable lowerLeftParameter)
            lowerLeftSquarefree
          lowerLeftOwnerFamily)
      referenceMaximality :=
        (FTA.Squarefree.Build.Box.prove lowerLeftIsolationInput).boxes.maximality }

/-- The exact root chamber at the lower right parameter.

The original coefficient table, separated owner family, coefficient allowance bound and finite isolation maximality
certificate are retained together. -/
@[expose] def lowerRightChamber :
  Progressive.Chamber.Frame.ChamberFrame where
  reference := Legendre.Coefficients.Exact.coefficientTable lowerRightParameter
  chamber :=
    { degreeAtLeastTwo := by decide
      squarefree := lowerRightSquarefree
      owners := lowerRightOwnerFamily
      referenceSmall := Legendre.Coefficients.Exact.coefficientTable_allowances_lt _
        (Progressive.Chamber.Target.simpleRootChamberTarget_pos
          (Legendre.Coefficients.Exact.coefficientTable lowerRightParameter)
            lowerRightSquarefree
          lowerRightOwnerFamily)
      referenceMaximality :=
        (FTA.Squarefree.Build.Box.prove lowerRightIsolationInput).boxes.maximality }

/-- The lower left chamber represents the original Legendre polynomial. -/
@[simp] theorem lowerLeftChamber_polynomial :
    lowerLeftChamber.polynomial = Legendre.Paths.polynomial lowerLeftParameter :=
      rfl

/-- The lower right chamber represents the original Legendre polynomial. -/
@[simp] theorem lowerRightChamber_polynomial :
    lowerRightChamber.polynomial = Legendre.Paths.polynomial lowerRightParameter :=
      rfl

/-- The lower left sample owners in increasing real-projection order. -/
@[expose] def lowerLeftProjectionOwner :
    Fin 3 -> LocalOwner (Legendre.Paths.polynomial
      lowerLeftParameter) :=
  Data.Fin.cases (lowerLeftSampleMoving)
    (fun rest => Data.Fin.cases (lowerLeftSampleZero)
      (fun _ => lowerLeftSampleOne) rest)

/-- The lower right sample owners in increasing real-projection order. -/
@[expose] def lowerRightProjectionOwner :
    Fin 3 -> LocalOwner (Legendre.Paths.polynomial
      lowerRightParameter) :=
  Data.Fin.cases (lowerRightSampleZero)
    (fun rest => Data.Fin.cases (lowerRightSampleMoving)
      (fun _ => lowerRightSampleOne) rest)

/-- The projected frame at the lower left parameter.

Its original labels and chamber owners are linked to the retained sample boxes by refinement, containment and strict
projection order. -/
@[expose] def lowerLeftFrame : Legendre.Paths.Frame
  lowerLeftParameter where
  chamber := lowerLeftChamber
  polynomial_eq := rfl
  labels := Data.Fin.Bijection.identity 3
  owner_contains := by
    intro label
    rcases Cases.three label with labelZero | labelOne | labelTwo <;>
      subst label <;> decide
  projectionOrder := UpperZero.targetProjectionOrder
  projectionOwner := fun position =>
    Owner.Local.Transport.castOwner lowerLeftChamber_polynomial.symm
      (lowerLeftProjectionOwner position)
  projection_refines := by
    intro position
    rcases Cases.three position with positionZero | positionOne |
      positionTwo <;> subst position <;>
      simp only [lowerLeftProjectionOwner,
        UpperZero.targetProjectionOrder,
        lowerLeftChamber, lowerLeftOwnerFamily,
          lowerLeftOwner,
        lowerLeftSampleMoving,
          lowerLeftSampleZero,
          lowerLeftSampleOne,
        lowerLeftMovingOwner,
          lowerLeftZeroOwner, lowerLeftOneOwner,
          UpperZero.ownerOf,
        Owner.Local.Transport.castOwner_box,
        Progressive.Chamber.Frame.ChamberFrame.owner] <;>
      exact ⟨by decide, by decide, by decide, by decide⟩
  projection_xOrdered := by
    intro left right order
    rcases Cases.three left with leftZero | leftOne | leftTwo <;>
      subst left <;>
      rcases Cases.three right with rightZero | rightOne | rightTwo <;>
      subst right <;>
      simp only [Fin.isValue, Owner.Local.Transport.castOwner_box] at order ⊢ <;>
      first
      | exact ((by decide : ¬ ((0 : Nat) < 0)) order).elim
      | exact ((by decide : ¬ ((1 : Nat) < 0)) order).elim
      | exact ((by decide : ¬ ((1 : Nat) < 1)) order).elim
      | exact ((by decide : ¬ ((2 : Nat) < 0)) order).elim
      | exact ((by decide : ¬ ((2 : Nat) < 1)) order).elim
      | exact ((by decide : ¬ ((2 : Nat) < 2)) order).elim
      | decide

/-- The projected frame at the lower right parameter.

Its original labels and chamber owners are linked to the retained sample boxes by refinement, containment and strict
projection order. -/
@[expose] def lowerRightFrame : Legendre.Paths.Frame
  lowerRightParameter where
  chamber := lowerRightChamber
  polynomial_eq := rfl
  labels := Data.Fin.Bijection.identity 3
  owner_contains := by
    intro label
    rcases Cases.three label with labelZero | labelOne | labelTwo <;>
      subst label <;> decide
  projectionOrder := Data.Fin.Bijection.identity 3
  projectionOwner := fun position =>
    Owner.Local.Transport.castOwner lowerRightChamber_polynomial.symm
      (lowerRightProjectionOwner position)
  projection_refines := by
    intro position
    rcases Cases.three position with positionZero | positionOne |
      positionTwo <;> subst position <;>
      simp only [lowerRightProjectionOwner,
        Data.Fin.Bijection.identity,
        lowerRightChamber,
          lowerRightOwnerFamily,
          lowerRightOwner,
        lowerRightSampleMoving,
          lowerRightSampleZero,
          lowerRightSampleOne,
        lowerRightMovingOwner,
          lowerRightZeroOwner,
          lowerRightOneOwner, UpperZero.ownerOf,
        Owner.Local.Transport.castOwner_box,
        Progressive.Chamber.Frame.ChamberFrame.owner] <;>
      exact ⟨by decide, by decide, by decide, by decide⟩
  projection_xOrdered := by
    intro left right order
    rcases Cases.three left with leftZero | leftOne | leftTwo <;>
      subst left <;>
      rcases Cases.three right with rightZero | rightOne | rightTwo <;>
      subst right <;>
      simp only [Fin.isValue, Owner.Local.Transport.castOwner_box] at order ⊢ <;>
      first
      | exact ((by decide : ¬ ((0 : Nat) < 0)) order).elim
      | exact ((by decide : ¬ ((1 : Nat) < 0)) order).elim
      | exact ((by decide : ¬ ((1 : Nat) < 1)) order).elim
      | exact ((by decide : ¬ ((2 : Nat) < 0)) order).elim
      | exact ((by decide : ¬ ((2 : Nat) < 1)) order).elim
      | exact ((by decide : ¬ ((2 : Nat) < 2)) order).elim
      | decide

/-! ## The lower positive crossing -/

/-- The polynomial perturbation moving the lower-left parameter to the lower-right parameter. -/
@[expose] def lowerPerturbation : GaussianPolynomial :=
  Legendre.Polynomial.perturbationAt lowerLeftParameter
    lowerRightParameter

/-- The lower-right Legendre polynomial is the lower-left polynomial plus the retained perturbation. -/
theorem lower_target_eq_add : Legendre.Paths.polynomial
  lowerRightParameter =
    Legendre.Paths.polynomial lowerLeftParameter + lowerPerturbation := by
  decide

/-- Orient a supplied boundary-dominance witness from the lower-left polynomial to the lower-right polynomial.

The original owner box and exact perturbation equation are retained in the Rouche certificate. -/
@[expose] def lowerOrientedRouche
    (owner : LocalOwner (Legendre.Paths.polynomial
      lowerLeftParameter))
    (dominance : BoundaryNormDominance
      (Legendre.Paths.polynomial lowerLeftParameter)
        lowerPerturbation owner.box) :
    Box.Rouche.Connection.OrientedRouche
      (Legendre.Paths.polynomial lowerLeftParameter) (Legendre.Paths.polynomial
        lowerRightParameter)
      owner.box where
  perturbation := lowerPerturbation
  target_eq_add := lower_target_eq_add
  dominance := dominance

/-- The lower parameter perturbation is boundary dominated on the fixed root zero owner box. -/
@[expose] def lowerZeroDominance :
  BoundaryNormDominance
    (Legendre.Paths.polynomial lowerLeftParameter)
      lowerPerturbation
      lowerLeftZeroOwner.box :=
  Legendre.Rouche.factorMoveDominanceAt lowerLeftParameter
    lowerRightParameter
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (belowClearance lowerLeftParameter (by decide))
    (rightClearance 1 (by decide)) (by decide)

/-- The lower parameter perturbation is boundary dominated on the moving root owner box. -/
@[expose] def lowerMovingDominance :
  BoundaryNormDominance
    (Legendre.Paths.polynomial lowerLeftParameter)
      lowerPerturbation
      lowerLeftMovingOwner.box :=
  Legendre.Rouche.factorMoveDominanceAt lowerLeftParameter
    lowerRightParameter
    (aboveClearance 0 (by decide))
    (centeredClearance lowerLeftParameter
      (by decide) (by decide) (by decide) (by decide))
    (aboveClearance 1 (by decide)) (by decide)

/-- The lower parameter perturbation is boundary dominated on the fixed root one owner box. -/
@[expose] def lowerOneDominance :
  BoundaryNormDominance
    (Legendre.Paths.polynomial lowerLeftParameter)
      lowerPerturbation
      lowerLeftOneOwner.box :=
  Legendre.Rouche.factorMoveDominanceAt lowerLeftParameter
    lowerRightParameter
    (leftClearance 0 (by decide))
    (belowClearance lowerLeftParameter (by decide))
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))
    (by decide)

/-- The oriented Rouche owner bridge for the fixed root zero across the lower crossing. -/
@[expose] def lowerZeroBridge :
  OwnerBridge
    (Legendre.Paths.polynomial lowerLeftParameter) (Legendre.Paths.polynomial
      lowerRightParameter) :=
  OwnerBridge.ofForward lowerLeftZeroOwner
    (lowerOrientedRouche lowerLeftZeroOwner
      lowerZeroDominance)

/-- The oriented Rouche owner bridge for the moving root across the lower crossing. -/
@[expose] def lowerMovingBridge :
  OwnerBridge
    (Legendre.Paths.polynomial lowerLeftParameter) (Legendre.Paths.polynomial
      lowerRightParameter) :=
  OwnerBridge.ofForward lowerLeftMovingOwner
    (lowerOrientedRouche lowerLeftMovingOwner
      lowerMovingDominance)

/-- The oriented Rouche owner bridge for the fixed root one across the lower crossing. -/
@[expose] def lowerOneBridge :
  OwnerBridge
    (Legendre.Paths.polynomial lowerLeftParameter) (Legendre.Paths.polynomial
      lowerRightParameter) :=
  OwnerBridge.ofForward lowerLeftOneOwner
    (lowerOrientedRouche lowerLeftOneOwner
      lowerOneDominance)

/-- Select the retained zero, moving-root or one bridge by its original root index. -/
@[expose] def lowerBridgeAt : Fin 3 ->
  OwnerBridge
    (Legendre.Paths.polynomial lowerLeftParameter) (Legendre.Paths.polynomial
      lowerRightParameter) :=
  Data.Fin.cases (lowerZeroBridge)
    (fun rest => Data.Fin.cases (lowerMovingBridge)
      (fun _ => lowerOneBridge) rest)

/-- The overlap matching the lower-left and lower-right chambers by root label.

Its three original Rouche bridges refine both corresponding endpoint owners. -/
@[expose] def lowerChamberOverlap :
  Progressive.Chamber.Overlap.ChamberOverlap
    lowerLeftChamber lowerRightChamber where
  matching := Data.Fin.Bijection.identity 3
  bridge := lowerBridgeAt
  bridge_refines_left := by
    intro index
    rcases Cases.three index with indexZero | indexOne | indexTwo <;>
      subst index <;> exact Rational.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rcases Cases.three index with indexZero | indexOne | indexTwo <;>
      subst index <;> exact Rational.Box.refines_refl _

/-- The moving owner lies strictly below the zero owner across the lower positive crossing. -/
theorem lowerCrossingGeometry :
    Progressive.Braid.Projected.Overlap.CrossingGeometry
      lowerLeftFrame.projected
        lowerRightFrame.projected
        lowerChamberOverlap
      Legendre.Conventions.lowerPositive where
  heightSeparated := by
    change lowerMovingBox.yUpper <
      (Centered.realAxisSquareSixteenth 0).yLower
    decide

/-- The projected chamber overlap with its single lower-positive crossing and retained label matching. -/
@[expose] def lowerProjectedOverlap :
  Progressive.Braid.Projected.Overlap.ProjectedOverlap
    lowerLeftFrame.projected
      lowerRightFrame.projected :=
  .crossing lowerChamberOverlap
    Legendre.Conventions.lowerPositive lowerCrossingGeometry (by
      intro position
      change UpperZero.targetProjectionOrder.forward position =
        Legendre.Conventions.lowerPositive.permutation.forward position
      rcases Cases.three position with positionZero | positionOne |
        positionTwo <;> subst position <;> rfl)

/-- The minimum of the six endpoint boundary-clearance bounds of the three lower bridges. -/
@[expose] def lowerSheetBound : Fraction.Rational :=
  min lowerZeroBridge.leftClearance.bound
    (min lowerZeroBridge.rightClearance.bound
      (min lowerMovingBridge.leftClearance.bound
        (min lowerMovingBridge.rightClearance.bound
          (min lowerOneBridge.leftClearance.bound
            lowerOneBridge.rightClearance.bound))))

/-- The common lower-bridge sheet-clearance bound is positive. -/
theorem lowerSheetBound_positive : 0 < lowerSheetBound := by
  unfold lowerSheetBound
  exact Fraction.Order.Basic.lt_min lowerZeroBridge.leftClearance.positive
    (Fraction.Order.Basic.lt_min lowerZeroBridge.rightClearance.positive
      (Fraction.Order.Basic.lt_min lowerMovingBridge.leftClearance.positive
        (Fraction.Order.Basic.lt_min lowerMovingBridge.rightClearance.positive
          (Fraction.Order.Basic.lt_min lowerOneBridge.leftClearance.positive
            lowerOneBridge.rightClearance.positive))))

/-- The positive common sheet clearance for the three retained lower-crossing bridges.

The minimum bound lies below each original left and right boundary clearance. -/
@[expose] def lowerSheetClearance :
  Legendre.Paths.BridgeClearance lowerLeftFrame
  lowerRightFrame
    lowerChamberOverlap where
  bound := lowerSheetBound
  positive := lowerSheetBound_positive
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

/-- The horizontal segment from `-1/4 - 2i` to `1/4 - 2i`. -/
@[expose] def lowerGeometry : Legendre.Paths.AxisSegment
  lowerLeftParameter lowerRightParameter :=
  .horizontal (-(1 / 4)) (1 / 4) (-2)

/-- The displayed lower horizontal segment stays away from both excluded parameters zero and one. -/
@[expose] def lowerGeometrySafe :
  Legendre.Paths.AxisSegment.Safe lowerGeometry where
  avoidsZero := { bound := 1, positive := by decide, lower := by decide }
  avoidsOne := { bound := 1, positive := by decide, lower := by decide }

/-- The certified lower-positive Legendre crossing segment.

It combines the retained horizontal path, avoidance bounds, projected overlap and common sheet clearance. -/
@[expose] def lowerSegment : Legendre.Paths.Segment
  lowerLeftFrame lowerRightFrame :=
  Legendre.Paths.Segment.ofProjectedOverlap lowerGeometry
    lowerGeometrySafe
    lowerProjectedOverlap lowerSheetClearance

/-- The lower segment has exactly the lower-positive crossing. -/
@[simp] theorem lowerSegment_crossings :
  lowerSegment.crossings =
    [Legendre.Conventions.lowerPositive] := rfl

/-- The one-segment path from the lower-left frame to the lower-right frame. -/
@[expose] def lowerPath : Legendre.Paths.Path
  lowerLeftFrame lowerRightFrame :=
  .cons lowerSegment (.nil lowerRightFrame)

/-- The lower path has the one-letter lower-positive crossing word. -/
@[simp] theorem lowerPath_word :
  lowerPath.word =
    [Legendre.Conventions.lowerPositive] := rfl

end Purelib.Examples.Curves.Legendre.Crossings.LowerZero

end
