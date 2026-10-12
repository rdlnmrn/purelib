module
import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.Data.Fin.Cases
import Purelib.Data.Fin
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Progressive.Chamber.Target
import Purelib.Polynomial.Clearance.Box.Boundary.Translated
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Vector.Operational.Basic
import Purelib.Approximation.Matrix.Operational.Integral.Action
public import Purelib.Curves.Legendre.Coefficients.Exact
public import Purelib.Curves.Legendre.Conventions
public import Purelib.Curves.Legendre.GaussManin.Endpoint
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Polynomial
public import Purelib.Curves.Legendre.Polynomial.Clearance
import Purelib.Curves.Legendre.Polynomial.Winding
public import Purelib.Curves.Legendre.Rouche
public import Purelib.Curves.Legendre.Squarefree
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.LinearAlgebra.Matrix.Integral.Two
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Winding.Box.Affine
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Rouche.Connection
public import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.RootIsolation.FTA.Squarefree.Build
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Owner.Bridge.Rouche
public import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.RootIsolation.Progressive.Braid.Projected.Overlap
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
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

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
public section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

namespace Purelib.Examples.Curves.Legendre.Crossings.UpperZero

open Purelib.Polynomial.Clearance.Box.Boundary.Translated
open Purelib.Polynomial.Winding
open Purelib.Data.Fin
open Purelib.Polynomial.Clearance.Box.Dominance.Basic (BoundaryNormDominance)

open Purelib.Examples

open Purelib.Approximation
open Purelib.Curves
open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib.Topology

open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)
open Purelib.RootIsolation.Owner.Local.Basic (LocalOwner)
open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)
open Purelib.Polynomial.Dense.Gaussian.Linear
open Purelib.Geometry.Rational.Box.Square
open Purelib.Approximation.Gaussian.Vector.Operational.Basic (VectorEquivalent)

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Legendre.Paths (GaussianPolynomial)

/-- The starting parameter 1/4+2i of the positive crossing over zero. -/
@[expose] def sourceParameter : Gaussian :=
  Legendre.Paths.gaussian (1 / 4) 2
/-- The ending parameter -1/4+2i of the positive crossing over zero. -/
@[expose] def targetParameter : Gaussian :=
  Legendre.Paths.gaussian (-(1 / 4)) 2

/-- The source Legendre polynomial equals its displayed product of three linear root factors. -/
theorem source_polynomial_eq_factors :
    Legendre.Paths.polynomial sourceParameter = Legendre.Polynomial.factorsAt
      sourceParameter := by
  exact Legendre.Polynomial.polynomial_eq_factorsAt sourceParameter

/-- The target Legendre polynomial equals its displayed product of three linear root factors. -/
theorem target_polynomial_eq_factors :
    Legendre.Paths.polynomial targetParameter = Legendre.Polynomial.factorsAt
      targetParameter := by
  exact Legendre.Polynomial.polynomial_eq_factorsAt targetParameter

/-- The common moving-root box with real bounds -1 and 1 and imaginary bounds 1 and 3. -/
@[expose] def movingBox : Rational.Box where
  xLower := -1
  xUpper := 1
  yLower := 1
  yUpper := 3
  x_valid := by decide
  y_valid := by decide

/-- Both coordinate intervals of the moving-root box have strictly positive width. -/
theorem movingBox_proper :
  movingBox.Proper := by
  constructor <;> decide

/-- Certify the Legendre product on the broad zero box when the moving root lies strictly above it. -/
@[expose] def broadZeroClearance (lambda :
  Gaussian.Basic.Canonical)
    (movingAbove : (Centered.realAxisSquareSixteenth 0).yUpper < lambda.im) :
    BoundaryClearance (Legendre.Polynomial.factorsAt lambda)
      (Centered.realAxisSquareSixteenth 0) :=
  Legendre.Polynomial.Clearance.factorsClearance
    (ExplicitLegendreSegment.centeredClearance 0 (by decide) (by decide) (by decide)
      (by decide))
    (ExplicitLegendreSegment.aboveClearance lambda movingAbove)
    (ExplicitLegendreSegment.rightClearance 1 (by decide))

/-- Certify the Legendre product on the common moving box from four strict interior bounds on the moving root. -/
@[expose] def broadMovingClearance (lambda :
  Gaussian.Basic.Canonical)
    (insideLeft : movingBox.xLower < lambda.re)
    (insideRight : lambda.re < movingBox.xUpper)
    (insideBelow : movingBox.yLower < lambda.im)
    (insideAbove : lambda.im < movingBox.yUpper) :
    BoundaryClearance (Legendre.Polynomial.factorsAt lambda) movingBox :=
  Legendre.Polynomial.Clearance.factorsClearance
    (ExplicitLegendreSegment.belowClearance 0 (by decide))
    (ExplicitLegendreSegment.centeredClearance lambda insideLeft insideRight
      insideBelow insideAbove)
    (ExplicitLegendreSegment.belowClearance 1 (by decide))

/-- Certify the Legendre product on the broad one box when the moving root lies strictly above it. -/
@[expose] def broadOneClearance (lambda :
  Gaussian.Basic.Canonical)
    (movingAbove : (Centered.realAxisSquareSixteenth 1).yUpper < lambda.im) :
    BoundaryClearance (Legendre.Polynomial.factorsAt lambda)
      (Centered.realAxisSquareSixteenth 1) :=
  Legendre.Polynomial.Clearance.factorsClearance
    (ExplicitLegendreSegment.leftClearance 0 (by decide))
    (ExplicitLegendreSegment.aboveClearance lambda movingAbove)
    (ExplicitLegendreSegment.centeredClearance 1 (by decide) (by decide) (by decide)
      (by decide))

/-- Certify the Legendre product on the small zero sample box when the moving root lies above it. -/
@[expose] def sampleZeroClearance (lambda :
  Gaussian.Basic.Canonical)
    (movingAbove : (Centered.sampleBox 0).yUpper < lambda.im) :
    BoundaryClearance (Legendre.Polynomial.factorsAt lambda)
      (Centered.sampleBox 0) :=
  Legendre.Polynomial.Clearance.factorsClearance
    (ExplicitLegendreSegment.centeredClearance 0 (by decide) (by decide) (by decide)
      (by decide))
    (ExplicitLegendreSegment.aboveClearance lambda movingAbove)
    (ExplicitLegendreSegment.rightClearance 1 (by decide))

/-- Certify the Legendre product on the moving-root sample box when its imaginary part exceeds one sixteenth. -/
@[expose] def sampleMovingClearance (lambda :
  Gaussian.Basic.Canonical)
    (imaginaryHigh : (1 / 16 : Fraction.Rational) < lambda.im) :
    BoundaryClearance (Legendre.Polynomial.factorsAt lambda)
      (Centered.sampleBox lambda) :=
  Legendre.Polynomial.Clearance.factorsClearance
    (ExplicitLegendreSegment.belowClearance 0 (by
      change (0 : Fraction.Rational) < lambda.im - 1 / 16
      exact Fraction.Order.Arithmetic.sub_pos_direct imaginaryHigh))
    (ExplicitLegendreSegment.centeredClearance lambda
      (by
        change lambda.re - 1 / 16 < lambda.re
        have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 16) lambda.re
        have scalarZero : lambda.re - 0 = lambda.re := by
          rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
            show -(0 : Fraction.Rational) = 0 by decide]
          exact (Fraction.Field.add_comm lambda.re 0).trans (Fraction.Field.zero_add lambda.re)
        rewrite [scalarZero] at translated
        exact translated)
      (by
        change lambda.re < lambda.re + 1 / 16
        have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 16) lambda.re
        have scalarZero : lambda.re + 0 = lambda.re :=
          (Fraction.Field.add_comm lambda.re 0).trans (Fraction.Field.zero_add lambda.re)
        rewrite [scalarZero] at translated
        exact translated)
      (by
        change lambda.im - 1 / 16 < lambda.im
        have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 16) lambda.im
        have scalarZero : lambda.im - 0 = lambda.im := by
          rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct,
            show -(0 : Fraction.Rational) = 0 by decide]
          exact (Fraction.Field.add_comm lambda.im 0).trans (Fraction.Field.zero_add lambda.im)
        rewrite [scalarZero] at translated
        exact translated)
      (by
        change lambda.im < lambda.im + 1 / 16
        have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 16) lambda.im
        have scalarZero : lambda.im + 0 = lambda.im :=
          (Fraction.Field.add_comm lambda.im 0).trans (Fraction.Field.zero_add lambda.im)
        rewrite [scalarZero] at translated
        exact translated))
    (ExplicitLegendreSegment.belowClearance 1 (by
      change (0 : Fraction.Rational) < lambda.im - 1 / 16
      exact Fraction.Order.Arithmetic.sub_pos_direct imaginaryHigh))

/-- Certify the Legendre product on the small one sample box when the moving root lies above it. -/
@[expose] def sampleOneClearance (lambda :
  Gaussian.Basic.Canonical)
    (movingAbove : (Centered.sampleBox 1).yUpper < lambda.im) :
    BoundaryClearance (Legendre.Polynomial.factorsAt lambda)
      (Centered.sampleBox 1) :=
  Legendre.Polynomial.Clearance.factorsClearance
    (ExplicitLegendreSegment.leftClearance 0 (by decide))
    (ExplicitLegendreSegment.aboveClearance lambda movingAbove)
    (ExplicitLegendreSegment.centeredClearance 1 (by decide) (by decide) (by decide)
      (by decide))

/-! ## Exact endpoint chambers -/

/-- Transport a boundary clearance of the factored source cubic to its exact coefficient polynomial. -/
@[expose] def sourcePolynomialClearance {box :
  Rational.Box}
    (clearance : BoundaryClearance (Legendre.Polynomial.factorsAt
      sourceParameter) box) :
    BoundaryClearance (Legendre.Paths.polynomial
      sourceParameter) box := by
  rw [source_polynomial_eq_factors]
  exact clearance

/-- Transport a boundary clearance of the factored target cubic to its exact coefficient polynomial. -/
@[expose] def targetPolynomialClearance {box :
  Rational.Box}
    (clearance : BoundaryClearance (Legendre.Polynomial.factorsAt
      targetParameter) box) :
    BoundaryClearance (Legendre.Paths.polynomial
      targetParameter) box := by
  rw [target_polynomial_eq_factors]
  exact clearance

/-- Construct a local root owner from the exact box, properness, boundary clearance and quadrupled winding four. -/
@[expose] def ownerOf {lambda : Gaussian.Basic.Canonical}
  (box : Rational.Box) (proper : box.Proper)
    (clearance : BoundaryClearance (Legendre.Paths.polynomial lambda) box)
    (winding : Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial lambda) box = 4) :
    LocalOwner (Legendre.Paths.polynomial lambda) where
  box := box
  proper := proper
  clearance := clearance
  rawWindingFour := winding

/-- The source moving root lies strictly above the broad box around zero. -/
theorem source_above_fixedZero :
    (Centered.realAxisSquareSixteenth 0).yUpper <
      sourceParameter.im := by
  change (1 / 16 : Fraction.Rational) < 2
  decide

/-- The source moving root lies strictly above the broad box around one. -/
theorem source_above_fixedOne :
    (Centered.realAxisSquareSixteenth 1).yUpper <
      sourceParameter.im :=
      source_above_fixedZero

/-- The target moving root lies strictly above the broad box around zero. -/
theorem target_above_fixedZero :
    (Centered.realAxisSquareSixteenth 0).yUpper <
      targetParameter.im := by
  change (1 / 16 : Fraction.Rational) < 2
  decide

/-- The target moving root lies strictly above the broad box around one. -/
theorem target_above_fixedOne :
    (Centered.realAxisSquareSixteenth 1).yUpper <
      targetParameter.im :=
      target_above_fixedZero

/-- The source moving root lies strictly inside the common moving-root box. -/
theorem source_in_movingBox :
    movingBox.xLower < sourceParameter.re ∧
      sourceParameter.re < movingBox.xUpper ∧
      movingBox.yLower < sourceParameter.im ∧
      sourceParameter.im < movingBox.yUpper :=
        by
  constructor
  · change (-1 : Fraction.Rational) < 1 / 4
    decide
  constructor
  · change (1 / 4 : Fraction.Rational) < 1
    decide
  constructor
  · change (1 : Fraction.Rational) < 2
    decide
  · change (2 : Fraction.Rational) < 3
    decide

/-- The target moving root lies strictly inside the common moving-root box. -/
theorem target_in_movingBox :
    movingBox.xLower < targetParameter.re ∧
      targetParameter.re < movingBox.xUpper ∧
      movingBox.yLower < targetParameter.im ∧
      targetParameter.im < movingBox.yUpper :=
        by
  constructor
  · change (-1 : Fraction.Rational) < -(1 / 4)
    decide
  constructor
  · change (-(1 / 4) : Fraction.Rational) < 1
    decide
  exact source_in_movingBox.2.2

/-- The source moving root lies strictly above the small sample box around zero. -/
theorem source_above_sampleZero :
    (Centered.sampleBox 0).yUpper < sourceParameter.im := by
  change (1 / 16 : Fraction.Rational) < 2
  decide

/-- The source moving root lies strictly above the small sample box around one. -/
theorem source_above_sampleOne :
    (Centered.sampleBox 1).yUpper < sourceParameter.im :=
      source_above_sampleZero

/-- The target moving root lies strictly above the small sample box around zero. -/
theorem target_above_sampleZero :
    (Centered.sampleBox 0).yUpper < targetParameter.im := by
  change (1 / 16 : Fraction.Rational) < 2
  decide

/-- The target moving root lies strictly above the small sample box around one. -/
theorem target_above_sampleOne :
    (Centered.sampleBox 1).yUpper < targetParameter.im :=
      target_above_sampleZero

/-- The source moving root has imaginary part greater than one sixteenth. -/
theorem source_imaginary_high :
    (1 / 16 : Fraction.Rational) < sourceParameter.im := by
  change (1 / 16 : Fraction.Rational) < 2
  decide

/-- The target moving root has imaginary part greater than one sixteenth. -/
theorem target_imaginary_high :
    (1 / 16 : Fraction.Rational) < targetParameter.im := by
  change (1 / 16 : Fraction.Rational) < 2
  decide

/-- The source cubic has quadrupled winding four around the broad zero box. -/
theorem sourceZeroWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial sourceParameter)
        (Centered.realAxisSquareSixteenth 0) = 4 := by
  rw [source_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.realAxisSquareSixteenth_proper
    0)
    (ExplicitLegendreSegment.centeredClearance 0 (by decide) (by decide) (by decide)
      (by decide))
    (ExplicitLegendreSegment.aboveClearance
      sourceParameter source_above_fixedZero)
    (ExplicitLegendreSegment.rightClearance 1 (by decide))
  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
        (Centered.realAxisSquareSixteenth 0) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate 0
      (by decide) (by decide) (by decide) (by decide)
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        sourceParameter)
        (Centered.realAxisSquareSixteenth 0) = 0 := by decide
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
        (Centered.realAxisSquareSixteenth 0) = 0 := by
    decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The source cubic has quadrupled winding four around the broad moving root box. -/
theorem sourceMovingWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial sourceParameter)
        movingBox = 4 := by
  rw [source_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum movingBox_proper
    (ExplicitLegendreSegment.belowClearance 0 (by decide))
    (ExplicitLegendreSegment.centeredClearance
      sourceParameter source_in_movingBox.1
      source_in_movingBox.2.1
        source_in_movingBox.2.2.1
      source_in_movingBox.2.2.2)
    (ExplicitLegendreSegment.belowClearance 1 (by decide))
  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0) movingBox =
        0 := by decide
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        sourceParameter)
        movingBox = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate
      sourceParameter source_in_movingBox.1
        source_in_movingBox.2.1
      source_in_movingBox.2.2.1
        source_in_movingBox.2.2.2
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1) movingBox =
        0 := by decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The source cubic has quadrupled winding four around the broad one box. -/
theorem sourceOneWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial sourceParameter)
        (Centered.realAxisSquareSixteenth 1) = 4 := by
  rw [source_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.realAxisSquareSixteenth_proper
    1)
    (ExplicitLegendreSegment.leftClearance 0 (by decide))
    (ExplicitLegendreSegment.aboveClearance
      sourceParameter source_above_fixedOne)
    (ExplicitLegendreSegment.centeredClearance 1 (by decide) (by decide) (by decide)
      (by decide))
  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
        (Centered.realAxisSquareSixteenth 1) = 0 := by decide
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        sourceParameter)
        (Centered.realAxisSquareSixteenth 1) = 0 := by decide
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
        (Centered.realAxisSquareSixteenth 1) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate 1
      (by decide) (by decide) (by decide) (by decide)
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The target cubic has quadrupled winding four around the broad zero box. -/
theorem targetZeroWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial targetParameter)
        (Centered.realAxisSquareSixteenth 0) = 4 := by
  rw [target_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.realAxisSquareSixteenth_proper
    0)
    (ExplicitLegendreSegment.centeredClearance 0 (by decide) (by decide) (by decide)
      (by decide))
    (ExplicitLegendreSegment.aboveClearance
      targetParameter target_above_fixedZero)
    (ExplicitLegendreSegment.rightClearance 1 (by decide))
  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
        (Centered.realAxisSquareSixteenth 0) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate 0
      (by decide) (by decide) (by decide) (by decide)
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        targetParameter)
        (Centered.realAxisSquareSixteenth 0) = 0 := by decide
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
        (Centered.realAxisSquareSixteenth 0) = 0 := by
    decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The target cubic has quadrupled winding four around the broad moving root box. -/
theorem targetMovingWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial targetParameter)
        movingBox = 4 := by
  rw [target_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum movingBox_proper
    (ExplicitLegendreSegment.belowClearance 0 (by decide))
    (ExplicitLegendreSegment.centeredClearance
      targetParameter target_in_movingBox.1
      target_in_movingBox.2.1
        target_in_movingBox.2.2.1
      target_in_movingBox.2.2.2)
    (ExplicitLegendreSegment.belowClearance 1 (by decide))
  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0) movingBox =
        0 := by decide
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        targetParameter)
        movingBox = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate
      targetParameter target_in_movingBox.1
        target_in_movingBox.2.1
      target_in_movingBox.2.2.1
        target_in_movingBox.2.2.2
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1) movingBox =
        0 := by decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The target cubic has quadrupled winding four around the broad one box. -/
theorem targetOneWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial targetParameter)
        (Centered.realAxisSquareSixteenth 1) = 4 := by
  rw [target_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.realAxisSquareSixteenth_proper
    1)
    (ExplicitLegendreSegment.leftClearance 0 (by decide))
    (ExplicitLegendreSegment.aboveClearance
      targetParameter target_above_fixedOne)
    (ExplicitLegendreSegment.centeredClearance 1 (by decide) (by decide) (by decide)
      (by decide))
  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0)
        (Centered.realAxisSquareSixteenth 1) = 0 := by decide
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        targetParameter)
        (Centered.realAxisSquareSixteenth 1) = 0 := by decide
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1)
        (Centered.realAxisSquareSixteenth 1) = 4 :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate 1
      (by decide) (by decide) (by decide) (by decide)
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The source cubic has quadrupled winding four around the small zero sample box. -/
theorem sourceSampleZeroWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial sourceParameter)
        (Centered.sampleBox 0) = 4 := by
  rw [source_polynomial_eq_factors]
  apply Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.sampleBox_proper 0)
    (ExplicitLegendreSegment.centeredClearance 0 (by decide) (by decide) (by decide)
      (by decide))
    (ExplicitLegendreSegment.aboveClearance
      sourceParameter source_above_sampleZero)
    (ExplicitLegendreSegment.rightClearance 1 (by decide))
  have zeroWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 0) (Centered.sampleBox 0) = 4
        :=
    Box.Affine.quadrupledBoxWinding_translatedCoordinate 0
      (by decide) (by decide) (by decide) (by decide)
  have movingWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate
        sourceParameter)
        (Centered.sampleBox 0) = 0 := by decide
  have oneWinding : Box.Basic.quadrupledBoxWinding
      (Translated.translatedCoordinate 1) (Centered.sampleBox 0) = 0
        := by decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

/-- The source cubic has quadrupled winding four around the small moving root sample box. -/
theorem sourceSampleMovingWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial sourceParameter)
        (Centered.sampleBox sourceParameter) = 4 := by
  rw [source_polynomial_eq_factors]
  exact Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.sampleBox_proper
    sourceParameter)
    (ExplicitLegendreSegment.belowClearance 0 (by decide))
    (ExplicitLegendreSegment.centeredClearance
      sourceParameter (by decide) (by decide)
      (by decide) (by decide))
    (ExplicitLegendreSegment.belowClearance 1 (by decide)) (by decide)

/-- The source cubic has quadrupled winding four around the small one sample box. -/
theorem sourceSampleOneWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial sourceParameter)
        (Centered.sampleBox 1) = 4 := by
  rw [source_polynomial_eq_factors]
  exact Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.sampleBox_proper 1)
    (ExplicitLegendreSegment.leftClearance 0 (by decide))
    (ExplicitLegendreSegment.aboveClearance
      sourceParameter source_above_sampleOne)
    (ExplicitLegendreSegment.centeredClearance 1 (by decide) (by decide) (by decide)
      (by decide))
    (by decide)

/-- The target cubic has quadrupled winding four around the small zero sample box. -/
theorem targetSampleZeroWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial targetParameter)
        (Centered.sampleBox 0) = 4 := by
  rw [target_polynomial_eq_factors]
  exact Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.sampleBox_proper 0)
    (ExplicitLegendreSegment.centeredClearance 0 (by decide) (by decide) (by decide)
      (by decide))
    (ExplicitLegendreSegment.aboveClearance
      targetParameter target_above_sampleZero)
    (ExplicitLegendreSegment.rightClearance 1 (by decide)) (by decide)

/-- The target cubic has quadrupled winding four around the small moving root sample box. -/
theorem targetSampleMovingWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial targetParameter)
        (Centered.sampleBox targetParameter) = 4 := by
  rw [target_polynomial_eq_factors]
  exact Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.sampleBox_proper
    targetParameter)
    (ExplicitLegendreSegment.belowClearance 0 (by decide))
    (ExplicitLegendreSegment.centeredClearance
      targetParameter (by decide) (by decide)
      (by decide) (by decide))
    (ExplicitLegendreSegment.belowClearance 1 (by decide)) (by decide)

/-- The target cubic has quadrupled winding four around the small one sample box. -/
theorem targetSampleOneWinding :
    Box.Basic.quadrupledBoxWinding
      (Legendre.Paths.polynomial targetParameter)
        (Centered.sampleBox 1) = 4 := by
  rw [target_polynomial_eq_factors]
  exact Legendre.Polynomial.Winding.factors_winding_of_sum (Centered.sampleBox_proper 1)
    (ExplicitLegendreSegment.leftClearance 0 (by decide))
    (ExplicitLegendreSegment.aboveClearance
      targetParameter target_above_sampleOne)
    (ExplicitLegendreSegment.centeredClearance 1 (by decide) (by decide) (by decide)
      (by decide))
    (by decide)

/-- The source broad zero owner with its exact box, boundary clearance and winding certificate. -/
@[expose] def sourceZeroOwner : LocalOwner
  (Legendre.Paths.polynomial sourceParameter) :=
  ownerOf (Centered.realAxisSquareSixteenth 0)
    (Centered.realAxisSquareSixteenth_proper 0)
    (sourcePolynomialClearance
      (broadZeroClearance sourceParameter
        source_above_fixedZero))
    sourceZeroWinding

/-- The source broad moving root owner with its exact box, boundary clearance and winding certificate. -/
@[expose] def sourceMovingOwner :
  LocalOwner (Legendre.Paths.polynomial sourceParameter) :=
  ownerOf movingBox
    movingBox_proper
    (sourcePolynomialClearance
      (broadMovingClearance sourceParameter
        source_in_movingBox.1
        source_in_movingBox.2.1
          source_in_movingBox.2.2.1
        source_in_movingBox.2.2.2))
          sourceMovingWinding

/-- The source broad one owner with its exact box, boundary clearance and winding certificate. -/
@[expose] def sourceOneOwner : LocalOwner
  (Legendre.Paths.polynomial sourceParameter) :=
  ownerOf (Centered.realAxisSquareSixteenth 1)
    (Centered.realAxisSquareSixteenth_proper 1)
    (sourcePolynomialClearance
      (broadOneClearance sourceParameter
        source_above_fixedOne)) sourceOneWinding

/-- The target broad zero owner with its exact box, boundary clearance and winding certificate. -/
@[expose] def targetZeroOwner : LocalOwner
  (Legendre.Paths.polynomial targetParameter) :=
  ownerOf (Centered.realAxisSquareSixteenth 0)
    (Centered.realAxisSquareSixteenth_proper 0)
    (targetPolynomialClearance
      (broadZeroClearance targetParameter
        target_above_fixedZero))
    targetZeroWinding

/-- The target broad moving root owner with its exact box, boundary clearance and winding certificate. -/
@[expose] def targetMovingOwner :
  LocalOwner (Legendre.Paths.polynomial targetParameter) :=
  ownerOf movingBox
    movingBox_proper
    (targetPolynomialClearance
      (broadMovingClearance targetParameter
        target_in_movingBox.1
        target_in_movingBox.2.1
          target_in_movingBox.2.2.1
        target_in_movingBox.2.2.2))
          targetMovingWinding

/-- The target broad one owner with its exact box, boundary clearance and winding certificate. -/
@[expose] def targetOneOwner : LocalOwner
  (Legendre.Paths.polynomial targetParameter) :=
  ownerOf (Centered.realAxisSquareSixteenth 1)
    (Centered.realAxisSquareSixteenth_proper 1)
    (targetPolynomialClearance
      (broadOneClearance targetParameter
        target_above_fixedOne)) targetOneWinding

/-- The source small zero sample owner with its exact clearance and winding certificate. -/
@[expose] def sourceSampleZero :
  LocalOwner (Legendre.Paths.polynomial sourceParameter) :=
  ownerOf (Centered.sampleBox 0)
    (Centered.sampleBox_proper 0)
    (sourcePolynomialClearance
      (sampleZeroClearance sourceParameter
        source_above_sampleZero))
    sourceSampleZeroWinding

/-- The source small moving root sample owner with its exact clearance and winding certificate. -/
@[expose] def sourceSampleMoving :
  LocalOwner (Legendre.Paths.polynomial sourceParameter) :=
  ownerOf (Centered.sampleBox
    sourceParameter) (Centered.sampleBox_proper
    sourceParameter)
    (sourcePolynomialClearance
      (sampleMovingClearance sourceParameter
        source_imaginary_high))
    sourceSampleMovingWinding

/-- The source small one sample owner with its exact clearance and winding certificate. -/
@[expose] def sourceSampleOne : LocalOwner
  (Legendre.Paths.polynomial sourceParameter) :=
  ownerOf (Centered.sampleBox 1)
    (Centered.sampleBox_proper 1)
    (sourcePolynomialClearance
      (sampleOneClearance sourceParameter
        source_above_sampleOne))
    sourceSampleOneWinding

/-- The target small zero sample owner with its exact clearance and winding certificate. -/
@[expose] def targetSampleZero :
  LocalOwner (Legendre.Paths.polynomial targetParameter) :=
  ownerOf (Centered.sampleBox 0)
    (Centered.sampleBox_proper 0)
    (targetPolynomialClearance
      (sampleZeroClearance targetParameter
        target_above_sampleZero))
    targetSampleZeroWinding

/-- The target small moving root sample owner with its exact clearance and winding certificate. -/
@[expose] def targetSampleMoving :
  LocalOwner (Legendre.Paths.polynomial targetParameter) :=
  ownerOf (Centered.sampleBox
    targetParameter) (Centered.sampleBox_proper
    targetParameter)
    (targetPolynomialClearance
      (sampleMovingClearance targetParameter
        target_imaginary_high))
    targetSampleMovingWinding

/-- The target small one sample owner with its exact clearance and winding certificate. -/
@[expose] def targetSampleOne : LocalOwner
  (Legendre.Paths.polynomial targetParameter) :=
  ownerOf (Centered.sampleBox 1)
    (Centered.sampleBox_proper 1)
    (targetPolynomialClearance
      (sampleOneClearance targetParameter
        target_above_sampleOne))
    targetSampleOneWinding

/-- The source broad root owners in logical order: zero, moving root, one. -/
@[expose] def sourceOwner : Fin 3 ->
  LocalOwner (Legendre.Paths.polynomial sourceParameter) :=
  Data.Fin.cases (sourceZeroOwner)
    (fun rest => Data.Fin.cases (sourceMovingOwner)
      (fun _ => sourceOneOwner) rest)

/-- The target broad root owners in logical order: zero, moving root, one. -/
@[expose] def targetOwner : Fin 3 ->
  LocalOwner (Legendre.Paths.polynomial targetParameter) :=
  Data.Fin.cases (targetZeroOwner)
    (fun rest => Data.Fin.cases (targetMovingOwner)
      (fun _ => targetOneOwner) rest)

/-- Distinct source logical root indices have separated broad boxes. -/
theorem sourceOwner_pairwise : forall left right : Fin 3,
  left ≠ right ->
    (sourceOwner left).box.Separated
      (sourceOwner right).box := by
  intro left right different
  rcases Cases.three left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases Cases.three right with rightZero | rightOne | rightTwo <;>
    subst right <;>
    first | exact (different rfl).elim | decide

/-- Distinct target logical root indices have separated broad boxes. -/
theorem targetOwner_pairwise : forall left right : Fin 3,
  left ≠ right ->
    (targetOwner left).box.Separated
      (targetOwner right).box := by
  intro left right different
  rcases Cases.three left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases Cases.three right with rightZero | rightOne | rightTwo <;>
    subst right <;>
    first | exact (different rfl).elim | decide

/-- The retained three source root owners with their pairwise box separation. -/
@[expose] def sourceOwnerFamily :
    Owner.Family.Basic.OwnerFamily
      (Legendre.Paths.polynomial sourceParameter) 3 where
  owner := sourceOwner
  pairwiseSeparated := sourceOwner_pairwise

/-- The retained three target root owners with their pairwise box separation. -/
@[expose] def targetOwnerFamily :
    Owner.Family.Basic.OwnerFamily
      (Legendre.Paths.polynomial targetParameter) 3 where
  owner := targetOwner
  pairwiseSeparated := targetOwner_pairwise

/-- The explicit source cubic has a retained finite squarefreeness certificate. -/
@[expose] def sourceSquarefree :
  Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
    (Legendre.Coefficients.Exact.coefficientTable sourceParameter).polynomial := by
  rw [Legendre.Coefficients.Exact.coefficientTable_polynomial]
  exact Legendre.Squarefree.squarefreeAt sourceParameter
    (by decide)

/-- The explicit target cubic has a retained finite squarefreeness certificate. -/
@[expose] def targetSquarefree :
  Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
    (Legendre.Coefficients.Exact.coefficientTable targetParameter).polynomial := by
  rw [Legendre.Coefficients.Exact.coefficientTable_polynomial]
  exact Legendre.Squarefree.squarefreeAt targetParameter
    (by decide)

/-- The exact source cubic with its squarefreeness and degree-at-least-two certificates. -/
@[expose] def sourceIsolationInput :
    RootIsolation.FTA.Squarefree.Input (Legendre.Coefficients.Exact.coefficientTable
      sourceParameter).polynomial where
  squarefree := sourceSquarefree
  degreeAtLeastTwo := by decide

/-- The exact target cubic with its squarefreeness and degree-at-least-two certificates. -/
@[expose] def targetIsolationInput :
    RootIsolation.FTA.Squarefree.Input (Legendre.Coefficients.Exact.coefficientTable
      targetParameter).polynomial where
  squarefree := targetSquarefree
  degreeAtLeastTwo := by decide

/-- The exact source coefficient chamber retaining the three displayed broad root owners.

Coefficient allowances are zero, and finite root isolation supplies the degree-sharp maximality witness. -/
@[expose] def sourceChamber :
  Progressive.Chamber.Frame.ChamberFrame where
  reference := Legendre.Coefficients.Exact.coefficientTable sourceParameter
  chamber :=
    { degreeAtLeastTwo := by decide
      squarefree := sourceSquarefree
      owners := sourceOwnerFamily
      referenceSmall := Legendre.Coefficients.Exact.coefficientTable_allowances_lt
        sourceParameter
        (Progressive.Chamber.Target.simpleRootChamberTarget_pos
          (Legendre.Coefficients.Exact.coefficientTable sourceParameter)
            sourceSquarefree sourceOwnerFamily)
      referenceMaximality :=
        (Purelib.RootIsolation.FTA.Squarefree.Build.Box.prove
          sourceIsolationInput).boxes.maximality }

/-- The exact target coefficient chamber retaining the three displayed broad root owners.

Coefficient allowances are zero, and finite root isolation supplies the degree-sharp maximality witness. -/
@[expose] def targetChamber :
  Progressive.Chamber.Frame.ChamberFrame where
  reference := Legendre.Coefficients.Exact.coefficientTable targetParameter
  chamber :=
    { degreeAtLeastTwo := by decide
      squarefree := targetSquarefree
      owners := targetOwnerFamily
      referenceSmall := Legendre.Coefficients.Exact.coefficientTable_allowances_lt
        targetParameter
        (Progressive.Chamber.Target.simpleRootChamberTarget_pos
          (Legendre.Coefficients.Exact.coefficientTable targetParameter)
            targetSquarefree targetOwnerFamily)
      referenceMaximality :=
        (Purelib.RootIsolation.FTA.Squarefree.Build.Box.prove
          targetIsolationInput).boxes.maximality }

/-- The source chamber reads back the original Legendre polynomial. -/
@[simp] theorem sourceChamber_polynomial :
    sourceChamber.polynomial = Legendre.Paths.polynomial sourceParameter := rfl

/-- The target chamber reads back the original Legendre polynomial. -/
@[simp] theorem targetChamber_polynomial :
    targetChamber.polynomial = Legendre.Paths.polynomial targetParameter := rfl

/-- Each source chamber owner retains the corresponding displayed broad box. -/
@[simp] theorem sourceChamber_owner_box (index : Fin 3) :
    (sourceChamber.owner index).box =
      (sourceOwner index).box := rfl

/-- Each target chamber owner retains the corresponding displayed broad box. -/
@[simp] theorem targetChamber_owner_box (index : Fin 3) :
    (targetChamber.owner index).box =
      (targetOwner index).box := rfl

/-! ## Endpoint projection orders -/

/-- The source sample owners in projection order: zero, moving root, one. -/
@[expose] def sourceProjectionOwner : Fin 3 ->
  LocalOwner (Legendre.Paths.polynomial sourceParameter) :=
  Data.Fin.cases (sourceSampleZero)
    (fun rest => Data.Fin.cases (sourceSampleMoving)
      (fun _ => sourceSampleOne) rest)

/-- The target sample owners in projection order: moving root, zero, one. -/
@[expose] def targetProjectionOwner : Fin 3 ->
  LocalOwner (Legendre.Paths.polynomial targetParameter) :=
  Data.Fin.cases (targetSampleMoving)
    (fun rest => Data.Fin.cases (targetSampleZero)
      (fun _ => targetSampleOne) rest)

/-- Exchange the zero and moving-root labels while fixing the label of one. -/
@[expose] def targetProjectionOrder :
  Data.Fin.Bijection 3 3 where
  forward :=
    Data.Fin.cases (1)
      (fun rest => Data.Fin.cases (0) (fun _ => 2) rest)
  backward :=
    Data.Fin.cases (1)
      (fun rest => Data.Fin.cases (0) (fun _ => 2) rest)
  backward_forward := by
    intro position
    rcases Cases.three position with positionZero | positionOne |
      positionTwo <;> subst position <;> rfl
  forward_backward := by
    intro position
    rcases Cases.three position with positionZero | positionOne |
      positionTwo <;> subst position <;> rfl

/-- The source root frame retaining its exact chamber, logical labels and ordered sample boxes. -/
@[expose] def sourceFrame : Legendre.Paths.Frame
  sourceParameter where
  chamber := sourceChamber
  polynomial_eq := rfl
  labels := Data.Fin.Bijection.identity 3
  owner_contains := by
    intro label
    rcases Cases.three label with labelZero | labelOne | labelTwo <;>
      subst label <;> decide
  projectionOrder := Data.Fin.Bijection.identity 3
  projectionOwner := fun position =>
    Owner.Local.Transport.castOwner sourceChamber_polynomial.symm
      (sourceProjectionOwner position)
  projection_refines := by
    intro position
    change (sourceProjectionOwner position).box.Refines
      (sourceChamber.owner position).box
    rw [sourceChamber_owner_box]
    rcases Cases.three position with positionZero | positionOne |
      positionTwo <;> subst position <;>
      simp only [sourceProjectionOwner,
        sourceOwner, sourceSampleZero,
        sourceSampleMoving, sourceSampleOne,
          sourceZeroOwner,
        sourceMovingOwner, sourceOneOwner,
          ownerOf,
        Rational.Box.Refines] <;>
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

/-- The target root frame retaining its exact chamber, logical labels and ordered sample boxes. -/
@[expose] def targetFrame : Legendre.Paths.Frame
  targetParameter where
  chamber := targetChamber
  polynomial_eq := rfl
  labels := Data.Fin.Bijection.identity 3
  owner_contains := by
    intro label
    rcases Cases.three label with labelZero | labelOne | labelTwo <;>
      subst label <;> decide
  projectionOrder := targetProjectionOrder
  projectionOwner := fun position =>
    Owner.Local.Transport.castOwner targetChamber_polynomial.symm
      (targetProjectionOwner position)
  projection_refines := by
    intro position
    change (targetProjectionOwner position).box.Refines
      (targetChamber.owner
        (targetProjectionOrder.forward position)).box
    rw [targetChamber_owner_box]
    rcases Cases.three position with positionZero | positionOne |
      positionTwo <;> subst position <;>
      simp only [targetProjectionOwner,
        targetProjectionOrder, targetOwner,
        targetSampleZero, targetSampleMoving,
          targetSampleOne,
        targetZeroOwner, targetMovingOwner,
          targetOneOwner, ownerOf,
        Rational.Box.Refines] <;>
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

/-- At the source, projected positions agree with the persistent owner indices. -/
@[simp] theorem sourceFrame_projection_order (position : Fin
  3) :
    sourceFrame.projected.ownerIndex position = position := rfl

/-- The exact polynomial perturbation moving the source parameter to the target parameter. -/
@[expose] def perturbation : GaussianPolynomial :=
  Legendre.Polynomial.perturbationAt sourceParameter
    targetParameter

/-- The target Legendre polynomial equals the source polynomial plus the retained perturbation. -/
theorem target_eq_source_add_perturbation :
    Legendre.Paths.polynomial targetParameter =
      Legendre.Paths.polynomial sourceParameter + perturbation := by
  decide

/-- Evaluation of the source cubic equals the product of its three displayed linear factors. -/
theorem sourcePolynomial_eval_factors (point :
  Gaussian.Basic.Canonical) :
    (Legendre.Paths.polynomial sourceParameter).eval point =
      (Translated.translatedCoordinate 0).eval point *
        (Translated.translatedCoordinate
          sourceParameter).eval point *
        (Translated.translatedCoordinate 1).eval point := by
  exact Legendre.Polynomial.polynomial_eval_factorsAt sourceParameter point

/-- The perturbation evaluates to the zero and one factors times the parameter displacement. -/
theorem perturbation_eval (point : Gaussian.Basic.Canonical)
  :
    perturbation.eval point =
      (Translated.translatedCoordinate 0).eval point *
        (Translated.translatedCoordinate 1).eval point *
        (sourceParameter - targetParameter) :=
          by
  exact Legendre.Polynomial.perturbationAt_eval sourceParameter
    targetParameter point

/-- Certify strict boundary dominance for this fixed movement of the Legendre parameter.

The three original factor clearances are retained, and the squared parameter displacement must lie below the
moving-factor clearance. -/
@[expose] def factorMoveDominance {box :
  Rational.Box}
    (zeroClearance : BoundaryClearance
      (Translated.translatedCoordinate 0) box)
    (movingClearance : BoundaryClearance
      (Translated.translatedCoordinate
        sourceParameter) box)
    (oneClearance : BoundaryClearance
      (Translated.translatedCoordinate 1) box)
    (displacementSmall :
      Data.Gaussian.Norm.Basic.normSq
          (sourceParameter - targetParameter) <
            movingClearance.bound) :
    BoundaryNormDominance
      (Legendre.Paths.polynomial sourceParameter)
        perturbation box :=
  Legendre.Rouche.factorMoveDominanceAt sourceParameter
    targetParameter zeroClearance
    movingClearance oneClearance displacementSmall

/-- Retain the exact source-to-target perturbation and its strict boundary dominance as an oriented Rouché certificate.
-/
@[expose] def orientedRouche
    (owner : LocalOwner (Legendre.Paths.polynomial
      sourceParameter))
    (dominance : BoundaryNormDominance
      (Legendre.Paths.polynomial sourceParameter)
        perturbation owner.box) :
    Box.Rouche.Connection.OrientedRouche
      (Legendre.Paths.polynomial sourceParameter) (Legendre.Paths.polynomial
        targetParameter) owner.box where
  perturbation := perturbation
  target_eq_add := target_eq_source_add_perturbation
  dominance := dominance

/-- The parameter perturbation is strictly dominated on the retained broad zero box. -/
@[expose] def zeroDominance :
  BoundaryNormDominance
    (Legendre.Paths.polynomial sourceParameter)
      perturbation sourceZeroOwner.box :=
  factorMoveDominance
    (ExplicitLegendreSegment.centeredClearance 0 (by decide) (by decide) (by decide)
      (by decide))
    (ExplicitLegendreSegment.aboveClearance
      sourceParameter source_above_fixedZero)
    (ExplicitLegendreSegment.rightClearance 1 (by decide)) (by decide)

/-- The parameter perturbation is strictly dominated on the retained broad moving root box. -/
@[expose] def movingDominance :
  BoundaryNormDominance
    (Legendre.Paths.polynomial sourceParameter)
      perturbation sourceMovingOwner.box :=
  factorMoveDominance
    (ExplicitLegendreSegment.belowClearance 0 (by decide))
    (ExplicitLegendreSegment.centeredClearance
      sourceParameter source_in_movingBox.1
      source_in_movingBox.2.1
        source_in_movingBox.2.2.1
      source_in_movingBox.2.2.2)
    (ExplicitLegendreSegment.belowClearance 1 (by decide)) (by decide)

/-- The parameter perturbation is strictly dominated on the retained broad one box. -/
@[expose] def oneDominance :
  BoundaryNormDominance
    (Legendre.Paths.polynomial sourceParameter)
      perturbation sourceOneOwner.box :=
  factorMoveDominance
    (ExplicitLegendreSegment.leftClearance 0 (by decide))
    (ExplicitLegendreSegment.aboveClearance
      sourceParameter source_above_fixedOne)
    (ExplicitLegendreSegment.centeredClearance 1 (by decide) (by decide) (by decide)
      (by decide))
    (by decide)

/-- The forward Rouché bridge preserving the retained zero owner across the crossing. -/
@[expose] def zeroBridge : OwnerBridge
    (Legendre.Paths.polynomial sourceParameter) (Legendre.Paths.polynomial
      targetParameter) :=
  OwnerBridge.ofForward sourceZeroOwner
    (orientedRouche sourceZeroOwner
      zeroDominance)

/-- The forward Rouché bridge preserving the retained moving root owner across the crossing. -/
@[expose] def movingBridge : OwnerBridge
    (Legendre.Paths.polynomial sourceParameter) (Legendre.Paths.polynomial
      targetParameter) :=
  OwnerBridge.ofForward sourceMovingOwner
    (orientedRouche sourceMovingOwner
      movingDominance)

/-- The forward Rouché bridge preserving the retained one owner across the crossing. -/
@[expose] def oneBridge : OwnerBridge
    (Legendre.Paths.polynomial sourceParameter) (Legendre.Paths.polynomial
      targetParameter) :=
  OwnerBridge.ofForward sourceOneOwner
    (orientedRouche sourceOneOwner
      oneDominance)

/-- The three source-to-target root bridges in persistent logical order: zero, moving root, one. -/
@[expose] def bridgeAt : Fin 3 ->
  OwnerBridge
    (Legendre.Paths.polynomial sourceParameter) (Legendre.Paths.polynomial
      targetParameter) :=
  Data.Fin.cases (zeroBridge)
    (fun rest => Data.Fin.cases (movingBridge)
      (fun _ => oneBridge) rest)

/-- Match the two endpoint chambers by their identical persistent root labels and retained bridges. -/
@[expose] def chamberOverlap :
  Progressive.Chamber.Overlap.ChamberOverlap
    sourceChamber targetChamber where
  matching := Data.Fin.Bijection.identity 3
  bridge := bridgeAt
  bridge_refines_left := by
    intro index
    rcases Cases.three index with indexZero | indexOne | indexTwo <;>
      subst index <;>
      exact Rational.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rcases Cases.three index with indexZero | indexOne | indexTwo <;>
      subst index <;>
      exact Rational.Box.refines_refl _

/-- The zero-root owner lies strictly below the moving-root owner throughout their common crossing chart. -/
theorem crossingGeometry :
  Progressive.Braid.Projected.Overlap.CrossingGeometry
    sourceFrame.projected targetFrame.projected
      chamberOverlap
      Legendre.Conventions.lowerPositive where
  heightSeparated := by
    change (Centered.realAxisSquareSixteenth 0).yUpper <
      movingBox.yLower
    change (1 / 16 : Fraction.Rational) < 1
    decide

/-- The persistent moving root crosses the zero root positively: the zero
owner starts on the left and remains strictly below it in the common bridge
chart. -/
@[expose] def projectedOverlap :
  Progressive.Braid.Projected.Overlap.ProjectedOverlap
    sourceFrame.projected targetFrame.projected
      :=
  .crossing chamberOverlap Legendre.Conventions.lowerPositive
    crossingGeometry (by
      intro position
      change position = targetProjectionOrder.forward
        (Legendre.Conventions.lowerPositive.permutation.forward position)
      rcases Cases.three position with positionZero | positionOne |
        positionTwo <;> subst position <;> rfl)

/-- The projected overlap records exactly the positive lower crossing. -/
@[simp] theorem projectedOverlap_word :
  projectedOverlap.word =
    [Legendre.Conventions.lowerPositive] := rfl

/-- The minimum of all six endpoint clearance bounds of the three retained root bridges. -/
@[expose] def sheetBound : Fraction.Rational :=
  min zeroBridge.leftClearance.bound
    (min zeroBridge.rightClearance.bound
      (min movingBridge.leftClearance.bound
        (min movingBridge.rightClearance.bound
          (min oneBridge.leftClearance.bound
            oneBridge.rightClearance.bound))))

/-- The common sheet bound is positive because every retained bridge clearance is positive. -/
theorem sheetBound_positive : 0 < sheetBound := by
  unfold sheetBound
  exact Fraction.Order.Basic.lt_min zeroBridge.leftClearance.positive
    (Fraction.Order.Basic.lt_min zeroBridge.rightClearance.positive
      (Fraction.Order.Basic.lt_min movingBridge.leftClearance.positive
        (Fraction.Order.Basic.lt_min movingBridge.rightClearance.positive
          (Fraction.Order.Basic.lt_min oneBridge.leftClearance.positive
            oneBridge.rightClearance.positive))))

/-- Retain one positive lower bound for both endpoints of every persistent root bridge. -/
@[expose] def sheetClearance :
  Legendre.Paths.BridgeClearance sourceFrame
  targetFrame chamberOverlap where
  bound := sheetBound
  positive := sheetBound_positive
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

/-- The horizontal parameter segment from 1/4+2i to -1/4+2i. -/
@[expose] def geometry : Legendre.Paths.AxisSegment
  sourceParameter targetParameter :=
  .horizontal (1 / 4) (-(1 / 4)) 2

/-- The horizontal crossing segment retains positive clearance from both singular parameters zero and one. -/
@[expose] def geometrySafe : Legendre.Paths.AxisSegment.Safe
  geometry where
  avoidsZero :=
    { bound := 1
      positive := by decide
      lower := by decide }
  avoidsOne :=
    { bound := 1
      positive := by decide
      lower := by decide }

/-- The complete concrete pilot segment, including singularity avoidance,
the Rouché owner overlap, square-root clearance, and extracted crossing. -/
@[expose] def segment : Legendre.Paths.Segment
  sourceFrame targetFrame :=
  Legendre.Paths.Segment.ofProjectedOverlap geometry
    geometrySafe projectedOverlap
    sheetClearance

/-- The certified segment extracts exactly the positive lower crossing. -/
@[simp] theorem segment_crossings :
  segment.crossings =
    [Legendre.Conventions.lowerPositive] := rfl

/-- The one-segment path joining the retained source and target Legendre frames. -/
@[expose] def path : Legendre.Paths.Path
  sourceFrame targetFrame :=
  .cons segment (.nil targetFrame)

/-- The displayed crossing path has one segment. -/
@[simp] theorem path_stepCount :
  path.stepCount = 1 := rfl

/-- The displayed crossing path carries the single positive lower crossing word. -/
@[simp] theorem path_word :
  path.word =
    [Legendre.Conventions.lowerPositive] := rfl

/-- The same certified event controls both the extracted braid permutation
and the persistent chamber-owner transport. -/
theorem owner_transport_agrees (position : Fin 3) :
    path.ownerTransport.forward
      (sourceFrame.projected.ownerIndex position) =
      targetFrame.projected.ownerIndex
        (path.word.permutation.forward position) :=
  path.ownerTransport_agrees position

/-! ## Actual endpoint period programs -/

/-- Unconditional prepared standard periods on the source fibre. -/
@[expose] def sourceFibre : Legendre.Periods.Fibre.FibreData
  sourceFrame where
  periods :=
    Integration.PreparedRefinementPrograms.automaticStandardPeriodData
      (Legendre.Periods.Fibre.frameCurve sourceFrame)

/-- Unconditional prepared standard periods on the target fibre. -/
@[expose] def targetFibre : Legendre.Periods.Fibre.FibreData
  targetFrame where
  periods :=
    Integration.PreparedRefinementPrograms.automaticStandardPeriodData
      (Legendre.Periods.Fibre.frameCurve targetFrame)

/-- The concrete source-labelled homology basis continued to the actual
target fibre.  Its endpoint periods are defined from the target's certified
period programs and the dual of the extracted braid action. -/
@[expose] def endpointContinuation :
    Legendre.GaussManin.Endpoint.EndpointContinuation path where
  source := sourceFibre
  target := targetFibre

/-- The extracted positive lower half-twist acts on the endpoint period
column by the transpose matrix `[[1,0],[-1,1]]`. -/
theorem path_periodMatrix :
    Knot.Braid.ThreeStrand.Integral.Dual.periodMatrix path.word =
      SquareMatrix.Integral.Two.matrix₂ 1 0 (-1) 1 := by
  rw [path_word]
  rfl

/-- The continued endpoint periods equal the target raw period column acted on by [[1,0],[-1,1]]. -/
@[expose] def endpoint_periods_explicit :
    VectorEquivalent
      endpointContinuation.periods
      (Matrix.Operational.Integral.Action.matrixAction
        (SquareMatrix.Integral.Two.matrix₂ 1 0 (-1) 1)
        targetFibre.rawPeriods) := by
  rw [Legendre.GaussManin.Endpoint.EndpointContinuation.periods,
    path_periodMatrix]
  exact VectorEquivalent.refl _

end Purelib.Examples.Curves.Legendre.Crossings.UpperZero

end
