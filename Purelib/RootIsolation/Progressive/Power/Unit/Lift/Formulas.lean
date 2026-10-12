module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
public import Purelib.Polynomial.Winding.Polygon.Comparison
public import Purelib.Polynomial.Winding.Polygon.Phase
public import Purelib.Polynomial.Winding.Polygon.Product
import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Unit.Move.Budget
public import Purelib.RootIsolation.Power.Unit.Segment.Clearance
import Purelib.RootIsolation.Power.Unit.Segment.Homotopy
import Purelib.RootIsolation.Power.Unit.Segment.Product
import Purelib.RootIsolation.Progressive.Power.Unit.Frame
public import Purelib.RootIsolation.Progressive.Power.Unit.Lift.Vertices
import Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Geometry
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.Polynomial.Clearance.Pair.Basic (Certificate)
open Purelib.Polynomial.Winding.Polygon.Phase (ChainPhaseFormula)
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Data

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Progressive.Power.Unit.Lift.Formulas

open Purelib.Data.Gaussian

/-- The three rational lift edges of one small move, synchronized with one
parameter edge followed by two stationary target edges. -/
theorem unitMoveLiftHomotopy
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    Winding.Polygon.Comparison.ChainHomotopyFormula
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (degree.value - 1))
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
      (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftVertices sourceUnit targetUnit degree degreeAtLeastTwo small
        index)
      source (Progressive.Power.Unit.Lift.Vertices.unitMoveParameterVertices target) := by
  let sourceIndex := Progressive.Power.Unit.Rebase.Geometry.unitMoveSourceDegreeIndexFromFrame sourceUnit targetUnit
    degree degreeAtLeastTwo index
  let targetIndex := Progressive.Power.Unit.Rebase.Geometry.unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit
    degree degreeAtLeastTwo small index
  let bridgeAnchor := (Progressive.Power.Unit.Rebase.Geometry.unitMoveBridgeState sourceUnit targetUnit degree
    degreeAtLeastTwo small index).box.anchor
  let overlap := Progressive.Power.Unit.Rebase.Geometry.unitMoveOverlapPoint sourceUnit targetUnit degree
    degreeAtLeastTwo small index
  let targetAnchor := (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit)
    targetUnit degree degreeAtLeastTwo targetIndex).anchor
  change Winding.Polygon.Comparison.ChainHomotopyFormula _ _
    (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
    [bridgeAnchor, overlap, targetAnchor] source [target, target, target]
  exact .cons
    (Power.Unit.Segment.Homotopy.unitRobustSegmentHomotopy sourceUnit targetUnit degree degreeAtLeastTwo
      small sourceIndex
      (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase_inside_sourceRobustBox sourceUnit targetUnit degree
        degreeAtLeastTwo index)
      (Progressive.Power.Unit.Lift.Vertices.unitMoveBridgeAnchor_inside_sourceRobustBox sourceUnit targetUnit degree
        degreeAtLeastTwo small index))
    (.cons
      (Power.Unit.Segment.Homotopy.unitRobustSegmentConstantTargetHomotopy sourceUnit targetUnit degree
        degreeAtLeastTwo small sourceIndex
        (Progressive.Power.Unit.Lift.Vertices.unitMoveBridgeAnchor_inside_sourceRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index)
        (Progressive.Power.Unit.Lift.Vertices.unitMoveOverlapPoint_inside_sourceRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index))
      (.cons
        (Power.Unit.Segment.Homotopy.unitRobustSegmentConstantTargetHomotopy targetUnit targetUnit degree
          degreeAtLeastTwo (UnitMoveSmall.reflexive targetUnit degree
            degreeAtLeastTwo) targetIndex
          (Progressive.Power.Unit.Rebase.Geometry.unitMoveOverlapPoint_inside_targetRobustBox sourceUnit targetUnit
            degree degreeAtLeastTwo small index)
          (Progressive.Power.Unit.Lift.Vertices.unitMoveTargetAnchor_inside_targetRobustBox sourceUnit targetUnit
            degree degreeAtLeastTwo small index))
        (.nil targetAnchor target)))
end Purelib.RootIsolation.Progressive.Power.Unit.Lift.Formulas

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Progressive.Power.Unit.Lift.Formulas

open Purelib.Data.Gaussian

/-- The same three robust connector edges carry constructive modulo-four
phase formulas for the coordinate path itself. -/
def unitMoveLiftPhaseFormula
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    ChainPhaseFormula
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
      (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftVertices sourceUnit targetUnit degree degreeAtLeastTwo small
        index) := by
  let sourceIndex := Progressive.Power.Unit.Rebase.Geometry.unitMoveSourceDegreeIndexFromFrame sourceUnit targetUnit
    degree degreeAtLeastTwo index
  let targetIndex := Progressive.Power.Unit.Rebase.Geometry.unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit
    degree degreeAtLeastTwo small index
  let bridgeAnchor := (Progressive.Power.Unit.Rebase.Geometry.unitMoveBridgeState sourceUnit targetUnit degree
    degreeAtLeastTwo small index).box.anchor
  let overlap := Progressive.Power.Unit.Rebase.Geometry.unitMoveOverlapPoint sourceUnit targetUnit degree
    degreeAtLeastTwo small index
  let targetAnchor := (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit)
    targetUnit degree degreeAtLeastTwo targetIndex).anchor
  have firstCertificate : Certificate
      (Dense.Gaussian.Path.Components.pathReal Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
        (bridgeAnchor -
          Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index))
      (Dense.Gaussian.Path.Components.pathImag Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
        (bridgeAnchor -
          Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index))
      { lower := 0, upper := 1, valid := by decide } := by
    simpa only [show Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial =
        Dense.Gaussian.Power.Coordinate.coordinatePositivePower 0 from rfl] using
      Power.Unit.Segment.Clearance.unitRobustSegmentCoordinatePowerCertificate
        (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeAtLeastTwo
        sourceIndex
        (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase_inside_sourceRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo index)
        (Progressive.Power.Unit.Lift.Vertices.unitMoveBridgeAnchor_inside_sourceRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index) 0
  have secondCertificate : Certificate
      (Dense.Gaussian.Path.Components.pathReal Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        bridgeAnchor (overlap - bridgeAnchor))
      (Dense.Gaussian.Path.Components.pathImag Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        bridgeAnchor (overlap - bridgeAnchor))
      { lower := 0, upper := 1, valid := by decide } := by
    simpa only [show Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial =
        Dense.Gaussian.Power.Coordinate.coordinatePositivePower 0 from rfl] using
      Power.Unit.Segment.Clearance.unitRobustSegmentCoordinatePowerCertificate
        (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeAtLeastTwo
        sourceIndex
        (Progressive.Power.Unit.Lift.Vertices.unitMoveBridgeAnchor_inside_sourceRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index)
        (Progressive.Power.Unit.Lift.Vertices.unitMoveOverlapPoint_inside_sourceRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index) 0
  have thirdCertificate : Certificate
      (Dense.Gaussian.Path.Components.pathReal Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        overlap (targetAnchor - overlap))
      (Dense.Gaussian.Path.Components.pathImag Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        overlap (targetAnchor - overlap))
      { lower := 0, upper := 1, valid := by decide } := by
    simpa only [show Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial =
        Dense.Gaussian.Power.Coordinate.coordinatePositivePower 0 from rfl] using
      Power.Unit.Segment.Clearance.unitRobustSegmentCoordinatePowerCertificate
        (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeAtLeastTwo
        targetIndex
        (Progressive.Power.Unit.Rebase.Geometry.unitMoveOverlapPoint_inside_targetRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index)
        (Progressive.Power.Unit.Lift.Vertices.unitMoveTargetAnchor_inside_targetRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index) 0
  change ChainPhaseFormula
    Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
    (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
    [bridgeAnchor, overlap, targetAnchor]
  exact ChainPhaseFormula.consOfClearance firstCertificate
    (ChainPhaseFormula.consOfClearance secondCertificate
      (ChainPhaseFormula.consOfClearance thirdCertificate
        (ChainPhaseFormula.nil
          Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial targetAnchor)))
end Purelib.RootIsolation.Progressive.Power.Unit.Lift.Formulas

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Progressive.Power.Unit.Lift.Formulas

open Purelib.Data.Gaussian

/-- Combine the three original lifted-edge product formulas using the retained synchronized and constant-parameter
homotopies. -/
theorem unitMoveLiftProductFormula
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (Progressive.Power.Unit.Frame.robustChamberFrame (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one
      sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index)
    (exponent : Nat) :
    Winding.Polygon.Product.ChainProductFormula
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower exponent)
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
      (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftVertices sourceUnit targetUnit degree degreeAtLeastTwo small
        index) := by
  let sourceIndex := Progressive.Power.Unit.Rebase.Geometry.unitMoveSourceDegreeIndexFromFrame sourceUnit targetUnit
    degree degreeAtLeastTwo index
  let targetIndex := Progressive.Power.Unit.Rebase.Geometry.unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit
    degree degreeAtLeastTwo small index
  let bridgeAnchor := (Progressive.Power.Unit.Rebase.Geometry.unitMoveBridgeState sourceUnit targetUnit degree
    degreeAtLeastTwo small index).box.anchor
  let overlap := Progressive.Power.Unit.Rebase.Geometry.unitMoveOverlapPoint sourceUnit targetUnit degree
    degreeAtLeastTwo small index
  let targetAnchor := (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit)
    targetUnit degree degreeAtLeastTwo targetIndex).anchor
  change Winding.Polygon.Product.ChainProductFormula _ _
    (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
    [bridgeAnchor, overlap, targetAnchor]
  exact .cons
    (Power.Unit.Segment.Product.unitRobustSegmentProductFormula
      (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeAtLeastTwo
      sourceIndex
      (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase_inside_sourceRobustBox sourceUnit targetUnit degree
        degreeAtLeastTwo index)
      (Progressive.Power.Unit.Lift.Vertices.unitMoveBridgeAnchor_inside_sourceRobustBox sourceUnit targetUnit degree
        degreeAtLeastTwo small index) exponent)
    (.cons
      (Power.Unit.Segment.Product.unitRobustSegmentProductFormula
        (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeAtLeastTwo
        sourceIndex
        (Progressive.Power.Unit.Lift.Vertices.unitMoveBridgeAnchor_inside_sourceRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index)
        (Progressive.Power.Unit.Lift.Vertices.unitMoveOverlapPoint_inside_sourceRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index) exponent)
      (.cons
        (Power.Unit.Segment.Product.unitRobustSegmentProductFormula
          (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeAtLeastTwo
          targetIndex
          (Progressive.Power.Unit.Rebase.Geometry.unitMoveOverlapPoint_inside_targetRobustBox sourceUnit targetUnit
            degree degreeAtLeastTwo small index)
          (Progressive.Power.Unit.Lift.Vertices.unitMoveTargetAnchor_inside_targetRobustBox sourceUnit targetUnit
            degree degreeAtLeastTwo small index) exponent)
        (.nil targetAnchor)))
end Purelib.RootIsolation.Progressive.Power.Unit.Lift.Formulas

end
