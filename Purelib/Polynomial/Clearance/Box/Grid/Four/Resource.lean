module
import Purelib.Data.Rat.Fraction.Resource.Model
public import Purelib.Data.Rat.Interval.Candidates.Resource
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Resource
public import Purelib.Polynomial.Clearance.Box.Grid.Four.Elimination
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Elimination.Axis.Cuts
import Purelib.Polynomial.Elimination.Axis.Cuts.Resource

import Purelib.Polynomial.Clearance.Box.Grid.Four.Basic

/-!
# Coordinate magnitudes of four-child clearance grids

The selected axis cuts retain their coordinate bounds. Combining them with the original box endpoints bounds all four
actual child boxes in the same safe-cut envelope.
-/

namespace Purelib.Polynomial.Clearance.Box.Grid.Four.Resource

open Purelib
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Data.Rat

/-- All four children of the canonical safe-cut grid satisfy the computed coordinate-magnitude envelope.

The bound combines the original box-coordinate bound with the displayed eliminant degree and applies to the actual
retained child boxes. -/
public theorem clearFourGrid_children_within
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound bound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (box : Box) (proper : box.Proper) (boxWithin : Box.Resource.BoxWithin box bound) :
    let grid := Clearance.Box.Grid.Four.Elimination.buildClearFourGrid elimination box proper
    Box.Resource.BoxWithin grid.lowerLeft (Data.Rat.Interval.Candidates.Resource.safeCutMagnitudeEnvelope bound
      degreeBound) ∧
      Box.Resource.BoxWithin grid.upperLeft (Data.Rat.Interval.Candidates.Resource.safeCutMagnitudeEnvelope bound
        degreeBound) ∧
      Box.Resource.BoxWithin grid.lowerRight (Data.Rat.Interval.Candidates.Resource.safeCutMagnitudeEnvelope bound
        degreeBound) ∧
      Box.Resource.BoxWithin grid.upperRight (Data.Rat.Interval.Candidates.Resource.safeCutMagnitudeEnvelope bound
        degreeBound) := by
  let grid := Clearance.Box.Grid.Four.Elimination.buildClearFourGrid elimination box proper
  let outputBound := Data.Rat.Interval.Candidates.Resource.safeCutMagnitudeEnvelope bound degreeBound
  have oldBound : bound ≤ outputBound :=
    Data.Rat.Interval.Candidates.Resource.bound_le_safeCutMagnitudeEnvelope bound degreeBound
  have xCutBound : Fraction.Resource.Model.coordinateMagnitude grid.xCut ≤ outputBound := by
    change Fraction.Resource.Model.coordinateMagnitude
      (Elimination.Axis.Cuts.verticalSafeCoordinate elimination box proper) ≤ _
    exact Elimination.Axis.Cuts.Resource.verticalSafeCoordinate_magnitude_le elimination box proper boxWithin
  have yCutBound : Fraction.Resource.Model.coordinateMagnitude grid.yCut ≤ outputBound := by
    change Fraction.Resource.Model.coordinateMagnitude
      (Elimination.Axis.Cuts.horizontalSafeCoordinate elimination box proper) ≤ _
    exact Elimination.Axis.Cuts.Resource.horizontalSafeCoordinate_magnitude_le elimination box proper boxWithin
  have xLower := boxWithin.1.trans oldBound
  have xUpper := boxWithin.2.1.trans oldBound
  have yLower := boxWithin.2.2.1.trans oldBound
  have yUpper := boxWithin.2.2.2.trans oldBound
  change
    Box.Resource.BoxWithin
        ((box.verticalLeft grid.xCut grid.xInside).horizontalLower
          grid.yCut grid.yInside) outputBound ∧
      Box.Resource.BoxWithin
        ((box.verticalLeft grid.xCut grid.xInside).horizontalUpper
          grid.yCut grid.yInside) outputBound ∧
      Box.Resource.BoxWithin
        ((box.verticalRight grid.xCut grid.xInside).horizontalLower
          grid.yCut grid.yInside) outputBound ∧
      Box.Resource.BoxWithin
        ((box.verticalRight grid.xCut grid.xInside).horizontalUpper
          grid.yCut grid.yInside) outputBound
  exact ⟨⟨xLower, xCutBound, yLower, yCutBound⟩,
    ⟨xLower, xCutBound, yCutBound, yUpper⟩,
    ⟨xCutBound, xUpper, yLower, yCutBound⟩,
    ⟨xCutBound, xUpper, yCutBound, yUpper⟩⟩

end Purelib.Polynomial.Clearance.Box.Grid.Four.Resource
