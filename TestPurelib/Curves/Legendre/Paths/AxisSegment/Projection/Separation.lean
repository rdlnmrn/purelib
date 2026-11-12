module

import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Separation
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Stationary
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
import Purelib.Curves.Legendre.Paths

/-! # Uniform endpoint-derived projection gaps and finite subdivision budgets -/

namespace TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Separation

open Purelib.Curves.Legendre.Paths

/-- The original horizontal parameter stays in the middle projection chamber. -/
def original : AxisSegment (gaussian (1 / 4) 1) (gaussian (3 / 4) 1) := .horizontal (1 / 4) (3 / 4) 1

/-- Both original fixed readings have endpoint-derived positive gaps in the same zero-slope chart. -/
def separation : original.ProjectionSeparation 0 :=
  ⟨AxisSegment.ProjectionClearance.ofNotContained original 0 0 (by decide +kernel),
    AxisSegment.ProjectionClearance.ofNotContained original 0 1 (by decide +kernel)⟩

/-- Read the actual original positive gap floor from a successful whole-segment separation check. -/
def computedGap {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope : Coordinate) : Option Coordinate :=
  match segment.checkProjectionSeparation slope with
  | .inl _ => none
  | .inr prepared => some prepared.gap

/-- The checker computes the same quarter floor from the original two projected endpoints. -/
example : computedGap original 0 = some (1 / 4) := by decide +kernel

/-- Reversing the original motion retains the same computed whole-segment gap floor. -/
example : computedGap original.reverse 0 = some (1 / 4) := by decide +kernel

/-- A constant-projection original vertical segment also computes a positive floor. -/
example : computedGap (AxisSegment.vertical (1 / 2) (-1) 1) 0 = some (1 / 2) := by decide +kernel

/-- An actual zero reading collision returns its typed collision outcome instead of a separation floor. -/
example : computedGap (AxisSegment.horizontal (-1 / 8) (1 / 8) 1) 0 = none := by decide +kernel

/-- A one reading collision is also returned when the original zero check had a positive clearance. -/
example : computedGap (AxisSegment.horizontal (3 / 4) (5 / 4) 1) 0 = none := by decide +kernel

/-- The original computed uniform adjacent projection-gap floor is one quarter. -/
example : separation.gap = 1 / 4 := by decide +kernel

/-- Every original unit parameter's actual adjacent branch gap pays that same retained floor. -/
example (parameter : Coordinate) (bounds : 0 ≤ parameter ∧ parameter ≤ 1) :
    separation.gap ≤ branchProjectionGap (original.pointAt parameter) 0 :=
  separation.pays parameter bounds.1 bounds.2

/-- The original retained chart and gap compute a uniform displacement-radius floor one forty-eighth. -/
example : separation.radiusFloor.val = 1 / 48 := by decide +kernel

/-- The actual original velocity turns that same radius floor into parameter allocation one over 2880. -/
example : separation.parameterAllocation.val = 1 / 2880 := by decide +kernel

/-- The exact existing grid procedure computes a finite count with half-mesh below that same allocation. -/
example : separation.subdivisionCount = 1441 := by decide +kernel

/-- The computed original count retains its all-input positive-count certificate. -/
example : 0 < separation.subdivisionCount := separation.subdivisionCount_positive

/-- The computed finite half-mesh pays the same cached original parameter allocation. -/
example : (1 / 2 : Coordinate) / (separation.subdivisionCount : Coordinate) < separation.parameterAllocation.val :=
  separation.halfMesh_lt_allocation

/-- Every actual original anchor window retains a radius paying the same uniform floor. -/
example (parameter : Coordinate) (bounds : 0 ≤ parameter ∧ parameter ≤ 1) :
    separation.radiusFloor.val ≤ (separation.windowAt parameter bounds).radius :=
  separation.radiusFloor_le_windowAt parameter bounds

end TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Separation
