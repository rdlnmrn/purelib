module

import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic

/-! # Computed original axis-segment projection events -/

namespace TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection

open Purelib.Curves.Legendre.Paths
open Purelib.Data.Gaussian.Coordinates

/-- Paid charts contain the same unit readings in their original projected endpoint intervals. -/
example {start finish : Gaussian} (segment : AxisSegment start finish) (first last reading : Coordinate)
    (startFirst : Projection.slopeCost start < first) (finishFirst : Projection.slopeCost finish < first)
    (startLast : Projection.slopeCost start < last) (finishLast : Projection.slopeCost finish < last)
    (nonnegative : 0 ≤ reading) (atMostOne : reading ≤ 1) :
    ((segment.projectionBounds first).Contains reading ↔ (segment.projectionBounds last).Contains reading) :=
  segment.projectionBounds_contains_iff_of_slopeCost first last reading
    startFirst finishFirst startLast finishLast nonnegative atMostOne

/-- Read the actual parameter retained by the computed collision outcome. -/
def computedParameter {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope reading : Coordinate) : Option Coordinate :=
  match segment.checkProjectionCollision slope reading with
  | .inl collision => some collision.val
  | .inr _ => none

/-- Read the same original positive endpoint gap retained by a computed absence outcome. -/
def computedGap {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope reading : Coordinate) : Option Coordinate :=
  match segment.checkProjectionCollision slope reading with
  | .inl _ => none
  | .inr clearance => some clearance.gap

/-- An original above-zero horizontal segment crosses the zero reading halfway through. -/
def aboveZero : AxisSegment (gaussian (1 / 8) 1) (gaussian (-1 / 8) 1) :=
  .horizontal (1 / 8) (-1 / 8) 1

/-- The exact checker computes the original collision parameter. -/
example : computedParameter aboveZero 0 0 = some (1 / 2) := by decide +kernel

/-- Reversing the original segment computes the same midpoint without an orientation certificate. -/
example : computedParameter aboveZero.reverse 0 0 = some (1 / 2) := by decide +kernel

/-- The same original segment misses the one reading throughout. -/
example : computedParameter aboveZero 0 1 = none := by decide +kernel

/-- The same computed absence retains the exact positive seven-eighths gap from reading one. -/
example : computedGap aboveZero 0 1 = some (7 / 8) := by decide +kernel

/-- The original actual zero crossing returns a collision rather than an absence gap. -/
example : computedGap aboveZero 0 0 = none := by decide +kernel

/-- An original vertical segment has a nonstationary real projection in a nonzero chart. -/
def vertical : AxisSegment (gaussian (-1 / 2) (-1)) (gaussian (-1 / 2) 1) :=
  .vertical (-1 / 2) (-1) 1

/-- The zero reading occurs at its computed parameter, while the one reading is excluded. -/
example : computedParameter vertical 1 0 = some (3 / 4) ∧
    computedParameter vertical 1 1 = none := by
  constructor <;> decide +kernel

/-- Reversal retains the actual complementary crossing parameter. -/
example : computedParameter vertical.reverse 1 0 = some (1 / 4) := by decide +kernel

/-- A longer original vertical segment has distinct computed collisions with zero and one. -/
example : computedParameter (AxisSegment.vertical (-1 / 2) (-1) 2) 1 0 = some (1 / 2) ∧
    computedParameter (AxisSegment.vertical (-1 / 2) (-1) 2) 1 1 = some (5 / 6) := by
  constructor <;> decide +kernel

/-- An endpoint projection tie is returned with its exact original zero parameter. -/
example : computedParameter (AxisSegment.horizontal 0 1 1) 0 0 = some 0 := by decide +kernel

/-- A stationary original segment at the prescribed reading retains parameter zero. -/
example : computedParameter (AxisSegment.horizontal 0 0 1) 0 0 = some 0 := by decide +kernel

/-- A stationary original segment away from the prescribed reading returns a proved miss. -/
example : computedParameter (AxisSegment.horizontal 2 2 1) 0 0 = none := by decide +kernel

/-- A zero-slope vertical projection is stationary even when the original segment moves. -/
example : computedParameter vertical 0 0 = none := by decide +kernel

/-- The original horizontal segment avoids the actual branch zero by its fixed nonzero height. -/
theorem aboveZero_avoids : aboveZero.Avoids (gaussian 0 0) := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (1 : Coordinate) ≠ 0) imaginary

/-- The original midpoint is a certified projected collision in the retained zero-slope chart. -/
def collision : aboveZero.ProjectionCollision 0 0 :=
  AxisSegment.ProjectionCollision.ofContainedReading aboveZero 0 0 (by constructor <;> decide)

/-- The named collision constructor retains the same computed original affine parameter. -/
example : collision.val = aboveZero.projectionParameter 0 0 :=
  AxisSegment.ProjectionCollision.ofContainedReading_parameter aboveZero 0 0 _

/-- Intrinsic branch avoidance proves nonzero actual signed height at the original collision. -/
example : (Rotation.rotate 0 (aboveZero.pointAt collision.val)).im + 0 * 0 ≠ 0 :=
  collision.relativeHeight_nonzero aboveZero_avoids

/-- Regular endpoint readings make the retained collision strictly interior. -/
example : 0 < collision.val ∧ collision.val < 1 :=
  collision.interior (by decide) (by decide)

/-- Any original parameter at the zero reading agrees with the computed affine parameter. -/
example (parameter : Coordinate) (hits : (Rotation.rotate 0 (aboveZero.pointAt parameter)).re = 0) :
    parameter = aboveZero.projectionParameter 0 0 :=
  aboveZero.projectionParameter_unique 0 0 (by constructor <;> decide) (by decide) parameter hits

/-- A nonzero chart preserves the actual vertical segment's nonstationarity. -/
example : (Rotation.rotate 1 (gaussian (-1 / 2) (-1))).re ≠
    (Rotation.rotate 1 (gaussian (-1 / 2) 1)).re :=
  vertical.projection_nonstationary 1 (by decide) (by decide)

/-- Every arbitrary original checker outcome certifies either an actual collision or absence on the whole segment. -/
example {start finish : Gaussian} (segment : AxisSegment start finish) (slope reading : Coordinate)
    (parameter : Coordinate) (nonnegative : 0 ≤ parameter) (atMostOne : parameter ≤ 1) :
    match segment.checkProjectionCollision slope reading with
    | .inl hit => (Rotation.rotate slope (segment.pointAt hit.val)).re = reading
    | .inr _ => (Rotation.rotate slope (segment.pointAt parameter)).re ≠ reading := by
  cases segment.checkProjectionCollision slope reading with
  | inl hit => exact hit.property.2.2
  | inr clearance => exact clearance.misses parameter nonnegative atMostOne

/-- The original affine velocity transports the complete difference of arbitrary projected readings. -/
example {start finish : Gaussian} (segment : AxisSegment start finish) (slope source target : Coordinate) :
    (Rotation.rotate slope (segment.pointAt target)).re - (Rotation.rotate slope (segment.pointAt source)).re =
      (target - source) * segment.projectionVelocity slope := segment.projectionDifference slope source target

/-- Positive original velocity preserves the parameter order forced by two actual projection readings. -/
example {start finish : Gaussian} (segment : AxisSegment start finish) (slope source target : Coordinate)
    (positive : 0 < segment.projectionVelocity slope)
    (ordered : (Rotation.rotate slope (segment.pointAt source)).re <
      (Rotation.rotate slope (segment.pointAt target)).re) : source < target :=
  segment.parameter_lt_of_projection_lt_of_velocity_pos slope source target positive ordered

/-- Negative original velocity reverses projection order while retaining the actual increasing parameter direction. -/
example {start finish : Gaussian} (segment : AxisSegment start finish) (slope source target : Coordinate)
    (negative : segment.projectionVelocity slope < 0)
    (ordered : (Rotation.rotate slope (segment.pointAt target)).re <
      (Rotation.rotate slope (segment.pointAt source)).re) : source < target :=
  segment.parameter_lt_of_projection_gt_of_velocity_neg slope source target negative ordered

end TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection
