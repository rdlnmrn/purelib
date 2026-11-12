module

public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
public import Purelib.Curves.Legendre.Paths.Preparation
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Uniform projection gaps on original crossing-free segments

The original two projection-clearance outcomes retain their exact positive
endpoint gaps. Their same unit-capped minimum pays the actual adjacent
branch projection gap at every original parameter in the unit interval.
-/

public section

namespace Purelib.Curves.Legendre.Paths.AxisSegment

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Coordinates
open Fraction.Order

/-- The original positive endpoint projection clearances at the fixed zero and one readings in one retained chart. -/
abbrev ProjectionSeparation {start finish : Gaussian} (segment : AxisSegment start finish) (slope : Coordinate) :=
  ProjectionClearance segment slope 0 × ProjectionClearance segment slope 1

namespace ProjectionSeparation

/-- Compute both original projection clearances from exact unit-interval avoidance of the fixed readings.

The two finite endpoint-interval gaps are derived internally. Their original
segment and chart are retained, with no supplied quantitative clearance or
successful subdivision result.
-/
@[expose] def ofAvoidance {start finish : Gaussian} (segment : AxisSegment start finish) (slope : Coordinate)
    (missesZero : ∀ parameter : Coordinate, 0 ≤ parameter → parameter ≤ 1 →
      (Rotation.rotate slope (segment.pointAt parameter)).re ≠ 0)
    (missesOne : ∀ parameter : Coordinate, 0 ≤ parameter → parameter ≤ 1 →
      (Rotation.rotate slope (segment.pointAt parameter)).re ≠ 1) : ProjectionSeparation segment slope :=
  ⟨ProjectionClearance.ofAvoidance segment slope 0 missesZero,
    ProjectionClearance.ofAvoidance segment slope 1 missesOne⟩

/-- Compute the original unit-capped minimum of both retained fixed-reading projection gaps. -/
@[expose] def gap {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) : Coordinate :=
  min 1 (min separation.1.gap separation.2.gap)

/-- The same computed minimum of the original positive projection gaps is strictly positive. -/
theorem positive {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) : 0 < separation.gap :=
  Basic.lt_min (by decide) (Basic.lt_min separation.1.positive separation.2.positive)

/-- Every original unit parameter retains separation of its actual branch readings in this same original chart. -/
theorem separates {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (parameter : Coordinate)
    (nonnegative : 0 ≤ parameter) (atMostOne : parameter ≤ 1) :
    (segment.pointAt parameter).re + slope * (segment.pointAt parameter).im ≠ 0 ∧
      (segment.pointAt parameter).re + slope * (segment.pointAt parameter).im ≠ 1 := by
  have zero := separation.1.misses parameter nonnegative atMostOne
  have one := separation.2.misses parameter nonnegative atMostOne
  rewrite [Rotation.rotate_real] at zero one
  exact ⟨zero, one⟩

/-- The original cached projection-gap minimum pays the actual adjacent branch gap at every unit parameter.

The same two endpoint-interval clearances pay both fixed-reading
displacements. The original order's three scalar cases transport these
bounds and the unit cap to the actual adjacent-gap minimum. -/
theorem pays {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (parameter : Coordinate)
    (nonnegative : 0 ≤ parameter) (atMostOne : parameter ≤ 1) :
    separation.gap ≤ branchProjectionGap (segment.pointAt parameter) slope := by
  have zero := separation.1.pays parameter nonnegative atMostOne
  have one := separation.2.pays parameter nonnegative atMostOne
  rewrite [show (Rotation.rotate slope (segment.pointAt parameter)).re - 0 =
    (Rotation.rotate slope (segment.pointAt parameter)).re by ring1] at zero
  apply branchProjectionGap_lower_bound _ _ _ (Basic.min_le_left _ _)
  · rewrite [branchProjection, branchPoint_one]
    exact ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _)).trans zero
  · rewrite [branchProjection, branchPoint_one]
    exact ((Basic.min_le_right _ _).trans (Basic.min_le_right _ _)).trans one

/-- The original zero-reading projection clearance excludes the physical zero branch throughout the segment. -/
theorem avoidsZero {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) : segment.Avoids 0 := by
  intro parameter nonnegative atMostOne same
  have excluded := separation.1.misses parameter nonnegative atMostOne
  apply excluded
  rewrite [same, Rotation.rotate_real]
  change 0 + slope * 0 = 0
  ring1

/-- The original one-reading projection clearance excludes the physical one branch throughout the segment. -/
theorem avoidsOne {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) : segment.Avoids 1 := by
  intro parameter nonnegative atMostOne same
  have excluded := separation.2.misses parameter nonnegative atMostOne
  apply excluded
  rewrite [same, Rotation.rotate_real]
  change 1 + slope * 0 = 1
  ring1

end ProjectionSeparation

/-- Compute an actual fixed-reading projection collision or both original positive whole-segment projection gaps.

Each original collision check is run at most once. A collision retains
its exact original parameter and reading; otherwise the same two computed
clearances supply a uniform positive branch-gap floor on the whole segment. -/
@[expose] def checkProjectionSeparation {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope : Coordinate) :
    (ProjectionCollision segment slope 0 ⊕ ProjectionCollision segment slope 1) ⊕
      ProjectionSeparation segment slope :=
  match segment.checkProjectionCollision slope 0 with
  | .inl collision => .inl (.inl collision)
  | .inr zero =>
    match segment.checkProjectionCollision slope 1 with
    | .inl collision => .inl (.inr collision)
    | .inr one => .inr (zero, one)

end Purelib.Curves.Legendre.Paths.AxisSegment
