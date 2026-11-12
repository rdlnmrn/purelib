module

public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Separation
public import Purelib.Curves.Legendre.Paths.AxisSegment.Window
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Rat.Interval.ConvexCombination
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Coordinates.Rotation

/-!
# Original projection clearances on retained axis restrictions

Unit restrictions consume whole-segment avoidance. Restrictions wholly
before or after an original affine collision instead consume its exact
unique parameter and the supplied cut bounds, in either orientation.
-/

public section

namespace Purelib.Curves.Legendre.Paths.AxisSegment

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Coordinates
open Purelib.Geometry.Rational
open Fraction.Order

namespace ProjectionClearance

/-- Derive the original projection clearance on a unit restriction from the retained whole-segment clearance.

The original affine restriction transports each unit parameter into the
same original unit interval. Its retained avoidance then computes the
new restriction's exact endpoint-interval gap, including reversed cuts.
-/
@[expose] def restrict {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (clearance : ProjectionClearance segment slope reading) (source target : Coordinate)
    (sourceInside : 0 ≤ source ∧ source ≤ 1) (targetInside : 0 ≤ target ∧ target ≤ 1) :
    ProjectionClearance (segment.restrict source target) slope reading :=
  ofAvoidance (segment.restrict source target) slope reading (by
    intro parameter nonnegative atMostOne
    have inside := Box.coordinate_between sourceInside targetInside ⟨nonnegative, atMostOne⟩
    rewrite [segment.restrict_pointAt]
    exact clearance.misses _ inside.1 inside.2)

end ProjectionClearance

namespace ProjectionSeparation

/-- Derive both original fixed-reading clearances on a restriction of the same retained separated segment. -/
@[expose] def restrict {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (source target : Coordinate)
    (sourceInside : 0 ≤ source ∧ source ≤ 1) (targetInside : 0 ≤ target ∧ target ≤ 1) :
    ProjectionSeparation (segment.restrict source target) slope :=
  ⟨separation.1.restrict source target sourceInside targetInside,
    separation.2.restrict source target sourceInside targetInside⟩

end ProjectionSeparation

namespace ProjectionCollision

/-- Derive original projection clearance on any restriction whose two parameters are strictly before the actual event.

Each restricted unit parameter lies between the same two cuts. A hit would
equal the original collision's unique affine parameter, contradicting its
proved strict upper bound. The cuts may have either orientation.
-/
@[expose] def clearanceBefore {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (source target : Coordinate) (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (sourceBefore : source < collision.val) (targetBefore : target < collision.val) :
    ProjectionClearance (segment.restrict source target) slope reading :=
  ProjectionClearance.ofAvoidance (segment.restrict source target) slope reading (by
    intro parameter nonnegative atMostOne hits
    have inside := Box.coordinate_between
      ⟨Basic.min_le_left source target, Basic.le_max_left source target⟩
      ⟨Basic.min_le_right source target, Basic.le_max_right source target⟩ ⟨nonnegative, atMostOne⟩
    have before := inside.2.trans_lt (Basic.max_lt sourceBefore targetBefore)
    rewrite [segment.restrict_pointAt] at hits
    exact before.ne (collision.parameter_eq startMisses _ hits))

/-- Derive original projection clearance on any restriction whose two parameters are strictly after the actual event.

Each restricted unit parameter lies between the same two cuts. A hit would
equal the original collision's unique affine parameter, contradicting its
proved strict lower bound. The cuts may have either orientation.
-/
@[expose] def clearanceAfter {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (source target : Coordinate) (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (sourceAfter : collision.val < source) (targetAfter : collision.val < target) :
    ProjectionClearance (segment.restrict source target) slope reading :=
  ProjectionClearance.ofAvoidance (segment.restrict source target) slope reading (by
    intro parameter nonnegative atMostOne hits
    have inside := Box.coordinate_between
      ⟨Basic.min_le_left source target, Basic.le_max_left source target⟩
      ⟨Basic.min_le_right source target, Basic.le_max_right source target⟩ ⟨nonnegative, atMostOne⟩
    have after := (Basic.lt_min sourceAfter targetAfter).trans_le inside.1
    rewrite [segment.restrict_pointAt] at hits
    exact after.ne' (collision.parameter_eq startMisses _ hits))

end ProjectionCollision

end Purelib.Curves.Legendre.Paths.AxisSegment
