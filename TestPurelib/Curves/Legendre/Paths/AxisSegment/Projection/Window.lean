module

import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Curves.Legendre.Paths.Frame.Gaps
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Interval.Basic

/-! # Root-derived original owner windows without supplied clearances -/

namespace TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Window

open Purelib.Curves.Legendre.Paths
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Coordinates

/-- The original moving root crosses the zero reading at height one. -/
def segment : AxisSegment (gaussian (1 / 8) 1) (gaussian (-1 / 8) 1) :=
  .horizontal (1 / 8) (-1 / 8) 1

/-- The original whole segment intrinsically avoids zero. -/
theorem avoidsZero : segment.Avoids 0 := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (1 : Coordinate) ≠ 0) imaginary

/-- The original whole segment intrinsically avoids one. -/
theorem avoidsOne : segment.Avoids 1 := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (1 : Coordinate) ≠ 0) imaginary

/-- The original projected event is computed from the retained endpoint interval. -/
def collision : segment.ProjectionCollision 0 0 :=
  AxisSegment.ProjectionCollision.ofContainedReading segment 0 0 (by constructor <;> decide)

/-- Prepare the original frame, side cache, radius and window from the computed event and intrinsic avoidance. -/
def window : AxisSegment.ProjectionCollision.OwnerWindow collision :=
  collision.prepareOwnerWindow avoidsZero avoidsOne

/-- The retained original frame has the same actual collision parameter as its polynomial index. -/
example : window.frame = Frame.ofParameter (segment.pointAt collision.val)
    (avoidsZero collision.val collision.property.1 collision.property.2.1)
    (avoidsOne collision.val collision.property.1 collision.property.2.1) :=
  collision.prepareOwnerWindow_frame avoidsZero avoidsOne

/-- The original prepared frame contains its moving branch strictly inside the same retained owner. -/
example : (window.frame.chamber.owner (window.frame.labels.forward 1)).box.StrictContains
    (branchPoint (segment.pointAt collision.val) 1) := window.frame.rootStrictContains 1

/-- The retained side vector is the actual materialized original anchor-frame vector. -/
example : window.sides = window.frame.movingSides := collision.prepareOwnerWindow_sides avoidsZero avoidsOne

/-- The radius is computed from the actual original root gap and the same retained outside-side gaps. -/
example : window.radius = 1 / 28 := by decide +kernel

/-- The actual parameter window uses that root-derived allowance rather than a caller's numerical bound. -/
example : window.parameters.lower = 831 / 1666 ∧ window.parameters.upper = 835 / 1666 := by
  constructor <;> decide +kernel

/-- The computed interval contains its actual original projected event. -/
example : window.parameters.Contains collision.val := window.contains_collision

/-- The computed original collision is strictly between the same retained parameter endpoints. -/
example : window.parameters.lower < collision.val ∧ collision.val < window.parameters.upper :=
  collision.prepareOwnerWindow_anchor_interior avoidsZero avoidsOne (by constructor <;> decide +kernel)

/-- Both actual original window endpoints internally miss the event's retained zero reading. -/
example : (Rotation.rotate 0 (segment.pointAt window.parameters.lower)).re ≠ 0 ∧
    (Rotation.rotate 0 (segment.pointAt window.parameters.upper)).re ≠ 0 :=
  collision.prepareOwnerWindow_endpoints_miss avoidsZero avoidsOne (by decide) (by decide)

/-- Every original point in the retained window pays the same stored radius squared. -/
example (parameter : Coordinate) (inside : window.parameters.Contains parameter) :
    Norm.Basic.normSq (segment.pointAt parameter - segment.pointAt collision.val) < window.radius ^ 2 :=
  window.normSq_lt parameter inside

/-- The stored radius retains its exact original defining equality for the same frame and side data. -/
example : window.radius = window.frame.displacementRadius window.sides := window.radius_eq

/-- The public producer pays the whole-window bound for any intrinsically admissible original segment and event. -/
example {start finish : Gaussian} {original : AxisSegment start finish} {slope reading : Coordinate}
    (event : original.ProjectionCollision slope reading)
    (excludesZero : original.Avoids 0) (excludesOne : original.Avoids 1)
    (parameter : Coordinate)
    (inside : (event.prepareOwnerWindow excludesZero excludesOne).parameters.Contains parameter) :
    Norm.Basic.normSq (original.pointAt parameter - original.pointAt event.val) <
      (event.prepareOwnerWindow excludesZero excludesOne).radius ^ 2 :=
  (event.prepareOwnerWindow excludesZero excludesOne
   ).normSq_lt parameter inside

end TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Window
