module

import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Restriction
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Separation
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
import Purelib.Curves.Legendre.Paths.AxisSegment.Window
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Gaussian.Coordinates.Rotation

/-! # Original projection clearances before and after retained collision parameters -/

namespace TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Restriction

open Purelib.Curves.Legendre.Paths
open Purelib.Data.Gaussian.Coordinates

/-- An original above-axis segment has two actual nonstationary projected events in its zero-slope chart. -/
def original : AxisSegment (gaussian (-1) 1) (gaussian 2 1) := .horizontal (-1) 2 1

/-- The original checker computes its exact zero event from the retained endpoint interval. -/
def zero : original.ProjectionCollision 0 0 :=
  AxisSegment.ProjectionCollision.ofContainedReading original 0 0 (by constructor <;> decide +kernel)

/-- The original checker computes its exact one event from the same original endpoint interval. -/
def one : original.ProjectionCollision 0 1 :=
  AxisSegment.ProjectionCollision.ofContainedReading original 0 1 (by constructor <;> decide +kernel)

/-- Both events retain the exact computed original affine parameters. -/
example : zero.val = 1 / 3 ∧ one.val = 2 / 3 := by constructor <;> decide +kernel

/-- A restriction wholly before the original zero event computes its projection clearance internally. -/
def before : (original.restrict 0 (1 / 6)).ProjectionClearance 0 0 :=
  zero.clearanceBefore 0 (1 / 6) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Reversed before-event cuts retain the same original geometric interval and computed positive gap. -/
def beforeReversed : (original.restrict (1 / 6) 0).ProjectionClearance 0 0 :=
  zero.clearanceBefore (1 / 6) 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Both orientations compute the same exact original half-unit projection gap. -/
example : before.gap = 1 / 2 ∧ beforeReversed.gap = 1 / 2 := by constructor <;> decide +kernel

/-- A restriction wholly after the original one event computes its projection clearance internally. -/
def after : (original.restrict (5 / 6) 1).ProjectionClearance 0 1 :=
  one.clearanceAfter (5 / 6) 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Reversed after-event cuts retain the same original geometric interval and computed positive gap. -/
def afterReversed : (original.restrict 1 (5 / 6)).ProjectionClearance 0 1 :=
  one.clearanceAfter 1 (5 / 6) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Both after-event orientations compute the same exact original half-unit projection gap. -/
example : after.gap = 1 / 2 ∧ afterReversed.gap = 1 / 2 := by constructor <;> decide +kernel

/-- A restriction between both actual events computes its original paired zero and one clearances. -/
def middle : (original.restrict (5 / 12) (7 / 12)).ProjectionSeparation 0 :=
  ⟨zero.clearanceAfter (5 / 12) (7 / 12) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    one.clearanceBefore (5 / 12) (7 / 12) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

/-- Both actual fixed-reading gaps of the middle restriction are the exact original quarter-unit clearances. -/
example : middle.1.gap = 1 / 4 ∧ middle.2.gap = 1 / 4 := by constructor <;> decide +kernel

/-- The same retained separated geometry gives projection clearance on an arbitrary unit restriction. -/
example {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (clearance : segment.ProjectionClearance slope reading) (source target parameter : Coordinate)
    (sourceInside : 0 ≤ source ∧ source ≤ 1) (targetInside : 0 ≤ target ∧ target ≤ 1)
    (parameterInside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (Rotation.rotate slope ((segment.restrict source target).pointAt parameter)).re ≠ reading :=
  (clearance.restrict source target sourceInside targetInside).misses _ parameterInside.1 parameterInside.2

/-- Reconstructing clearance from its own intrinsic avoidance retains the complete original certificate. -/
example {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (clearance : segment.ProjectionClearance slope reading) :
    AxisSegment.ProjectionClearance.ofAvoidance segment slope reading
        (fun parameter nonnegative atMostOne => clearance.misses parameter nonnegative atMostOne) = clearance := by
  apply Subtype.ext
  exact clearance.gap_eq.symm

/-- Both retained original separation clearances are constructed on a unit restriction without new chart evidence. -/
example {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : segment.ProjectionSeparation slope) (source target parameter : Coordinate)
    (sourceInside : 0 ≤ source ∧ source ≤ 1) (targetInside : 0 ≤ target ∧ target ≤ 1)
    (parameterInside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (Rotation.rotate slope ((segment.restrict source target).pointAt parameter)).re ≠ 0 ∧
      (Rotation.rotate slope ((segment.restrict source target).pointAt parameter)).re ≠ 1 :=
  ⟨(separation.restrict source target sourceInside targetInside).1.misses _ parameterInside.1 parameterInside.2,
    (separation.restrict source target sourceInside targetInside).2.misses _ parameterInside.1 parameterInside.2⟩

end TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Restriction
