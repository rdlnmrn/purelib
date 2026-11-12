module

import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Crossing
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Height
import Purelib.Curves.Legendre.Paths.Preparation
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Fin.Bijection.Transposition
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Tactic.Ring

/-! # Original generators computed from projected event direction and height -/

namespace TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Crossing

open Purelib.Curves.Legendre.Paths
open Purelib.Data.Fin.Bijection
open Purelib.Topology.Knot
open Purelib.Data.Gaussian.Coordinates
open Purelib.Data.Rat

/-- Actual collisions in positive charts retain the same complete original signed generator. -/
example {start finish : Gaussian} {segment : AxisSegment start finish} {first last reading : Coordinate}
    (left : segment.ProjectionCollision first reading) (right : segment.ProjectionCollision last reading)
    (firstPositive : 0 < first) (lastPositive : 0 < last) : left.generator = right.generator :=
  left.generator_eq_of_positive_slopes right firstPositive lastPositive

/-- The original vertical axis crosses the real interval between its same two nonsingular endpoints. -/
def acrossUnit : AxisSegment (gaussian (1 / 4) (-1)) (gaussian (1 / 4) 1) := .vertical (1 / 4) (-1) 1

/-- The actual zero event in chart two retains its original computed unit parameter. -/
def chartTwoZero : acrossUnit.ProjectionCollision 2 0 :=
  AxisSegment.ProjectionCollision.ofContainedReading acrossUnit 2 0 (by constructor <;> decide)

/-- The actual zero event in chart three retains its distinct original computed unit parameter. -/
def chartThreeZero : acrossUnit.ProjectionCollision 3 0 :=
  AxisSegment.ProjectionCollision.ofContainedReading acrossUnit 3 0 (by constructor <;> decide)

/-- Chart changes move the actual collision parameters while retaining the same complete signed generator. -/
example : chartTwoZero.val = 7 / 16 ∧ chartThreeZero.val = 11 / 24 ∧
    chartTwoZero.generator = chartThreeZero.generator := by
  refine ⟨by decide, by decide, ?_⟩
  exact chartTwoZero.generator_eq_of_positive_slopes chartThreeZero (by decide) (by decide)

/-- The original moving branch crosses zero right-to-left above the real axis. -/
def upperZero : AxisSegment (gaussian (1 / 8) 1) (gaussian (-1 / 8) 1) := .horizontal (1 / 8) (-1 / 8) 1

/-- The original positive-height zero event is computed from its actual projected interval. -/
def upperZeroEvent : upperZero.ProjectionCollision 0 0 :=
  AxisSegment.ProjectionCollision.ofContainedReading upperZero 0 0 (by constructor <;> decide)

/-- Right-to-left motion above zero computes the original positive lower generator. -/
example : upperZeroEvent.generator = ({ index := 0, sign := .positive } : Braid.Generator 3) := rfl

/-- Reversing the original motion above zero computes the original negative lower generator. -/
example : (AxisSegment.ProjectionCollision.ofContainedReading upperZero.reverse 0 0
    (by constructor <;> decide)).generator = ({ index := 0, sign := .negative } : Braid.Generator 3) := rfl

/-- The original moving branch crosses zero right-to-left below the real axis. -/
def lowerZero : AxisSegment (gaussian (1 / 8) (-1)) (gaussian (-1 / 8) (-1)) := .horizontal (1 / 8) (-1 / 8) (-1)

/-- Right-to-left motion below zero computes the original negative lower generator. -/
example : (AxisSegment.ProjectionCollision.ofContainedReading lowerZero 0 0
    (by constructor <;> decide)).generator = ({ index := 0, sign := .negative } : Braid.Generator 3) := rfl

/-- The original moving branch crosses one right-to-left above the real axis. -/
def upperOne : AxisSegment (gaussian (9 / 8) 1) (gaussian (7 / 8) 1) := .horizontal (9 / 8) (7 / 8) 1

/-- The original one event is computed from its actual projected endpoint interval. -/
def upperOneEvent : upperOne.ProjectionCollision 0 1 :=
  AxisSegment.ProjectionCollision.ofContainedReading upperOne 0 1 (by constructor <;> decide)

/-- Right-to-left motion above one computes the original positive upper generator. -/
example : upperOneEvent.generator = ({ index := 1, sign := .positive } : Braid.Generator 3) := rfl

/-- Reversing the original motion above one computes the original negative upper generator. -/
example : (AxisSegment.ProjectionCollision.ofContainedReading upperOne.reverse 0 1
    (by constructor <;> decide)).generator = ({ index := 1, sign := .negative } : Braid.Generator 3) := rfl

/-- Nonstationarity of the original affine projection follows from its actual event and regular start reading. -/
example : upperOne.projectionVelocity 0 ≠ 0 := upperOneEvent.projectionVelocity_ne_zero (by decide)

/-- Every original affine reading is positioned relative to the same retained event by its original velocity. -/
example (parameter : Coordinate) : (branchProjection (upperZero.pointAt parameter) 1 0).re =
    (parameter - upperZeroEvent.val) * upperZero.projectionVelocity 0 := by
  have relative := upperZeroEvent.relativeReading parameter
  rewrite [show (Rotation.rotate 0 (upperZero.pointAt parameter)).re - 0 =
    (Rotation.rotate 0 (upperZero.pointAt parameter)).re by ring1] at relative
  exact relative

/-- The all-input computed adjacent permutation agrees with the actual original endpoint logical branch orders. -/
example {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : segment.ProjectionCollision slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (avoids : segment.Avoids (gaussian reading 0)) (position : Fin 3) :
    let window := collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses
    (branchOrder (segment.pointAt window.parameters.lower) slope).forward position =
      (branchOrder (segment.pointAt window.parameters.upper) slope).forward
        (collision.generator.permutation.forward position) :=
  collision.crossingWindow_orders_permutation avoidsZero avoidsOne fixed startMisses finishMisses avoids position

end TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Crossing
