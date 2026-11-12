module

import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Complement
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Crossing
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Cover
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
import Purelib.Curves.Legendre.Paths.AxisSegment.Window
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Paths.Path
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Tactic.QuotientFreeOmega

/-! # Original crossing packets and their automatically cleared complementary intervals -/

namespace TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Complement

open Purelib.Curves.Legendre.Paths
open AxisSegment.ProjectionCollision
open Purelib.Data.Gaussian.Coordinates

/-- Both projection directions retain the complete original zero and one crossing packets in their actual order. -/
example {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (zero : segment.ProjectionCollision slope 0) (one : segment.ProjectionCollision slope 1)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1) :
    match zero.prepareCrossingComplements one avoidsZero avoidsOne startZero finishZero startOne finishOne with
    | .inl packet =>
        packet.1 = zero.prepareCrossingOverlap avoidsZero avoidsOne (Or.inl rfl) startZero finishZero ∧
          packet.2.1 = one.prepareCrossingOverlap avoidsZero avoidsOne (Or.inr rfl) startOne finishOne
    | .inr packet =>
        packet.1 = one.prepareCrossingOverlap avoidsZero avoidsOne (Or.inr rfl) startOne finishOne ∧
          packet.2.1 = zero.prepareCrossingOverlap avoidsZero avoidsOne (Or.inl rfl) startZero finishZero :=
  zero.prepareCrossingComplements_crossings one avoidsZero avoidsOne startZero finishZero startOne finishOne

/-- Every actual complementary restriction misses both readings at every original unit parameter. -/
example {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope firstReading lastReading : Coordinate}
    {firstCollision : segment.ProjectionCollision slope firstReading}
    {lastCollision : segment.ProjectionCollision slope lastReading}
    {first : OwnerWindow firstCollision} {last : OwnerWindow lastCollision}
    (separations : OwnerWindow.ComplementSeparations first last)
    (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    ((segment.restrict 0 first.parameters.lower).pointAt parameter).re +
        slope * ((segment.restrict 0 first.parameters.lower).pointAt parameter).im ≠ 0 ∧
      ((segment.restrict 0 first.parameters.lower).pointAt parameter).re +
        slope * ((segment.restrict 0 first.parameters.lower).pointAt parameter).im ≠ 1 :=
  separations.1.separates parameter inside.1 inside.2

/-- The actual middle restriction is separated throughout its own unit parametrization. -/
example {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope firstReading lastReading : Coordinate}
    {firstCollision : segment.ProjectionCollision slope firstReading}
    {lastCollision : segment.ProjectionCollision slope lastReading}
    {first : OwnerWindow firstCollision} {last : OwnerWindow lastCollision}
    (separations : OwnerWindow.ComplementSeparations first last)
    (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    ((segment.restrict first.parameters.upper last.parameters.lower).pointAt parameter).re +
        slope * ((segment.restrict first.parameters.upper last.parameters.lower).pointAt parameter).im ≠ 0 ∧
      ((segment.restrict first.parameters.upper last.parameters.lower).pointAt parameter).re +
        slope * ((segment.restrict first.parameters.upper last.parameters.lower).pointAt parameter).im ≠ 1 :=
  separations.2.1.separates parameter inside.1 inside.2

/-- The actual suffix restriction is separated throughout its own unit parametrization. -/
example {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope firstReading lastReading : Coordinate}
    {firstCollision : segment.ProjectionCollision slope firstReading}
    {lastCollision : segment.ProjectionCollision slope lastReading}
    {first : OwnerWindow firstCollision} {last : OwnerWindow lastCollision}
    (separations : OwnerWindow.ComplementSeparations first last)
    (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    ((segment.restrict last.parameters.upper 1).pointAt parameter).re +
        slope * ((segment.restrict last.parameters.upper 1).pointAt parameter).im ≠ 0 ∧
      ((segment.restrict last.parameters.upper 1).pointAt parameter).re +
        slope * ((segment.restrict last.parameters.upper 1).pointAt parameter).im ≠ 1 :=
  separations.2.2.separates parameter inside.1 inside.2

/-- The prefix path retains the complete original fold of its actual stored caches. -/
example {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope firstReading lastReading : Coordinate}
    {firstCollision : segment.ProjectionCollision slope firstReading}
    {lastCollision : segment.ProjectionCollision slope lastReading}
    {first : OwnerWindow firstCollision} {last : OwnerWindow lastCollision}
    (separations : OwnerWindow.ComplementSeparations first last) :
    let prepared := separations.preparePaths
    prepared.1.2.path = separations.1.subdivisionEndpointPath prepared.1.1
      prepared.1.2.midpoints prepared.1.2.samples prepared.1.2.bridges prepared.1.2.pieces prepared.1.2.joins :=
  (separations.preparePaths).1.2.path_eq

/-- The middle path retains the complete original fold of its independent actual caches. -/
example {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope firstReading lastReading : Coordinate}
    {firstCollision : segment.ProjectionCollision slope firstReading}
    {lastCollision : segment.ProjectionCollision slope lastReading}
    {first : OwnerWindow firstCollision} {last : OwnerWindow lastCollision}
    (separations : OwnerWindow.ComplementSeparations first last) :
    let prepared := separations.preparePaths
    prepared.2.1.2.path = separations.2.1.subdivisionEndpointPath prepared.2.1.1
      prepared.2.1.2.midpoints prepared.2.1.2.samples prepared.2.1.2.bridges
        prepared.2.1.2.pieces prepared.2.1.2.joins :=
  (separations.preparePaths).2.1.2.path_eq

/-- The suffix path retains the complete original fold of its independent actual caches. -/
example {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope firstReading lastReading : Coordinate}
    {firstCollision : segment.ProjectionCollision slope firstReading}
    {lastCollision : segment.ProjectionCollision slope lastReading}
    {first : OwnerWindow firstCollision} {last : OwnerWindow lastCollision}
    (separations : OwnerWindow.ComplementSeparations first last) :
    let prepared := separations.preparePaths
    prepared.2.2.2.path = separations.2.2.subdivisionEndpointPath prepared.2.2.1
      prepared.2.2.2.midpoints prepared.2.2.2.samples prepared.2.2.2.bridges
        prepared.2.2.2.pieces prepared.2.2.2.joins :=
  (separations.preparePaths).2.2.2.path_eq

/-- The automatically cut prefix excludes both actual fixed readings for every restricted unit parameter. -/
example {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : segment.ProjectionCollision slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (other : segment.ProjectionClearance slope (1 - reading))
    (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    let prepared := collision.prepareSingleCrossingComplements avoidsZero avoidsOne fixed startMisses finishMisses other
    ((segment.restrict 0 prepared.1.samples.1.parameters.lower).pointAt parameter).re +
        slope * ((segment.restrict 0 prepared.1.samples.1.parameters.lower).pointAt parameter).im ≠ 0 ∧
      ((segment.restrict 0 prepared.1.samples.1.parameters.lower).pointAt parameter).re +
        slope * ((segment.restrict 0 prepared.1.samples.1.parameters.lower).pointAt parameter).im ≠ 1 :=
  (collision.prepareSingleCrossingComplements avoidsZero avoidsOne fixed startMisses finishMisses other).2.1.separates
    parameter inside.1 inside.2

/-- The automatically cut suffix excludes both actual fixed readings for every restricted unit parameter. -/
example {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : segment.ProjectionCollision slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (other : segment.ProjectionClearance slope (1 - reading))
    (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    let prepared := collision.prepareSingleCrossingComplements avoidsZero avoidsOne fixed startMisses finishMisses other
    ((segment.restrict prepared.1.samples.1.parameters.upper 1).pointAt parameter).re +
        slope * ((segment.restrict prepared.1.samples.1.parameters.upper 1).pointAt parameter).im ≠ 0 ∧
      ((segment.restrict prepared.1.samples.1.parameters.upper 1).pointAt parameter).re +
        slope * ((segment.restrict prepared.1.samples.1.parameters.upper 1).pointAt parameter).im ≠ 1 :=
  (collision.prepareSingleCrossingComplements avoidsZero avoidsOne fixed startMisses finishMisses other).2.2.separates
    parameter inside.1 inside.2


section Joins

variable {start finish : Gaussian} {original : AxisSegment start finish} {slope reading : Coordinate}
    {collision : original.ProjectionCollision slope reading} (crossing : PreparedWindow collision)
    {source target : Gaussian}
    {beforeSegment : AxisSegment source (original.pointAt crossing.samples.1.parameters.lower)}
    {afterSegment : AxisSegment (original.pointAt crossing.samples.1.parameters.upper) target}
    {beforeSeparation : beforeSegment.ProjectionSeparation slope} {beforeWindows : beforeSeparation.SubdivisionWindows}
    {afterSeparation : afterSegment.ProjectionSeparation slope} {afterWindows : afterSeparation.SubdivisionWindows}
    (before : beforeSeparation.PreparedSubdivision beforeWindows)
    (after : afterSeparation.PreparedSubdivision afterWindows)

/-- The actual prefix/crossing join retains the complete original constant axis restriction. -/
example : (crossing.joinSource before).geometry =
    original.restrict crossing.samples.1.parameters.lower crossing.samples.1.parameters.lower :=
  crossing.joinSource_geometry before

/-- Every parameter of the actual source join has the same original crossing endpoint. -/
example (parameter : Coordinate) : (crossing.joinSource before).geometry.pointAt parameter =
    original.pointAt crossing.samples.1.parameters.lower := crossing.joinSource_pointAt before parameter

/-- The actual source join retains the complete original comparison between the two cached endpoint owners. -/
example : (crossing.joinSource before).projection.chamberOverlap =
    (before.targetFrame.prepareOverlap crossing.sourceFrame).overlap := crossing.joinSource_overlap before

/-- The original source join adds no crossing event. -/
example : (crossing.joinSource before).projection.event = .stationary := crossing.joinSource_event before

/-- The actual crossing/suffix join retains the complete original constant axis restriction. -/
example : (crossing.joinTarget after).geometry =
    original.restrict crossing.samples.1.parameters.upper crossing.samples.1.parameters.upper :=
  crossing.joinTarget_geometry after

/-- Every parameter of the actual target join has the same original crossing endpoint. -/
example (parameter : Coordinate) : (crossing.joinTarget after).geometry.pointAt parameter =
    original.pointAt crossing.samples.1.parameters.upper := crossing.joinTarget_pointAt after parameter

/-- The actual target join retains the complete original comparison between the two cached endpoint owners. -/
example : (crossing.joinTarget after).projection.chamberOverlap =
    (crossing.targetFrame.prepareOverlap after.sourceFrame).overlap := crossing.joinTarget_overlap after

/-- The original target join adds no crossing event. -/
example : (crossing.joinTarget after).projection.event = .stationary := crossing.joinTarget_event after

/-- The combined path retains both exact cached paths and the actual crossing between its two computed joins. -/
example : crossing.pathWithComplements before after =
    before.path.append (.cons (crossing.joinSource before)
      (.cons crossing.toSegment (.cons (crossing.joinTarget after) after.path))) := rfl

/-- The combined path retains the exact computed cell budgets and three original crossing/comparison steps. -/
example : (crossing.pathWithComplements before after).stepCount =
    2 * (beforeSeparation.subdivisionCount + afterSeparation.subdivisionCount) + 5 := by
  rewrite [crossing.pathWithComplements_stepCount before after, before.path_stepCount, after.path_stepCount]
  omega0

/-- Extracted words retain the actual atomic crossing between the two cached complementary words. -/
example : (crossing.pathWithComplements before after).word =
    (before.path.word ++ crossing.toSegment.crossings) ++ after.path.word :=
  crossing.pathWithComplements_word before after

/-- Actual complementary caches contribute no crossings beyond their same original prepared window segment. -/
example : (crossing.pathWithComplements before after).word = crossing.toSegment.crossings :=
  crossing.pathWithComplements_word_window before after

end Joins

namespace Two

/-- A retained nonzero-slope chart has two events on the same original vertical axis segment. -/
def segment : AxisSegment (gaussian (-1 / 2) (-1)) (gaussian (-1 / 2) 2) := .vertical (-1 / 2) (-1) 2

/-- The original negative real coordinate excludes the physical zero branch throughout the unit interval. -/
theorem avoidsZero : segment.Avoids 0 := by
  intro parameter _ _ same
  have real := congrArg (fun point : Gaussian => point.re) same
  exact (by decide : (-1 / 2 : Coordinate) ≠ 0) real

/-- The same original real coordinate excludes the physical one branch throughout the unit interval. -/
theorem avoidsOne : segment.Avoids 1 := by
  intro parameter _ _ same
  have real := congrArg (fun point : Gaussian => point.re) same
  exact (by decide : (-1 / 2 : Coordinate) ≠ 1) real

/-- The original endpoint-interval checker computes its zero event. -/
def zero : segment.ProjectionCollision 1 0 :=
  AxisSegment.ProjectionCollision.ofContainedReading segment 1 0 (by constructor <;> decide +kernel)

/-- The same original checker computes its one event. -/
def one : segment.ProjectionCollision 1 1 :=
  AxisSegment.ProjectionCollision.ofContainedReading segment 1 1 (by constructor <;> decide +kernel)

/-- Automatic complementary preparation selects the actual zero-then-one order from the original velocity. -/
example : (match zero.prepareCrossingComplements one avoidsZero avoidsOne
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) with
  | .inl _ => true | .inr _ => false) = true := by decide +kernel

/-- The original reversed axis has its own exact zero event in the same chart. -/
def reverseZero : segment.reverse.ProjectionCollision 1 0 :=
  AxisSegment.ProjectionCollision.ofContainedReading segment.reverse 1 0 (by constructor <;> decide +kernel)

/-- The original reversed axis retains its own exact one event. -/
def reverseOne : segment.reverse.ProjectionCollision 1 1 :=
  AxisSegment.ProjectionCollision.ofContainedReading segment.reverse 1 1 (by constructor <;> decide +kernel)

/-- Automatic complementary preparation selects one then zero after reversing the same original geometry. -/
example : (match reverseZero.prepareCrossingComplements reverseOne avoidsZero.reverse avoidsOne.reverse
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) with
  | .inl _ => true | .inr _ => false) = false := by decide +kernel

end Two

end TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Complement
