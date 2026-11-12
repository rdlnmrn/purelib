module

import Purelib.Curves.Legendre.Paths.AxisSegment.Preparation
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Complement
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Cover
import Purelib.Curves.Legendre.Paths.AxisSegment
import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Curves.Legendre.Paths.Path
import Purelib.Curves.Legendre.Paths.Path.Refinement
import Purelib.Curves.Legendre.Paths.Projection
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.QuotientFreeOmega

/-! # Original endpoint ownership and intrinsic Legendre axis-path preparation -/

namespace TestPurelib.Curves.Legendre.Paths.AxisSegment.Preparation

open Purelib.Curves.Legendre.Paths
open Purelib.Data.Gaussian.Coordinates
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open AxisSegment.ProjectionCollision

section Two

variable {start finish : Gaussian} {original : AxisSegment start finish}
    {slope firstReading lastReading : Coordinate}
    {firstCollision : original.ProjectionCollision slope firstReading}
    {lastCollision : original.ProjectionCollision slope lastReading}
    (first : PreparedWindow firstCollision) (last : PreparedWindow lastCollision)
    {source target : Gaussian}
    {beforeSegment : AxisSegment source (original.pointAt first.samples.1.parameters.lower)}
    {betweenSegment : AxisSegment (original.pointAt first.samples.1.parameters.upper)
      (original.pointAt last.samples.1.parameters.lower)}
    {afterSegment : AxisSegment (original.pointAt last.samples.1.parameters.upper) target}
    {beforeSeparation : beforeSegment.ProjectionSeparation slope} {beforeWindows : beforeSeparation.SubdivisionWindows}
    {betweenSeparation : betweenSegment.ProjectionSeparation slope}
    {betweenWindows : betweenSeparation.SubdivisionWindows}
    {afterSeparation : afterSegment.ProjectionSeparation slope} {afterWindows : afterSeparation.SubdivisionWindows}
    (before : beforeSeparation.PreparedSubdivision beforeWindows)
    (between : betweenSeparation.PreparedSubdivision betweenWindows)
    (after : afterSeparation.PreparedSubdivision afterWindows)

/-- The actual two-crossing path retains every computed cell, three midpoint folds and four endpoint comparisons. -/
example : (first.pathWithWindows last before between after).stepCount =
    2 * (beforeSeparation.subdivisionCount + betweenSeparation.subdivisionCount + afterSeparation.subdivisionCount) +
      9 := by
  rewrite [first.pathWithWindows_stepCount last before between after,
    before.path_stepCount, between.path_stepCount, after.path_stepCount]
  omega0

/-- The complete original two-crossing fold retains the same three cached paths and all four actual joins in order. -/
example :
    let tail := between.path.append
      (.cons (last.joinSource between) (.cons last.toSegment (.cons (last.joinTarget after) after.path)))
    first.pathWithWindows last before between after = before.path.append
      (.cons (first.joinSource before) (.cons first.toSegment (.cons (first.joinTarget between) tail))) := rfl

/-- The complete two-window fold retains exactly its original first and last crossing words. -/
example :
    (first.pathWithWindows last before between after).word = first.toSegment.crossings ++ last.toSegment.crossings :=
  first.pathWithWindows_word last before between after

end Two

/-- Both actual two-event branches retain their original computed generators in the selected parameter order. -/
example {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (zero : segment.ProjectionCollision slope 0) (one : segment.ProjectionCollision slope 1)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1) :
    (zero.prepareCrossingPath one avoidsZero avoidsOne startZero finishZero startOne finishOne).2.2.word =
      if 0 < segment.projectionVelocity slope then [zero.generator, one.generator]
      else [one.generator, zero.generator] :=
  zero.prepareCrossingPath_word_generators one avoidsZero avoidsOne startZero finishZero startOne finishOne

/-- Intrinsic axis preparation derives its two-generator bound without a supplied chart or braid certificate. -/
example {start finish : Gaussian} (segment : AxisSegment start finish)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) :
    (segment.preparePath avoidsZero avoidsOne).2.2.word.length ≤ 2 :=
  segment.preparePath_word_length_le avoidsZero avoidsOne

/-- Both actual original axis preparations retain the same ordered signed word in charts paying their endpoint costs. -/
example {start finish : Gaussian} (segment : AxisSegment start finish) (first last : Coordinate)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (firstStartZero : (Rotation.rotate first start).re ≠ 0) (firstFinishZero : (Rotation.rotate first finish).re ≠ 0)
    (firstStartOne : (Rotation.rotate first start).re ≠ 1) (firstFinishOne : (Rotation.rotate first finish).re ≠ 1)
    (lastStartZero : (Rotation.rotate last start).re ≠ 0) (lastFinishZero : (Rotation.rotate last finish).re ≠ 0)
    (lastStartOne : (Rotation.rotate last start).re ≠ 1) (lastFinishOne : (Rotation.rotate last finish).re ≠ 1)
    (startFirst : Projection.slopeCost start < first) (finishFirst : Projection.slopeCost finish < first)
    (startLast : Projection.slopeCost start < last) (finishLast : Projection.slopeCost finish < last) :
    (segment.preparePathAt first avoidsZero avoidsOne
      firstStartZero firstFinishZero firstStartOne firstFinishOne).2.2.word =
        (segment.preparePathAt last avoidsZero avoidsOne
          lastStartZero lastFinishZero lastStartOne lastFinishOne).2.2.word :=
  segment.preparePathAt_word_eq_of_slopeCost first last avoidsZero avoidsOne
    firstStartZero firstFinishZero firstStartOne firstFinishOne lastStartZero lastFinishZero lastStartOne lastFinishOne
    startFirst finishFirst startLast finishLast

/-- A regular original axis constructs actual endpoint frames and a certified path from intrinsic avoidance alone. -/
def prepared {start finish : Gaussian} (segment : AxisSegment start finish)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) :
    Σ source : Frame start, Σ target : Frame finish, Path source target := segment.preparePath avoidsZero avoidsOne

/-- Both actual frames from intrinsic preparation retain the computed common endpoint chart and branch reading. -/
example {start finish : Gaussian} (segment : AxisSegment start finish)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) :
    let endpoints : Fin 2 → Gaussian := fun index => if index.val = 0 then start else finish
    let slope := Projection.forParameters endpoints
    let result := segment.preparePath avoidsZero avoidsOne
    result.1.InChart slope ∧ result.2.1.InChart slope := segment.preparePath_inChart avoidsZero avoidsOne

/-- Endpoint safety is retained in both actual source and target frames of the internally prepared path. -/
example {start finish : Gaussian} (segment : AxisSegment start finish)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) :
    start ≠ 0 ∧ start ≠ 1 ∧ finish ≠ 0 ∧ finish ≠ 1 :=
  let result := segment.preparePath avoidsZero avoidsOne
  ⟨result.1.parameter_ne_zero, result.1.parameter_ne_one,
    result.2.1.parameter_ne_zero, result.2.1.parameter_ne_one⟩

/-- Intrinsic avoidance constructs the complete ordered physical refinement internally for the actual returned path. -/
example {start finish : Gaussian} (segment : AxisSegment start finish)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) :
    (segment.preparePath avoidsZero avoidsOne).2.2.RefinesAxis segment 0 1 :=
  segment.preparePath_refinesAxis avoidsZero avoidsOne

/-- Every original unit point is visited by an actual retained unit segment or endpoint of the intrinsic preparation. -/
example {start finish : Gaussian} (segment : AxisSegment start finish)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (segment.preparePath avoidsZero avoidsOne).2.2.Visits (segment.pointAt parameter) :=
  segment.preparePath_visits avoidsZero avoidsOne parameter inside

/-- A displayed regular chart retains its actual reading in either path endpoint for every checker combination. -/
example {start finish : Gaussian} (segment : AxisSegment start finish) (slope : Coordinate)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1) :
    let result := segment.preparePathAt slope avoidsZero avoidsOne startZero finishZero startOne finishOne
    result.1.InChart slope ∧ result.2.1.InChart slope :=
  segment.preparePathAt_inChart slope avoidsZero avoidsOne startZero finishZero startOne finishOne

/-- The actual one-crossing path is the complete cached original fold transported only by axis endpoint equalities. -/
example {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : segment.ProjectionCollision slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (other : segment.ProjectionClearance slope (1 - reading)) :
    let complements := collision.prepareSingleCrossingComplements
      avoidsZero avoidsOne fixed startMisses finishMisses other
    let beforeWindows := complements.2.1.prepareSubdivisionWindows
    let before := complements.2.1.prepareSubdivision beforeWindows
    let afterWindows := complements.2.2.prepareSubdivisionWindows
    let after := complements.2.2.prepareSubdivision afterWindows
    (collision.prepareSingleCrossingPath avoidsZero avoidsOne fixed startMisses finishMisses other).2.2 =
      (complements.1.pathWithComplements before after).castParameters segment.pointAt_zero segment.pointAt_one := rfl

namespace Nongeneric

/-- An original vertical path has a zero projected reading throughout its entire zero-slope chart. -/
def segment : AxisSegment (gaussian 0 1) (gaussian 0 2) := .vertical 0 1 2

/-- Every unit point of this vertical path has positive imaginary coordinate, excluding any real branch reading. -/
theorem avoidsReal (reading : Coordinate) : segment.Avoids (gaussian reading 0) := by
  intro parameter nonnegative _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  have positive : 0 < 1 + (2 - 1) * parameter := Arithmetic.add_pos_of_pos_of_nonneg_direct
    (by decide) (Arithmetic.mul_nonneg_direct (by decide : (0 : Coordinate) ≤ 2 - 1) nonnegative)
  exact positive.ne' imaginary

/-- The zero-slope projection is tied at every original parameter, including both endpoints. -/
example (parameter : Coordinate) : (Rotation.rotate 0 (segment.pointAt parameter)).re = 0 := by
  rewrite [Rotation.rotate_real, Fraction.Field.zero_mul_direct]
  change (0 : Coordinate) + 0 = 0
  rfl

/-- Intrinsic preparation accepts the nongeneric original path without a supplied chart or successful preparation. -/
def result : Σ source : Frame (gaussian 0 1), Σ target : Frame (gaussian 0 2), Path source target :=
  segment.preparePath (avoidsReal 0) (avoidsReal 1)

/-- The internally computed chart is exactly five halves in both actual returned frames. -/
example : result.1.InChart (5 / 2) ∧ result.2.1.InChart (5 / 2) := by
  let endpoints : Fin 2 → Gaussian := fun index => if index.val = 0 then gaussian 0 1 else gaussian 0 2
  have slope : Projection.forParameters endpoints = 5 / 2 := by decide +kernel
  have presented := segment.preparePath_inChart (avoidsReal 0) (avoidsReal 1)
  change result.1.InChart (Projection.forParameters endpoints) ∧
    result.2.1.InChart (Projection.forParameters endpoints) at presented
  rewrite [slope] at presented
  exact presented

/-- The nongeneric projected path's actual prepared data refines the same original complete physical axis. -/
example : result.2.2.RefinesAxis segment 0 1 := segment.preparePath_refinesAxis (avoidsReal 0) (avoidsReal 1)

/-- Every original unit point on the nongeneric path has an actual membership witness in that same prepared path. -/
example (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    result.2.2.Visits (segment.pointAt parameter) :=
  segment.preparePath_visits (avoidsReal 0) (avoidsReal 1) parameter inside

end Nongeneric

/-- Successful checked preparation derives the same original physical refinement with no caller certificate. -/
example {start finish : Gaussian} (segment : AxisSegment start finish) :
    match segment.checkPath with
    | .inl success => success.2.2.2.RefinesAxis segment 0 1
    | .inr _ => True := segment.checkPath_refinesAxis

/-- Checked path preparation retains the complete original computed safety outcome. -/
example {start finish : Gaussian} (segment : AxisSegment start finish) :
    match segment.checkPath with
    | .inl success => segment.checkSafety = .inl success.1
    | .inr collision => segment.checkSafety = .inr collision := segment.checkPath_safety

/-- Every returned invalidity identifies the original intrinsic avoidance condition violated by that segment. -/
example {start finish : Gaussian} (segment : AxisSegment start finish) :
    match segment.checkPath with
    | .inl _ => True
    | .inr (.inl _) => ¬ segment.Avoids 0
    | .inr (.inr _) => ¬ segment.Avoids 1 := by
  cases segment.checkPath with
  | inl success => exact True.intro
  | inr collision =>
      cases collision with
      | inl zero => exact zero.not_avoids
      | inr one => exact one.not_avoids

/-- An interior physical zero collision is rejected with its exact original half-unit parameter. -/
example :
    match (AxisSegment.horizontal (-(1 / 4)) (1 / 4) 0).checkPath with
    | .inr (.inl collision) => collision.parameter = 1 / 2
    | _ => False := rfl

/-- An interior physical one collision is retained separately with its exact original half-unit parameter. -/
example :
    match (AxisSegment.horizontal (3 / 4) (5 / 4) 0).checkPath with
    | .inr (.inr collision) => collision.parameter = 1 / 2
    | _ => False := rfl

/-- The checked closed interval rejects a singular starting endpoint with its actual unit parameter zero. -/
example :
    match (AxisSegment.horizontal 0 (1 / 4) 0).checkPath with
    | .inr (.inl collision) => collision.parameter = 0
    | _ => False := rfl

/-- The checked closed interval rejects a singular finishing endpoint with its actual unit parameter one. -/
example :
    match (AxisSegment.horizontal (3 / 4) 1 0).checkPath with
    | .inr (.inr collision) => collision.parameter = 1
    | _ => False := rfl

/-- A whole-unit separated original chart makes the actual intrinsic axis path's complete braid word empty. -/
example {start finish : Gaussian} (segment : AxisSegment start finish) (slope : Coordinate)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1)
    (separated : ∀ parameter : Coordinate, 0 ≤ parameter → parameter ≤ 1 →
      (Rotation.rotate slope (segment.pointAt parameter)).re ≠ 0 ∧
        (Rotation.rotate slope (segment.pointAt parameter)).re ≠ 1) :
    (segment.preparePathAt slope avoidsZero avoidsOne startZero finishZero startOne finishOne).2.2.word = [] :=
  segment.preparePathAt_word_nil slope avoidsZero avoidsOne startZero finishZero startOne finishOne separated

/-- Every original safe horizontal axis has empty prepared word from intrinsic avoidance alone. -/
example (first last height : Coordinate)
    (avoidsZero : (AxisSegment.horizontal first last height).Avoids 0)
    (avoidsOne : (AxisSegment.horizontal first last height).Avoids 1) :
    ((AxisSegment.horizontal first last height).preparePath avoidsZero avoidsOne).2.2.word = [] :=
  AxisSegment.preparePath_horizontal_word_nil first last height avoidsZero avoidsOne

/-- Intrinsic one-event preparation retains exactly its same internally computed original crossing-window word. -/
example {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : segment.ProjectionCollision slope reading) (avoidsZero : segment.Avoids 0)
    (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (other : segment.ProjectionClearance slope (1 - reading)) :
    let complements := collision.prepareSingleCrossingComplements
      avoidsZero avoidsOne fixed startMisses finishMisses other
    (collision.prepareSingleCrossingPath avoidsZero avoidsOne fixed startMisses finishMisses other).2.2.word =
      complements.1.toSegment.crossings :=
  collision.prepareSingleCrossingPath_word avoidsZero avoidsOne fixed startMisses finishMisses other

end TestPurelib.Curves.Legendre.Paths.AxisSegment.Preparation
