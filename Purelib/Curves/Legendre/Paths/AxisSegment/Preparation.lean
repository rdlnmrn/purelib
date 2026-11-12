module

public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Complement
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Crossing
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Separation
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Cover
import Purelib.Curves.Legendre.Paths.AxisSegment.Window
import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Curves.Legendre.Paths.Path
import Purelib.Curves.Legendre.Paths.Path.Refinement
import Purelib.Curves.Legendre.Paths.Projection
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Data.List.Append
import Purelib.Topology.Knot.Braid.Event
import Purelib.Tactic.QuotientFreeOmega

/-!
# Original Legendre path preparation from intrinsic axis avoidance

The original projection checks select no event, one event, or two events.
Actual crossing and complementary caches are joined in parameter order.
The complete retained path is transported to the same original endpoints;
one computed endpoint chart supplies every chart condition internally.
-/

public section

namespace Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision.PreparedWindow

open Purelib.Data

variable {start finish : Gaussian} {original : AxisSegment start finish} {slope firstReading lastReading : Coordinate}
    {firstCollision : ProjectionCollision original slope firstReading}
    {lastCollision : ProjectionCollision original slope lastReading}
    (first : PreparedWindow firstCollision) (last : PreparedWindow lastCollision)

/-- Fold two original prepared windows and three retained complementary paths in their supplied order.

Each complementary path is read from its original cache once. Four original
constant owner comparisons join the two actual window segments to those
cached endpoint frames, retaining all original segments in traversal order.
-/
@[expose] def pathWithWindows {source target : Gaussian}
    {beforeSegment : AxisSegment source (original.pointAt first.samples.1.parameters.lower)}
    {betweenSegment : AxisSegment (original.pointAt first.samples.1.parameters.upper)
      (original.pointAt last.samples.1.parameters.lower)}
    {afterSegment : AxisSegment (original.pointAt last.samples.1.parameters.upper) target}
    {beforeSeparation : ProjectionSeparation beforeSegment slope} {beforeWindows : beforeSeparation.SubdivisionWindows}
    {betweenSeparation : ProjectionSeparation betweenSegment slope}
    {betweenWindows : betweenSeparation.SubdivisionWindows}
    {afterSeparation : ProjectionSeparation afterSegment slope} {afterWindows : afterSeparation.SubdivisionWindows}
    (before : beforeSeparation.PreparedSubdivision beforeWindows)
    (between : betweenSeparation.PreparedSubdivision betweenWindows)
    (after : afterSeparation.PreparedSubdivision afterWindows) : Paths.Path before.sourceFrame after.targetFrame :=
  let firstSource := first.joinSource before
  let firstTarget := first.joinTarget between
  let lastSource := last.joinSource between
  let lastTarget := last.joinTarget after
  let tail := between.path.append (.cons lastSource (.cons last.toSegment (.cons lastTarget after.path)))
  before.path.append (.cons firstSource (.cons first.toSegment (.cons firstTarget tail)))

/-- The two-window fold retains all three cached counts, two window segments and four original comparisons. -/
theorem pathWithWindows_stepCount {source target : Gaussian}
    {beforeSegment : AxisSegment source (original.pointAt first.samples.1.parameters.lower)}
    {betweenSegment : AxisSegment (original.pointAt first.samples.1.parameters.upper)
      (original.pointAt last.samples.1.parameters.lower)}
    {afterSegment : AxisSegment (original.pointAt last.samples.1.parameters.upper) target}
    {beforeSeparation : ProjectionSeparation beforeSegment slope} {beforeWindows : beforeSeparation.SubdivisionWindows}
    {betweenSeparation : ProjectionSeparation betweenSegment slope}
    {betweenWindows : betweenSeparation.SubdivisionWindows}
    {afterSeparation : ProjectionSeparation afterSegment slope} {afterWindows : afterSeparation.SubdivisionWindows}
    (before : beforeSeparation.PreparedSubdivision beforeWindows)
    (between : betweenSeparation.PreparedSubdivision betweenWindows)
    (after : afterSeparation.PreparedSubdivision afterWindows) :
    (first.pathWithWindows last before between after).stepCount =
      before.path.stepCount + between.path.stepCount + after.path.stepCount + 6 := by
  unfold pathWithWindows
  rewrite [Paths.Path.append_stepCount]
  change before.path.stepCount + ((between.path.append
    (.cons (last.joinSource between) (.cons last.toSegment (.cons (last.joinTarget after) after.path)))).stepCount +
      1 + 1 + 1) = _
  rewrite [Paths.Path.append_stepCount]
  change before.path.stepCount + ((between.path.stepCount + (after.path.stepCount + 1 + 1 + 1)) + 1 + 1 + 1) = _
  omega0

/-- The complete original two-window fold retains exactly the two window words in their supplied traversal order.

All three actual complementary caches and four constant joins contribute
no crossings. Their stored paths and owner comparisons remain in the fold;
the complete original window segments supply its concatenated word.
-/
theorem pathWithWindows_word {source target : Gaussian}
    {beforeSegment : AxisSegment source (original.pointAt first.samples.1.parameters.lower)}
    {betweenSegment : AxisSegment (original.pointAt first.samples.1.parameters.upper)
      (original.pointAt last.samples.1.parameters.lower)}
    {afterSegment : AxisSegment (original.pointAt last.samples.1.parameters.upper) target}
    {beforeSeparation : ProjectionSeparation beforeSegment slope} {beforeWindows : beforeSeparation.SubdivisionWindows}
    {betweenSeparation : ProjectionSeparation betweenSegment slope}
    {betweenWindows : betweenSeparation.SubdivisionWindows}
    {afterSeparation : ProjectionSeparation afterSegment slope} {afterWindows : afterSeparation.SubdivisionWindows}
    (before : beforeSeparation.PreparedSubdivision beforeWindows)
    (between : betweenSeparation.PreparedSubdivision betweenWindows)
    (after : afterSeparation.PreparedSubdivision afterWindows) :
    (first.pathWithWindows last before between after).word = first.toSegment.crossings ++ last.toSegment.crossings := by
  unfold pathWithWindows
  rewrite [Paths.Path.word_append, before.path_word_nil]
  change first.toSegment.crossings ++ (between.path.append
    (.cons (last.joinSource between) (.cons last.toSegment (.cons (last.joinTarget after) after.path)))).word = _
  rewrite [Paths.Path.word_append, between.path_word_nil]
  change first.toSegment.crossings ++ (last.toSegment.crossings ++ after.path.word) = _
  rewrite [after.path_word_nil]
  exact congrArg (fun word => first.toSegment.crossings ++ word) (List.Append.append_nil last.toSegment.crossings)

/-- The two-window fold preserves the original parent-axis refinement of all three actual complementary paths. -/
theorem pathWithWindows_refinesAxis {source target : Gaussian}
    {beforeSegment : AxisSegment source (original.pointAt first.samples.1.parameters.lower)}
    {betweenSegment : AxisSegment (original.pointAt first.samples.1.parameters.upper)
      (original.pointAt last.samples.1.parameters.lower)}
    {afterSegment : AxisSegment (original.pointAt last.samples.1.parameters.upper) target}
    {beforeSeparation : ProjectionSeparation beforeSegment slope} {beforeWindows : beforeSeparation.SubdivisionWindows}
    {betweenSeparation : ProjectionSeparation betweenSegment slope}
    {betweenWindows : betweenSeparation.SubdivisionWindows}
    {afterSeparation : ProjectionSeparation afterSegment slope} {afterWindows : afterSeparation.SubdivisionWindows}
    (before : beforeSeparation.PreparedSubdivision beforeWindows)
    (between : betweenSeparation.PreparedSubdivision betweenWindows)
    (after : afterSeparation.PreparedSubdivision afterWindows) {lower upper : Coordinate}
    (beforeRefinement : before.path.RefinesAxis original lower first.samples.1.parameters.lower)
    (betweenRefinement : between.path.RefinesAxis original
      first.samples.1.parameters.upper last.samples.1.parameters.lower)
    (afterRefinement : after.path.RefinesAxis original last.samples.1.parameters.upper upper) :
    (first.pathWithWindows last before between after).RefinesAxis original lower upper := by
  have lastTail := (last.joinTarget_refinesAxis after).append original afterRefinement
  have lastWindow := last.toPath_refinesAxis.append original lastTail
  have lastJoined := (last.joinSource_refinesAxis between).append original lastWindow
  have middle := betweenRefinement.append original lastJoined
  have firstTail := (first.joinTarget_refinesAxis between).append original middle
  have firstWindow := first.toPath_refinesAxis.append original firstTail
  have firstJoined := (first.joinSource_refinesAxis before).append original firstWindow
  exact beforeRefinement.append original firstJoined

end Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision.PreparedWindow

namespace Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision

open Purelib.Data
open Purelib.Data.Gaussian.Coordinates

/-- Prepare an original one-event axis path from its actual event and absent-reading checker outcome.

The original crossing packet and complementary cuts are computed once.
Both retained clearances materialize their same covers and path caches.
The original crossing joins those actual paths, and exact endpoint transport
returns the resulting original frames and path at the original axis endpoints.
-/
@[expose] def prepareSingleCrossingPath {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (other : ProjectionClearance segment slope (1 - reading)) :
    Σ source : Paths.Frame start, Σ target : Paths.Frame finish, Paths.Path source target :=
  let complements := collision.prepareSingleCrossingComplements
    avoidsZero avoidsOne fixed startMisses finishMisses other
  let beforeWindows := complements.2.1.prepareSubdivisionWindows
  let before := complements.2.1.prepareSubdivision beforeWindows
  let afterWindows := complements.2.2.prepareSubdivisionWindows
  let after := complements.2.2.prepareSubdivision afterWindows
  let path := complements.1.pathWithComplements before after
  ⟨before.sourceFrame.castParameter segment.pointAt_zero, after.targetFrame.castParameter segment.pointAt_one,
    path.castParameters segment.pointAt_zero segment.pointAt_one⟩

/-- Both actual one-event path endpoint frames retain the original displayed chart and branch reading. -/
theorem prepareSingleCrossingPath_inChart {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (other : ProjectionClearance segment slope (1 - reading)) :
    let prepared := collision.prepareSingleCrossingPath avoidsZero avoidsOne fixed startMisses finishMisses other
    prepared.1.InChart slope ∧ prepared.2.1.InChart slope := by
  let complements := collision.prepareSingleCrossingComplements
    avoidsZero avoidsOne fixed startMisses finishMisses other
  let beforeWindows := complements.2.1.prepareSubdivisionWindows
  let before := complements.2.1.prepareSubdivision beforeWindows
  let afterWindows := complements.2.2.prepareSubdivisionWindows
  let after := complements.2.2.prepareSubdivision afterWindows
  exact ⟨before.sourceFrame_inChart.castParameter segment.pointAt_zero,
    after.targetFrame_inChart.castParameter segment.pointAt_one⟩

/-- The actual internally prepared one-event path retains the word of its same computed original crossing window.

The complementary caches and their comparisons contribute no crossings.
Exact endpoint transport preserves the whole word, so the same retained
window segment supplies the complete one-event path word without a caller
empty-complement or braid certificate.
-/
theorem prepareSingleCrossingPath_word {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (other : ProjectionClearance segment slope (1 - reading)) :
    let complements := collision.prepareSingleCrossingComplements
      avoidsZero avoidsOne fixed startMisses finishMisses other
    (collision.prepareSingleCrossingPath avoidsZero avoidsOne fixed startMisses finishMisses other).2.2.word =
      complements.1.toSegment.crossings := by
  let complements := collision.prepareSingleCrossingComplements
    avoidsZero avoidsOne fixed startMisses finishMisses other
  let beforeWindows := complements.2.1.prepareSubdivisionWindows
  let before := complements.2.1.prepareSubdivision beforeWindows
  let afterWindows := complements.2.2.prepareSubdivisionWindows
  let after := complements.2.2.prepareSubdivision afterWindows
  change ((complements.1.pathWithComplements before after).castParameters
    segment.pointAt_zero segment.pointAt_one).word = complements.1.toSegment.crossings
  rewrite [Paths.Path.castParameters_word]
  exact complements.1.pathWithComplements_word_window before after

/-- The same intrinsically prepared one-event axis path has exactly its original computed generator as its word. -/
theorem prepareSingleCrossingPath_word_generator {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (other : ProjectionClearance segment slope (1 - reading)) :
    (collision.prepareSingleCrossingPath avoidsZero avoidsOne fixed startMisses finishMisses other).2.2.word =
      [collision.generator] := by
  rewrite [collision.prepareSingleCrossingPath_word avoidsZero avoidsOne fixed startMisses finishMisses other,
    collision.prepareSingleCrossingComplements_crossing avoidsZero avoidsOne fixed startMisses finishMisses other]
  exact collision.prepareCrossingOverlap_word avoidsZero avoidsOne fixed startMisses finishMisses

/-- The internally prepared one-event path is an ordered physical refinement of the same complete original axis.

Each actual complementary path first refines its own original restriction.
The stored window bounds lift those refinements to the parent axis, where
the original window segment and constant joins complete the ordered fold.
The final endpoint transport preserves that same physical relation.
-/
theorem prepareSingleCrossingPath_refinesAxis {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (other : ProjectionClearance segment slope (1 - reading)) :
    (collision.prepareSingleCrossingPath avoidsZero avoidsOne fixed startMisses finishMisses other).2.2.RefinesAxis
      segment 0 1 := by
  let complements := collision.prepareSingleCrossingComplements
    avoidsZero avoidsOne fixed startMisses finishMisses other
  let beforeWindows := complements.2.1.prepareSubdivisionWindows
  let before := complements.2.1.prepareSubdivision beforeWindows
  let afterWindows := complements.2.2.prepareSubdivisionWindows
  let after := complements.2.2.prepareSubdivision afterWindows
  have beforeRefinement := before.path_refinesAxis.restrict_unit segment complements.1.samples.1.bounds.1
  have afterRefinement := after.path_refinesAxis.restrict_unit segment complements.1.samples.1.bounds.2.2
  exact (complements.1.pathWithComplements_refinesAxis before after beforeRefinement afterRefinement).castParameters
    segment segment.pointAt_zero segment.pointAt_one

/-- Prepare both actual projected crossings and all original complementary paths in their internally selected order.

The same original zero and one events compute the retained crossing packets
and their strict window order. Each complementary pair materializes its cover
and path cache once. The selected two-crossing fold is transported only by
the original axis endpoint equalities, retaining every actual segment/frame.
-/
@[expose] def prepareCrossingPath {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (zero : ProjectionCollision segment slope 0) (one : ProjectionCollision segment slope 1)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1) :
    Σ source : Paths.Frame start, Σ target : Paths.Frame finish, Paths.Path source target :=
  match zero.prepareCrossingComplements one avoidsZero avoidsOne startZero finishZero startOne finishOne with
  | .inl ⟨first, last, separations⟩ =>
      let paths := separations.val.preparePaths
      let path := first.pathWithWindows last paths.1.2 paths.2.1.2 paths.2.2.2
      ⟨paths.1.2.sourceFrame.castParameter segment.pointAt_zero,
        paths.2.2.2.targetFrame.castParameter segment.pointAt_one,
        path.castParameters segment.pointAt_zero segment.pointAt_one⟩
  | .inr ⟨first, last, separations⟩ =>
      let paths := separations.val.preparePaths
      let path := first.pathWithWindows last paths.1.2 paths.2.1.2 paths.2.2.2
      ⟨paths.1.2.sourceFrame.castParameter segment.pointAt_zero,
        paths.2.2.2.targetFrame.castParameter segment.pointAt_one,
        path.castParameters segment.pointAt_zero segment.pointAt_one⟩

/-- The internally ordered two-event path retains exactly its actual first and last crossing-window words.

The same original ordering procedure selects both stored crossing packets.
Their actual three complementary caches and four joins contribute no
crossings. Exact endpoint transport preserves the selected ordered word.
-/
theorem prepareCrossingPath_word {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (zero : ProjectionCollision segment slope 0) (one : ProjectionCollision segment slope 1)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1) :
    (zero.prepareCrossingPath one avoidsZero avoidsOne startZero finishZero startOne finishOne).2.2.word =
      match zero.prepareCrossingComplements one avoidsZero avoidsOne startZero finishZero startOne finishOne with
      | .inl packet => packet.1.toSegment.crossings ++ packet.2.1.toSegment.crossings
      | .inr packet => packet.1.toSegment.crossings ++ packet.2.1.toSegment.crossings := by
  unfold prepareCrossingPath
  cases zero.prepareCrossingComplements one avoidsZero avoidsOne startZero finishZero startOne finishOne with
  | inl packet =>
      rcases packet with ⟨first, last, separations⟩
      let paths := separations.val.preparePaths
      rewrite [Paths.Path.castParameters_word]
      exact first.pathWithWindows_word last paths.1.2 paths.2.1.2 paths.2.2.2
  | inr packet =>
      rcases packet with ⟨first, last, separations⟩
      let paths := separations.val.preparePaths
      rewrite [Paths.Path.castParameters_word]
      exact first.pathWithWindows_word last paths.1.2 paths.2.1.2 paths.2.2.2

/-- The actual two-event preparation word lists the original computed generators in its internally selected order.

Positive projection velocity selects zero before one; negative velocity
selects one before zero. The same retained crossing packets contribute
their original singleton words, after all actual complementary paths and
constant comparisons have been accounted for.
-/
theorem prepareCrossingPath_word_generators {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (zero : ProjectionCollision segment slope 0) (one : ProjectionCollision segment slope 1)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1) :
    (zero.prepareCrossingPath one avoidsZero avoidsOne startZero finishZero startOne finishOne).2.2.word =
      if 0 < segment.projectionVelocity slope then [zero.generator, one.generator]
      else [one.generator, zero.generator] := by
  rewrite [zero.prepareCrossingPath_word one avoidsZero avoidsOne startZero finishZero startOne finishOne]
  unfold prepareCrossingComplements
  by_cases positive : 0 < segment.projectionVelocity slope
  · rewrite [dif_pos positive, if_pos positive]
    change (zero.prepareCrossingOverlap avoidsZero avoidsOne (Or.inl rfl) startZero finishZero).toSegment.crossings ++
      (one.prepareCrossingOverlap avoidsZero avoidsOne (Or.inr rfl) startOne finishOne).toSegment.crossings = _
    rewrite [zero.prepareCrossingOverlap_word avoidsZero avoidsOne (Or.inl rfl) startZero finishZero,
      one.prepareCrossingOverlap_word avoidsZero avoidsOne (Or.inr rfl) startOne finishOne]
    rfl
  · rewrite [dif_neg positive, if_neg positive]
    change (one.prepareCrossingOverlap avoidsZero avoidsOne (Or.inr rfl) startOne finishOne).toSegment.crossings ++
      (zero.prepareCrossingOverlap avoidsZero avoidsOne (Or.inl rfl) startZero finishZero).toSegment.crossings = _
    rewrite [one.prepareCrossingOverlap_word avoidsZero avoidsOne (Or.inr rfl) startOne finishOne,
      zero.prepareCrossingOverlap_word avoidsZero avoidsOne (Or.inl rfl) startZero finishZero]
    rfl

/-- Both actual two-event path endpoint frames retain the original displayed chart and branch reading. -/
theorem prepareCrossingPath_inChart {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (zero : ProjectionCollision segment slope 0) (one : ProjectionCollision segment slope 1)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1) :
    let prepared := zero.prepareCrossingPath one avoidsZero avoidsOne startZero finishZero startOne finishOne
    prepared.1.InChart slope ∧ prepared.2.1.InChart slope := by
  unfold prepareCrossingPath
  cases zero.prepareCrossingComplements one avoidsZero avoidsOne startZero finishZero startOne finishOne with
  | inl packet =>
      rcases packet with ⟨first, last, separations⟩
      let paths := separations.val.preparePaths
      exact ⟨paths.1.2.sourceFrame_inChart.castParameter segment.pointAt_zero,
        paths.2.2.2.targetFrame_inChart.castParameter segment.pointAt_one⟩
  | inr packet =>
      rcases packet with ⟨first, last, separations⟩
      let paths := separations.val.preparePaths
      exact ⟨paths.1.2.sourceFrame_inChart.castParameter segment.pointAt_zero,
        paths.2.2.2.targetFrame_inChart.castParameter segment.pointAt_one⟩

/-- Both internally ordered two-event branches physically refine the same complete original axis segment.

The actual crossing windows retain their strict order. Their stored bounds
and order lift all three cached complementary paths to the original parent
axis. The actual four constant joins and two window segments complete the
physical refinement, which the original endpoint transport preserves.
-/
theorem prepareCrossingPath_refinesAxis {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (zero : ProjectionCollision segment slope 0) (one : ProjectionCollision segment slope 1)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1) :
    (zero.prepareCrossingPath one avoidsZero avoidsOne startZero finishZero startOne finishOne).2.2.RefinesAxis
      segment 0 1 := by
  unfold prepareCrossingPath
  cases zero.prepareCrossingComplements one avoidsZero avoidsOne startZero finishZero startOne finishOne with
  | inl packet =>
      rcases packet with ⟨first, last, separations⟩
      let paths := separations.val.preparePaths
      have before := paths.1.2.path_refinesAxis.restrict_unit segment first.samples.1.bounds.1
      have between := paths.2.1.2.path_refinesAxis.restrict_unit segment separations.property.le
      have after := paths.2.2.2.path_refinesAxis.restrict_unit segment last.samples.1.bounds.2.2
      exact (first.pathWithWindows_refinesAxis
        last paths.1.2 paths.2.1.2 paths.2.2.2 before between after).castParameters
        segment segment.pointAt_zero segment.pointAt_one
  | inr packet =>
      rcases packet with ⟨first, last, separations⟩
      let paths := separations.val.preparePaths
      have before := paths.1.2.path_refinesAxis.restrict_unit segment first.samples.1.bounds.1
      have between := paths.2.1.2.path_refinesAxis.restrict_unit segment separations.property.le
      have after := paths.2.2.2.path_refinesAxis.restrict_unit segment last.samples.1.bounds.2.2
      exact (first.pathWithWindows_refinesAxis
        last paths.1.2 paths.2.1.2 paths.2.2.2 before between after).castParameters
        segment segment.pointAt_zero segment.pointAt_one

end Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision

namespace Purelib.Curves.Legendre.Paths.AxisSegment

open Purelib.Data
open Purelib.Data.Gaussian.Coordinates

/-- Prepare the original axis path in a displayed chart whose original endpoints have distinct branch readings.

Both original projection checks run once. Their four possible combinations
select the retained separated, single-crossing or two-crossing construction.
Intrinsic avoidance supplies all physical regularity; no frame, subdivision,
clearance, signed geometry or braid certificate is supplied.
-/
@[expose] def preparePathAt {start finish : Gaussian} (segment : AxisSegment start finish) (slope : Coordinate)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1) :
    Σ source : Paths.Frame start, Σ target : Paths.Frame finish, Paths.Path source target :=
  match segment.checkProjectionCollision slope 0, segment.checkProjectionCollision slope 1 with
  | .inl zero, .inl one => zero.prepareCrossingPath one avoidsZero avoidsOne startZero finishZero startOne finishOne
  | .inl zero, .inr one =>
      zero.prepareSingleCrossingPath avoidsZero avoidsOne (Or.inl rfl) startZero finishZero one
  | .inr zero, .inl one =>
      one.prepareSingleCrossingPath avoidsZero avoidsOne (Or.inr rfl) startOne finishOne zero
  | .inr zero, .inr one =>
      let separation : ProjectionSeparation segment slope := ⟨zero, one⟩
      let windows := separation.prepareSubdivisionWindows
      let prepared := separation.prepareSubdivision windows
      ⟨prepared.sourceFrame, prepared.targetFrame, prepared.path⟩

/-- Every chart-checker outcome retains that same chart and branch reading in both actual path endpoint frames. -/
theorem preparePathAt_inChart {start finish : Gaussian} (segment : AxisSegment start finish) (slope : Coordinate)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1) :
    let prepared := segment.preparePathAt slope avoidsZero avoidsOne startZero finishZero startOne finishOne
    prepared.1.InChart slope ∧ prepared.2.1.InChart slope := by
  unfold preparePathAt
  cases segment.checkProjectionCollision slope 0 with
  | inl zero =>
      cases segment.checkProjectionCollision slope 1 with
      | inl one =>
          exact zero.prepareCrossingPath_inChart one avoidsZero avoidsOne
            startZero finishZero startOne finishOne
      | inr one =>
          exact zero.prepareSingleCrossingPath_inChart avoidsZero avoidsOne
            (Or.inl rfl) startZero finishZero one
  | inr zero =>
      cases segment.checkProjectionCollision slope 1 with
      | inl one =>
          exact one.prepareSingleCrossingPath_inChart avoidsZero avoidsOne
            (Or.inr rfl) startOne finishOne zero
      | inr one =>
          let separation : ProjectionSeparation segment slope := ⟨zero, one⟩
          let windows := separation.prepareSubdivisionWindows
          let prepared := separation.prepareSubdivision windows
          exact ⟨prepared.sourceFrame_inChart, prepared.targetFrame_inChart⟩

/-- The actual intrinsic axis preparation retains exactly the signed events selected by its original two checks.

Both successful events use the original affine traversal order. A single
event retains its original singleton generator; the absent-event branch
retains its computed stationary subdivision and empty word.
-/
theorem preparePathAt_word {start finish : Gaussian} (segment : AxisSegment start finish) (slope : Coordinate)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1) :
    (segment.preparePathAt slope avoidsZero avoidsOne startZero finishZero startOne finishOne).2.2.word =
      match segment.checkProjectionCollision slope 0, segment.checkProjectionCollision slope 1 with
      | .inl zero, .inl one =>
          if 0 < segment.projectionVelocity slope then [zero.generator, one.generator]
          else [one.generator, zero.generator]
      | .inl zero, .inr _ => [zero.generator]
      | .inr _, .inl one => [one.generator]
      | .inr _, .inr _ => [] := by
  unfold preparePathAt
  cases segment.checkProjectionCollision slope 0 with
  | inl zero =>
      cases segment.checkProjectionCollision slope 1 with
      | inl one =>
          exact zero.prepareCrossingPath_word_generators one avoidsZero avoidsOne
            startZero finishZero startOne finishOne
      | inr one =>
          exact zero.prepareSingleCrossingPath_word_generator avoidsZero avoidsOne
            (Or.inl rfl) startZero finishZero one
  | inr zero =>
      cases segment.checkProjectionCollision slope 1 with
      | inl one =>
          exact one.prepareSingleCrossingPath_word_generator avoidsZero avoidsOne
            (Or.inr rfl) startOne finishOne zero
      | inr one =>
          let separation : ProjectionSeparation segment slope := ⟨zero, one⟩
          let windows := separation.prepareSubdivisionWindows
          exact (separation.prepareSubdivision windows).path_word_nil

/-- Two charts paying both original endpoint costs prepare the same complete ordered signed axis word.

The actual projection checks agree on event presence. Positive slopes
preserve the original axis direction and complete signed generators.
The actual path-word readbacks compare all four checker branches while
retaining each chart's distinct collision parameters, windows and caches.
-/
theorem preparePathAt_word_eq_of_slopeCost {start finish : Gaussian} (segment : AxisSegment start finish)
    (first last : Coordinate) (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (firstStartZero : (Rotation.rotate first start).re ≠ 0) (firstFinishZero : (Rotation.rotate first finish).re ≠ 0)
    (firstStartOne : (Rotation.rotate first start).re ≠ 1) (firstFinishOne : (Rotation.rotate first finish).re ≠ 1)
    (lastStartZero : (Rotation.rotate last start).re ≠ 0) (lastFinishZero : (Rotation.rotate last finish).re ≠ 0)
    (lastStartOne : (Rotation.rotate last start).re ≠ 1) (lastFinishOne : (Rotation.rotate last finish).re ≠ 1)
    (startFirst : Paths.Projection.slopeCost start < first) (finishFirst : Paths.Projection.slopeCost finish < first)
    (startLast : Paths.Projection.slopeCost start < last) (finishLast : Paths.Projection.slopeCost finish < last) :
    (segment.preparePathAt first avoidsZero avoidsOne
      firstStartZero firstFinishZero firstStartOne firstFinishOne).2.2.word =
        (segment.preparePathAt last avoidsZero avoidsOne
          lastStartZero lastFinishZero lastStartOne lastFinishOne).2.2.word := by
  have firstPositive := (Paths.Projection.slopeCost_nonnegative start).trans_lt startFirst
  have lastPositive := (Paths.Projection.slopeCost_nonnegative start).trans_lt startLast
  have velocity := segment.projectionVelocity_pos_iff_of_positive_slopes first last firstPositive lastPositive
  rewrite [segment.preparePathAt_word first avoidsZero avoidsOne
    firstStartZero firstFinishZero firstStartOne firstFinishOne,
    segment.preparePathAt_word last avoidsZero avoidsOne lastStartZero lastFinishZero lastStartOne lastFinishOne]
  cases segment.checkProjectionCollision first 0 with
  | inl firstZero =>
      cases segment.checkProjectionCollision last 0 with
      | inr lastZero => exact (lastZero.excludes_collision_of_slopeCost firstZero
          startLast finishLast startFirst finishFirst (by decide) (by decide)).elim
      | inl lastZero =>
          have zero := firstZero.generator_eq_of_positive_slopes lastZero firstPositive lastPositive
          cases segment.checkProjectionCollision first 1 with
          | inl firstOne =>
              cases segment.checkProjectionCollision last 1 with
              | inr lastOne => exact (lastOne.excludes_collision_of_slopeCost firstOne
                  startLast finishLast startFirst finishFirst (by decide) (by decide)).elim
              | inl lastOne =>
                  have one := firstOne.generator_eq_of_positive_slopes lastOne firstPositive lastPositive
                  change (if 0 < segment.projectionVelocity first then [firstZero.generator, firstOne.generator]
                    else [firstOne.generator, firstZero.generator]) =
                      (if 0 < segment.projectionVelocity last then [lastZero.generator, lastOne.generator]
                      else [lastOne.generator, lastZero.generator])
                  rewrite [zero, one]
                  by_cases positive : 0 < segment.projectionVelocity first
                  · rewrite [if_pos positive, if_pos (velocity.mp positive)]
                    rfl
                  · rewrite [if_neg positive, if_neg (fun other => positive (velocity.mpr other))]
                    rfl
          | inr firstOne =>
              cases segment.checkProjectionCollision last 1 with
              | inl lastOne => exact (firstOne.excludes_collision_of_slopeCost lastOne
                  startFirst finishFirst startLast finishLast (by decide) (by decide)).elim
              | inr lastOne => exact congrArg (fun generator => [generator]) zero
  | inr firstZero =>
      cases segment.checkProjectionCollision last 0 with
      | inl lastZero => exact (firstZero.excludes_collision_of_slopeCost lastZero
          startFirst finishFirst startLast finishLast (by decide) (by decide)).elim
      | inr lastZero =>
          cases segment.checkProjectionCollision first 1 with
          | inl firstOne =>
              cases segment.checkProjectionCollision last 1 with
              | inr lastOne => exact (lastOne.excludes_collision_of_slopeCost firstOne
                  startLast finishLast startFirst finishFirst (by decide) (by decide)).elim
              | inl lastOne =>
                  exact congrArg (fun generator => [generator])
                    (firstOne.generator_eq_of_positive_slopes lastOne firstPositive lastPositive)
          | inr firstOne =>
              cases segment.checkProjectionCollision last 1 with
              | inl lastOne => exact (firstOne.excludes_collision_of_slopeCost lastOne
                  startFirst finishFirst startLast finishLast (by decide) (by decide)).elim
              | inr lastOne => rfl

/-- Whole-unit separation of both original readings makes the actual intrinsic axis preparation word empty.

Either original projected collision would contradict the same whole-unit
separation at its retained parameter. The actual absence outcomes therefore
materialize the same separated cover and cached stationary path, whose
complete word law preserves every original comparison step.
-/
theorem preparePathAt_word_nil {start finish : Gaussian} (segment : AxisSegment start finish) (slope : Coordinate)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1)
    (separated : ∀ parameter : Coordinate, 0 ≤ parameter → parameter ≤ 1 →
      (Rotation.rotate slope (segment.pointAt parameter)).re ≠ 0 ∧
        (Rotation.rotate slope (segment.pointAt parameter)).re ≠ 1) :
    (segment.preparePathAt slope avoidsZero avoidsOne startZero finishZero startOne finishOne).2.2.word = [] := by
  unfold preparePathAt
  cases segment.checkProjectionCollision slope 0 with
  | inl zero => exact False.elim ((separated zero.val zero.property.1 zero.property.2.1).1 zero.property.2.2)
  | inr zero =>
      cases segment.checkProjectionCollision slope 1 with
      | inl one => exact False.elim ((separated one.val one.property.1 one.property.2.1).2 one.property.2.2)
      | inr one =>
          let separation : ProjectionSeparation segment slope := ⟨zero, one⟩
          let windows := separation.prepareSubdivisionWindows
          exact (separation.prepareSubdivision windows).path_word_nil

/-- A safe horizontal axis contributes no crossings in any displayed chart paying both original endpoint costs. -/
theorem horizontal_preparePathAt_word_nil (first last height slope : Coordinate)
    (avoidsZero : (AxisSegment.horizontal first last height).Avoids 0)
    (avoidsOne : (AxisSegment.horizontal first last height).Avoids 1)
    (startZero : (Rotation.rotate slope (gaussian first height)).re ≠ 0)
    (finishZero : (Rotation.rotate slope (gaussian last height)).re ≠ 0)
    (startOne : (Rotation.rotate slope (gaussian first height)).re ≠ 1)
    (finishOne : (Rotation.rotate slope (gaussian last height)).re ≠ 1)
    (firstPaid : Paths.Projection.slopeCost (gaussian first height) < slope)
    (lastPaid : Paths.Projection.slopeCost (gaussian last height) < slope) :
    ((AxisSegment.horizontal first last height).preparePathAt slope avoidsZero avoidsOne
      startZero finishZero startOne finishOne).2.2.word = [] :=
  preparePathAt_word_nil _ _ avoidsZero avoidsOne startZero finishZero startOne finishOne
    (horizontal_projection_separates first last height slope avoidsZero avoidsOne firstPaid lastPaid)

/-- Every original chart outcome constructs an ordered physical refinement of the same complete axis. -/
theorem preparePathAt_refinesAxis {start finish : Gaussian} (segment : AxisSegment start finish) (slope : Coordinate)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1) :
    (segment.preparePathAt slope avoidsZero avoidsOne startZero finishZero startOne finishOne).2.2.RefinesAxis
      segment 0 1 := by
  unfold preparePathAt
  cases segment.checkProjectionCollision slope 0 with
  | inl zero =>
      cases segment.checkProjectionCollision slope 1 with
      | inl one =>
          exact zero.prepareCrossingPath_refinesAxis one avoidsZero avoidsOne
            startZero finishZero startOne finishOne
      | inr one =>
          exact zero.prepareSingleCrossingPath_refinesAxis avoidsZero avoidsOne
            (Or.inl rfl) startZero finishZero one
  | inr zero =>
      cases segment.checkProjectionCollision slope 1 with
      | inl one =>
          exact one.prepareSingleCrossingPath_refinesAxis avoidsZero avoidsOne
            (Or.inr rfl) startOne finishOne zero
      | inr one =>
          let separation : ProjectionSeparation segment slope := ⟨zero, one⟩
          let windows := separation.prepareSubdivisionWindows
          exact (separation.prepareSubdivision windows).path_refinesAxis

/-- Compute one original certified axis path from intrinsic avoidance of the two singular Legendre parameters.

The original finite endpoint family determines a common separating chart.
Intrinsic whole-segment avoidance supplies both endpoints' regularity, so
all chart conditions and projection-event outcomes are derived internally.
The result retains actual original frames and a safe certified path at the
same original axis endpoints, without a caller preparation certificate.
-/
@[expose] def preparePath {start finish : Gaussian} (segment : AxisSegment start finish)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) :
    Σ source : Paths.Frame start, Σ target : Paths.Frame finish, Paths.Path source target := by
  let endpoints : Fin 2 → Gaussian := fun index => if index.val = 0 then start else finish
  let slope := Paths.Projection.forParameters endpoints
  have startNonzero : start ≠ 0 := by
    have original := avoidsZero 0 (by decide) (by decide)
    rewrite [segment.pointAt_zero] at original
    exact original
  have startNotOne : start ≠ 1 := by
    have original := avoidsOne 0 (by decide) (by decide)
    rewrite [segment.pointAt_zero] at original
    exact original
  have finishNonzero : finish ≠ 0 := by
    have original := avoidsZero 1 (by decide) (by decide)
    rewrite [segment.pointAt_one] at original
    exact original
  have finishNotOne : finish ≠ 1 := by
    have original := avoidsOne 1 (by decide) (by decide)
    rewrite [segment.pointAt_one] at original
    exact original
  have source := Paths.Projection.forParameters_separates endpoints 0 startNonzero startNotOne
  have target := Paths.Projection.forParameters_separates endpoints 1 finishNonzero finishNotOne
  rewrite [← Rotation.rotate_real] at source target
  exact segment.preparePathAt slope avoidsZero avoidsOne source.1 target.1 source.2 target.2

/-- Every actual intrinsic axis preparation has at most two computed braid generators.

The two original reading checks select zero, one or two retained crossing
windows. Their actual cached-path word laws give the corresponding empty,
singleton or ordered two-generator word; subdivision and constant owner
comparisons add no generators.
-/
theorem preparePathAt_word_length_le {start finish : Gaussian} (segment : AxisSegment start finish) (slope : Coordinate)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1) :
    (segment.preparePathAt slope avoidsZero avoidsOne startZero finishZero startOne finishOne).2.2.word.length ≤ 2 := by
  unfold preparePathAt
  cases segment.checkProjectionCollision slope 0 with
  | inl zero =>
      cases segment.checkProjectionCollision slope 1 with
      | inl one =>
          rewrite [zero.prepareCrossingPath_word_generators one avoidsZero avoidsOne
            startZero finishZero startOne finishOne]
          by_cases positive : 0 < segment.projectionVelocity slope
          · rewrite [if_pos positive]
            exact Nat.le_refl _
          · rewrite [if_neg positive]
            exact Nat.le_refl _
      | inr one =>
          rewrite [zero.prepareSingleCrossingPath_word_generator avoidsZero avoidsOne (Or.inl rfl)
            startZero finishZero one]
          change (1 : Nat) ≤ 2
          decide
  | inr zero =>
      cases segment.checkProjectionCollision slope 1 with
      | inl one =>
          rewrite [one.prepareSingleCrossingPath_word_generator avoidsZero avoidsOne (Or.inr rfl)
            startOne finishOne zero]
          change (1 : Nat) ≤ 2
          decide
      | inr one =>
          let separation : ProjectionSeparation segment slope := ⟨zero, one⟩
          let windows := separation.prepareSubdivisionWindows
          let prepared := separation.prepareSubdivision windows
          change prepared.path.word.length ≤ 2
          rewrite [prepared.path_word_nil]
          decide

/-- The same complete intrinsic axis preparation has a two-generator word bound without a supplied chart. -/
theorem preparePath_word_length_le {start finish : Gaussian} (segment : AxisSegment start finish)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) :
    (segment.preparePath avoidsZero avoidsOne).2.2.word.length ≤ 2 := by
  unfold preparePath
  exact segment.preparePathAt_word_length_le _ _ _ _ _ _ _

/-- Intrinsic axis preparation retains the internally computed common endpoint chart in both actual frames. -/
theorem preparePath_inChart {start finish : Gaussian} (segment : AxisSegment start finish)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) :
    let endpoints : Fin 2 → Gaussian := fun index => if index.val = 0 then start else finish
    let slope := Paths.Projection.forParameters endpoints
    let prepared := segment.preparePath avoidsZero avoidsOne
    prepared.1.InChart slope ∧ prepared.2.1.InChart slope := by
  unfold preparePath
  exact segment.preparePathAt_inChart _ _ _ _ _ _ _

/-- Intrinsic avoidance constructs the ordered physical refinement of the same original complete axis internally. -/
theorem preparePath_refinesAxis {start finish : Gaussian} (segment : AxisSegment start finish)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) :
    (segment.preparePath avoidsZero avoidsOne).2.2.RefinesAxis segment 0 1 := by
  unfold preparePath
  exact segment.preparePathAt_refinesAxis _ _ _ _ _ _ _

/-- Intrinsic preparation of an original safe horizontal axis has empty braid word without any supplied chart.

The actual endpoint family computes its own slope, above both original
endpoint costs. The whole original horizontal axis then separates zero and
one in that same chart, so its actual stationary cover and retained owner
comparisons contribute no crossings.
-/
theorem preparePath_horizontal_word_nil (first last height : Coordinate)
    (avoidsZero : (AxisSegment.horizontal first last height).Avoids 0)
    (avoidsOne : (AxisSegment.horizontal first last height).Avoids 1) :
    ((AxisSegment.horizontal first last height).preparePath avoidsZero avoidsOne).2.2.word = [] := by
  let endpoints : Fin 2 → Gaussian := fun index =>
    if index.val = 0 then gaussian first height else gaussian last height
  have firstPaid := Paths.Projection.slopeCost_lt_forParameters endpoints 0
  have lastPaid := Paths.Projection.slopeCost_lt_forParameters endpoints 1
  unfold preparePath
  exact horizontal_preparePathAt_word_nil first last height (Paths.Projection.forParameters endpoints)
    avoidsZero avoidsOne _ _ _ _ firstPaid lastPaid

/-- Every original unit point is visited by the actual path constructed from the same intrinsic axis avoidance. -/
theorem preparePath_visits {start finish : Gaussian} (segment : AxisSegment start finish)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (segment.preparePath avoidsZero avoidsOne).2.2.Visits (segment.pointAt parameter) :=
  (segment.preparePath_refinesAxis avoidsZero avoidsOne).visits segment parameter inside

/-- Check whole-segment safety and prepare the path, or retain its exact violated singular-value condition.

Success retains the same computed zero/one safety cache and the actual
endpoint frames and certified path constructed from its intrinsic avoidance.
Invalidity retains the original unit parameter hitting zero or one; it
rejects that input segment without asserting a global pole or obstruction.
-/
@[expose] def checkPath {start finish : Gaussian} (segment : AxisSegment start finish) :
    (Safe segment × (Σ source : Paths.Frame start, Σ target : Paths.Frame finish, Paths.Path source target)) ⊕
      (Collision segment 0 ⊕ Collision segment 1) :=
  match segment.checkSafety with
  | .inl safe => .inl ⟨safe, segment.preparePath safe.avoidsZero.avoids safe.avoidsOne.avoids⟩
  | .inr collision => .inr collision

/-- Checked preparation retains the complete original safety-check outcome and its clearance or collision data. -/
theorem checkPath_safety {start finish : Gaussian} (segment : AxisSegment start finish) :
    match segment.checkPath with
    | .inl success => segment.checkSafety = .inl success.1
    | .inr collision => segment.checkSafety = .inr collision := by
  unfold checkPath
  cases segment.checkSafety <;> rfl

/-- Every successful safety-check outcome constructs the physical refinement of that same complete original axis. -/
theorem checkPath_refinesAxis {start finish : Gaussian} (segment : AxisSegment start finish) :
    match segment.checkPath with
    | .inl success => success.2.2.2.RefinesAxis segment 0 1
    | .inr _ => True := by
  unfold checkPath
  cases segment.checkSafety with
  | inl safe => exact segment.preparePath_refinesAxis safe.avoidsZero.avoids safe.avoidsOne.avoids
  | inr collision => exact True.intro

end Purelib.Curves.Legendre.Paths.AxisSegment
