module

public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Restriction
public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Crossing
public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Cover
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Height
import Purelib.Curves.Legendre.Paths.Path
import Purelib.Curves.Legendre.Paths.Path.Refinement
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.QuotientFreeOmega

/-!
# Complementary intervals of retained Legendre crossing windows

The actual original crossing windows determine their complementary cuts.
Affine-event uniqueness computes both projection clearances on those same
restrictions. Two-event preparation orders and retains both actual crossing
packets internally, including reversed projection direction.
-/

public section

namespace Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Coordinates
open Fraction.Order

namespace OwnerWindow

/-- Derive both original projection clearances before a retained single-event window.

Strict anchor containment excludes the event reading on the entire prefix.
The other reading's original whole-segment clearance restricts to the same
actual cuts. The fixed reading determines the original zero/one pair.
-/
@[expose] def separationBefore {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    (window : OwnerWindow collision) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (before : window.parameters.lower < collision.val)
    (other : ProjectionClearance segment slope (1 - reading)) :
    ProjectionSeparation (segment.restrict 0 window.parameters.lower) slope := by
  let event := collision.clearanceBefore 0 window.parameters.lower startMisses
    (before.trans_le' window.bounds.1) before
  let absent := other.restrict 0 window.parameters.lower ⟨le_rfl, by decide⟩
    ⟨window.bounds.1, window.bounds.2.1.le.trans window.bounds.2.2⟩
  if zero : reading = 0 then
    subst reading
    exact ⟨event, absent⟩
  else
    have one : reading = 1 := fixed.resolve_left zero
    subst reading
    exact ⟨absent, event⟩

/-- Derive both original projection clearances after a retained single-event window.

Strict anchor containment excludes the event reading on the actual suffix.
Restriction of the other reading's original clearance derives the remaining
gap, including a suffix whose original upper cut is the unit endpoint.
-/
@[expose] def separationAfter {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    (window : OwnerWindow collision) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (after : collision.val < window.parameters.upper)
    (other : ProjectionClearance segment slope (1 - reading)) :
    ProjectionSeparation (segment.restrict window.parameters.upper 1) slope := by
  let event := collision.clearanceAfter window.parameters.upper 1 startMisses after
    (after.trans_le window.bounds.2.2)
  let absent := other.restrict window.parameters.upper 1
    ⟨window.bounds.1.trans window.bounds.2.1.le, window.bounds.2.2⟩ ⟨by decide, le_rfl⟩
  if zero : reading = 0 then
    subst reading
    exact ⟨event, absent⟩
  else
    have one : reading = 1 := fixed.resolve_left zero
    subst reading
    exact ⟨absent, event⟩

/-- Both original fixed-reading clearances on the prefix, middle and suffix of two retained windows.

Every clearance remains indexed by the original axis restriction between
the actual stored window endpoints. The two event owners remain independent.
-/
abbrev ComplementSeparations {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope firstReading lastReading : Coordinate}
    {firstCollision : ProjectionCollision segment slope firstReading}
    {lastCollision : ProjectionCollision segment slope lastReading}
    (first : OwnerWindow firstCollision) (last : OwnerWindow lastCollision) :=
  ProjectionSeparation (segment.restrict 0 first.parameters.lower) slope ×
    ProjectionSeparation (segment.restrict first.parameters.upper last.parameters.lower) slope ×
      ProjectionSeparation (segment.restrict last.parameters.upper 1) slope

/-- Compute the three complementary separation pairs from two actual ordered, straddling crossing windows.

The first event is strictly after both prefix cuts and before both middle
cuts. The last event is strictly after both middle cuts and before both
suffix cuts. The original affine uniqueness laws compute each exact gap;
no numerical clearance or alternate interval owner is supplied.
-/
@[expose] def complementSeparations {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate}
    {firstCollision : ProjectionCollision segment slope reading}
    {lastCollision : ProjectionCollision segment slope (1 - reading)}
    (first : OwnerWindow firstCollision) (last : OwnerWindow lastCollision)
    (fixed : reading = 0 ∨ reading = 1)
    (startFirst : (Rotation.rotate slope start).re ≠ reading)
    (startLast : (Rotation.rotate slope start).re ≠ 1 - reading)
    (firstAnchor : first.parameters.lower < firstCollision.val ∧ firstCollision.val < first.parameters.upper)
    (lastAnchor : last.parameters.lower < lastCollision.val ∧ lastCollision.val < last.parameters.upper)
    (ordered : first.parameters.upper < last.parameters.lower) : ComplementSeparations first last := by
  have firstLowerBeforeLast := (first.bounds.2.1.trans ordered).trans lastAnchor.1
  have lastUpperAfterFirst := (firstAnchor.2.trans ordered).trans last.bounds.2.1
  let beforeFirst := firstCollision.clearanceBefore 0 first.parameters.lower startFirst
    (firstAnchor.1.trans_le' first.bounds.1) firstAnchor.1
  let beforeLast := lastCollision.clearanceBefore 0 first.parameters.lower startLast
    (firstLowerBeforeLast.trans_le' first.bounds.1) firstLowerBeforeLast
  let betweenFirst := firstCollision.clearanceAfter first.parameters.upper last.parameters.lower startFirst
    firstAnchor.2 (firstAnchor.2.trans ordered)
  let betweenLast := lastCollision.clearanceBefore first.parameters.upper last.parameters.lower startLast
    (ordered.trans lastAnchor.1) lastAnchor.1
  let afterFirst := firstCollision.clearanceAfter last.parameters.upper 1 startFirst
    lastUpperAfterFirst (lastUpperAfterFirst.trans_le last.bounds.2.2)
  let afterLast := lastCollision.clearanceAfter last.parameters.upper 1 startLast lastAnchor.2
    (lastAnchor.2.trans_le last.bounds.2.2)
  if zero : reading = 0 then
    subst reading
    exact ⟨⟨beforeFirst, beforeLast⟩, ⟨betweenFirst, betweenLast⟩, ⟨afterFirst, afterLast⟩⟩
  else
    have one : reading = 1 := fixed.resolve_left zero
    subst reading
    exact ⟨⟨beforeLast, beforeFirst⟩, ⟨betweenLast, betweenFirst⟩, ⟨afterLast, afterFirst⟩⟩

/-- The original unit interval is covered by a retained window and its actual prefix and suffix cuts. -/
theorem complements_cover {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} {collision : ProjectionCollision segment slope reading}
    (window : OwnerWindow collision) (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (0 ≤ parameter ∧ parameter ≤ window.parameters.lower) ∨ window.parameters.Contains parameter ∨
      (window.parameters.upper ≤ parameter ∧ parameter ≤ 1) := by
  rcases le_total parameter window.parameters.lower with before | afterLower
  · exact Or.inl ⟨inside.1, before⟩
  · rcases le_total parameter window.parameters.upper with beforeUpper | after
    · exact Or.inr (Or.inl ⟨afterLower, beforeUpper⟩)
    · exact Or.inr (Or.inr ⟨after, inside.2⟩)

/-- Two retained windows and their actual three complementary cuts cover every original unit parameter.

The witness selects the prefix, first window, middle, last window or suffix
by exact endpoint comparisons. Together with their strict ordering, these
are the same consecutive original intervals consumed by path preparation.
-/
theorem twoComplements_cover {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope firstReading lastReading : Coordinate}
    {firstCollision : ProjectionCollision segment slope firstReading}
    {lastCollision : ProjectionCollision segment slope lastReading}
    (first : OwnerWindow firstCollision) (last : OwnerWindow lastCollision)
    (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (0 ≤ parameter ∧ parameter ≤ first.parameters.lower) ∨ first.parameters.Contains parameter ∨
      (first.parameters.upper ≤ parameter ∧ parameter ≤ last.parameters.lower) ∨
        last.parameters.Contains parameter ∨ (last.parameters.upper ≤ parameter ∧ parameter ≤ 1) := by
  rcases first.complements_cover parameter inside with before | inFirst | afterFirst
  · exact Or.inl before
  · exact Or.inr (Or.inl inFirst)
  · rcases le_total parameter last.parameters.lower with beforeLast | afterLower
    · exact Or.inr (Or.inr (Or.inl ⟨afterFirst.1, beforeLast⟩))
    · rcases le_total parameter last.parameters.upper with beforeUpper | afterLast
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨afterLower, beforeUpper⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨afterLast, inside.2⟩)))

namespace ComplementSeparations

/-- Materialize the three original complementary covers and their cached certified paths once each.

The same retained separation pairs determine each original finite window
budget. Each path consumes its own actual window, sample, bridge, segment
and join caches, at the endpoints of that original affine restriction.
-/
@[expose] def preparePaths {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope firstReading lastReading : Coordinate}
    {firstCollision : ProjectionCollision segment slope firstReading}
    {lastCollision : ProjectionCollision segment slope lastReading}
    {first : OwnerWindow firstCollision} {last : OwnerWindow lastCollision}
    (separations : ComplementSeparations first last) :
    (Σ windows : separations.1.SubdivisionWindows, separations.1.PreparedSubdivision windows) ×
      (Σ windows : separations.2.1.SubdivisionWindows, separations.2.1.PreparedSubdivision windows) ×
        (Σ windows : separations.2.2.SubdivisionWindows, separations.2.2.PreparedSubdivision windows) :=
  let beforeWindows := separations.1.prepareSubdivisionWindows
  let before := separations.1.prepareSubdivision beforeWindows
  let betweenWindows := separations.2.1.prepareSubdivisionWindows
  let between := separations.2.1.prepareSubdivision betweenWindows
  let afterWindows := separations.2.2.prepareSubdivisionWindows
  let after := separations.2.2.prepareSubdivision afterWindows
  ⟨⟨beforeWindows, before⟩, ⟨betweenWindows, between⟩, ⟨afterWindows, after⟩⟩

end ComplementSeparations

end OwnerWindow

namespace PreparedWindow

variable {start finish : Gaussian} {original : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision original slope reading} (crossing : PreparedWindow collision)

section Source

variable {source : Gaussian}
    {beforeSegment : AxisSegment source (original.pointAt crossing.samples.1.parameters.lower)}
    {separation : ProjectionSeparation beforeSegment slope} {windows : separation.SubdivisionWindows}
    (prepared : separation.PreparedSubdivision windows)

/-- Join the actual retained prefix target frame to the original crossing source frame.

Both cached frames have the same parameter, chart and logical branch order.
Their actual original owner comparison is computed once and supplies the
stationary overlap and sheet clearance on the original constant restriction.
No common owner, frame equality or order certificate is supplied.
-/
@[expose] def joinSource : Paths.Segment prepared.targetFrame crossing.sourceFrame :=
  let comparison := prepared.targetFrame.prepareOverlap crossing.sourceFrame
  comparison.toSegment
    (original.restrict crossing.samples.1.parameters.lower crossing.samples.1.parameters.lower)
    (prepared.targetFrame_slope.trans crossing.sourceFrame_slope.symm)
    (fun position => (prepared.targetFrame_logicalOrder position).trans
      (crossing.sourceFrame_logicalOrder position).symm)

/-- The source join retains the complete original constant restriction at the actual crossing endpoint. -/
theorem joinSource_geometry :
    (crossing.joinSource prepared).geometry =
      original.restrict crossing.samples.1.parameters.lower crossing.samples.1.parameters.lower := rfl

/-- Every source-join parameter evaluates the same actual original crossing endpoint. -/
theorem joinSource_pointAt (parameter : Coordinate) :
    (crossing.joinSource prepared).geometry.pointAt parameter =
      original.pointAt crossing.samples.1.parameters.lower :=
  (crossing.joinSource prepared).geometry.pointAt_self parameter

/-- The source join retains the complete original comparison of the two actual cached endpoint frames. -/
theorem joinSource_overlap :
    (crossing.joinSource prepared).projection.chamberOverlap =
      (prepared.targetFrame.prepareOverlap crossing.sourceFrame).overlap := rfl

/-- The original source comparison contributes no crossing event. -/
theorem joinSource_event : (crossing.joinSource prepared).projection.event = .stationary := rfl

/-- The actual source comparison refines the original zero-length interval at that same stored crossing endpoint. -/
theorem joinSource_refinesAxis :
    (Paths.Path.cons (crossing.joinSource prepared) (Paths.Path.nil crossing.sourceFrame)).RefinesAxis original
      crossing.samples.1.parameters.lower crossing.samples.1.parameters.lower :=
  Paths.Path.RefinesAxis.single original (crossing.joinSource prepared) (Basic.le_refl _) (by
    intro parameter
    rewrite [crossing.joinSource_geometry prepared]
    exact original.restrict_pointAt _ _ parameter)

end Source

section Target

variable {target : Gaussian}
    {suffix : AxisSegment (original.pointAt crossing.samples.1.parameters.upper) target}
    {separation : ProjectionSeparation suffix slope} {windows : separation.SubdivisionWindows}
    (prepared : separation.PreparedSubdivision windows)

/-- Join the original crossing target frame to the actual retained suffix source frame.

Their same retained parameter and internally derived chart/order readbacks
compute the original common-owner comparison. The actual original constant
restriction, projected overlap and bridge-clearance observations are retained.
-/
@[expose] def joinTarget : Paths.Segment crossing.targetFrame prepared.sourceFrame :=
  let comparison := crossing.targetFrame.prepareOverlap prepared.sourceFrame
  comparison.toSegment
    (original.restrict crossing.samples.1.parameters.upper crossing.samples.1.parameters.upper)
    (crossing.targetFrame_slope.trans prepared.sourceFrame_slope.symm)
    (fun position => (crossing.targetFrame_logicalOrder position).trans
      (prepared.sourceFrame_logicalOrder position).symm)

/-- The target join retains the complete original constant restriction at the actual crossing endpoint. -/
theorem joinTarget_geometry :
    (crossing.joinTarget prepared).geometry =
      original.restrict crossing.samples.1.parameters.upper crossing.samples.1.parameters.upper := rfl

/-- Every target-join parameter evaluates the same actual original crossing endpoint. -/
theorem joinTarget_pointAt (parameter : Coordinate) :
    (crossing.joinTarget prepared).geometry.pointAt parameter =
      original.pointAt crossing.samples.1.parameters.upper :=
  (crossing.joinTarget prepared).geometry.pointAt_self parameter

/-- The target join retains the complete original comparison of the two actual cached endpoint frames. -/
theorem joinTarget_overlap :
    (crossing.joinTarget prepared).projection.chamberOverlap =
      (crossing.targetFrame.prepareOverlap prepared.sourceFrame).overlap := rfl

/-- The original target comparison contributes no crossing event. -/
theorem joinTarget_event : (crossing.joinTarget prepared).projection.event = .stationary := rfl

/-- The actual target comparison refines the original zero-length interval at that same stored crossing endpoint. -/
theorem joinTarget_refinesAxis :
    (Paths.Path.cons (crossing.joinTarget prepared) (Paths.Path.nil prepared.sourceFrame)).RefinesAxis original
      crossing.samples.1.parameters.upper crossing.samples.1.parameters.upper :=
  Paths.Path.RefinesAxis.single original (crossing.joinTarget prepared) (Basic.le_refl _) (by
    intro parameter
    rewrite [crossing.joinTarget_geometry prepared]
    exact original.restrict_pointAt _ _ parameter)

end Target

/-- Fold the actual retained prefix, crossing and suffix paths with their internally computed endpoint joins.

Both complementary paths are read from their original preparation caches.
The actual original atomic crossing and its two constant owner comparisons
are inserted in traversal order, retaining every original segment and frame.
-/
@[expose] def pathWithComplements {source target : Gaussian}
    {beforeSegment : AxisSegment source (original.pointAt crossing.samples.1.parameters.lower)}
    {suffix : AxisSegment (original.pointAt crossing.samples.1.parameters.upper) target}
    {beforeSeparation : ProjectionSeparation beforeSegment slope} {beforeWindows : beforeSeparation.SubdivisionWindows}
    {afterSeparation : ProjectionSeparation suffix slope} {afterWindows : afterSeparation.SubdivisionWindows}
    (before : beforeSeparation.PreparedSubdivision beforeWindows)
    (after : afterSeparation.PreparedSubdivision afterWindows) : Paths.Path before.sourceFrame after.targetFrame :=
  let beforeJoin := crossing.joinSource before
  let afterJoin := crossing.joinTarget after
  before.path.append (.cons beforeJoin (.cons crossing.toSegment (.cons afterJoin after.path)))

section Paths

variable {source target : Gaussian}
    {beforeSegment : AxisSegment source (original.pointAt crossing.samples.1.parameters.lower)}
    {afterSegment : AxisSegment (original.pointAt crossing.samples.1.parameters.upper) target}
    {beforeSeparation : ProjectionSeparation beforeSegment slope} {beforeWindows : beforeSeparation.SubdivisionWindows}
    {afterSeparation : ProjectionSeparation afterSegment slope} {afterWindows : afterSeparation.SubdivisionWindows}
    (before : beforeSeparation.PreparedSubdivision beforeWindows)
    (after : afterSeparation.PreparedSubdivision afterWindows)

/-- The combined original path retains both complementary counts, one crossing and its two actual comparisons. -/
theorem pathWithComplements_stepCount :
    (crossing.pathWithComplements before after).stepCount = before.path.stepCount + after.path.stepCount + 3 := by
  unfold pathWithComplements
  rewrite [Paths.Path.append_stepCount]
  change before.path.stepCount + (after.path.stepCount + 1 + 1 + 1) = _
  omega0

/-- The combined original path extracts the crossing between the two cached complementary words in traversal order.

The two actual owner comparisons contribute stationary events. The
original prefix and suffix words are retained, with the same original
atomic crossing word between them.
-/
theorem pathWithComplements_word :
    (crossing.pathWithComplements before after).word =
      (before.path.word ++ crossing.toSegment.crossings) ++ after.path.word := by
  unfold pathWithComplements
  rewrite [Paths.Path.word_append]
  change before.path.word ++ (crossing.toSegment.crossings ++ after.path.word) = _
  exact (List.Append.append_assoc _ _ _).symm

/-- The complete original crossing/complement fold retains only the actual window's crossing word.

Both actual complementary caches have stationary moving cells and joins.
Their complete stored-path laws therefore remove their empty word
contributions, while the original window segment remains unchanged.
-/
theorem pathWithComplements_word_window :
    (crossing.pathWithComplements before after).word = crossing.toSegment.crossings := by
  rewrite [crossing.pathWithComplements_word before after, before.path_word_nil, after.path_word_nil]
  exact List.Append.append_nil _

/-- The actual complementary-path fold preserves physical refinement of the same parent-axis interval.

The supplied complementary refinements keep their actual stored paths and
shared window cuts. The original window segment and its two constant joins
derive their own refinements internally; composition retains all those
actual segments in the original traversal order.
-/
theorem pathWithComplements_refinesAxis {lower upper : Coordinate}
    (beforeRefinement : before.path.RefinesAxis original lower crossing.samples.1.parameters.lower)
    (afterRefinement : after.path.RefinesAxis original crossing.samples.1.parameters.upper upper) :
    (crossing.pathWithComplements before after).RefinesAxis original lower upper := by
  have tail := (crossing.joinTarget_refinesAxis after).append original afterRefinement
  have window := crossing.toPath_refinesAxis.append original tail
  have joined := (crossing.joinSource_refinesAxis before).append original window
  exact beforeRefinement.append original joined

end Paths

end PreparedWindow

/-- Compute the two original complementary clearances around one retained atomic crossing.

The actual crossing packet is computed once, then its stored window supplies
both cuts. Affine uniqueness and the other reading's original checker outcome
derive both separation pairs without caller frames, cuts or gap bounds.
-/
@[expose] def prepareSingleCrossingComplements {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (other : ProjectionClearance segment slope (1 - reading)) :
    Σ prepared : PreparedWindow collision,
      ProjectionSeparation (segment.restrict 0 prepared.samples.1.parameters.lower) slope ×
        ProjectionSeparation (segment.restrict prepared.samples.1.parameters.upper 1) slope :=
  let prepared := collision.prepareCrossingOverlap avoidsZero avoidsOne fixed startMisses finishMisses
  let window := prepared.samples.1
  let anchor := collision.prepareCrossingWindow_anchor_interior avoidsZero avoidsOne fixed startMisses finishMisses
  ⟨prepared, window.separationBefore fixed startMisses anchor.1 other,
    window.separationAfter fixed startMisses anchor.2 other⟩

/-- Single-event complement preparation retains the complete original computed atomic crossing packet. -/
theorem prepareSingleCrossingComplements_crossing {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (other : ProjectionClearance segment slope (1 - reading)) :
    (collision.prepareSingleCrossingComplements avoidsZero avoidsOne fixed startMisses finishMisses other).1 =
      collision.prepareCrossingOverlap avoidsZero avoidsOne fixed startMisses finishMisses := rfl

/-- Compute both original atomic crossings and all complementary clearances in their actual parameter order.

The original affine velocity chooses zero then one, or one then zero.
Each crossing packet is computed once and retains its own actual window,
samples, factors and bridges. The stored windows supply the strict order
and all three paired restriction clearances internally. No subdivision,
quantitative clearance, window order or braid certificate is supplied.
-/
@[expose] def prepareCrossingComplements {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (zero : ProjectionCollision segment slope 0) (one : ProjectionCollision segment slope 1)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1) :
    (Σ first : PreparedWindow zero, Σ last : PreparedWindow one,
      {_separations : OwnerWindow.ComplementSeparations first.samples.1 last.samples.1 //
        first.samples.1.parameters.upper < last.samples.1.parameters.lower}) ⊕
    (Σ first : PreparedWindow one, Σ last : PreparedWindow zero,
      {_separations : OwnerWindow.ComplementSeparations first.samples.1 last.samples.1 //
        first.samples.1.parameters.upper < last.samples.1.parameters.lower}) := by
  let zeroPrepared := zero.prepareCrossingOverlap avoidsZero avoidsOne (Or.inl rfl) startZero finishZero
  let onePrepared := one.prepareCrossingOverlap avoidsZero avoidsOne (Or.inr rfl) startOne finishOne
  let zeroWindow := zeroPrepared.samples.1
  let oneWindow := onePrepared.samples.1
  have zeroAnchor := zero.prepareCrossingWindow_anchor_interior avoidsZero avoidsOne (Or.inl rfl) startZero finishZero
  have oneAnchor := one.prepareCrossingWindow_anchor_interior avoidsZero avoidsOne (Or.inr rfl) startOne finishOne
  if positive : 0 < segment.projectionVelocity slope then
    have ordered := zero.prepareCrossingWindows_order_of_velocity_pos one avoidsZero avoidsOne
      startZero finishZero startOne finishOne positive
    exact .inl ⟨zeroPrepared, onePrepared,
      zeroWindow.complementSeparations oneWindow (Or.inl rfl) startZero startOne zeroAnchor oneAnchor ordered, ordered⟩
  else
    have negative : segment.projectionVelocity slope < 0 := by
      rcases lt_trichotomy 0 (segment.projectionVelocity slope) with increasing | equal | decreasing
      · exact (positive increasing).elim
      · exact (zero.projectionVelocity_ne_zero startZero equal.symm).elim
      · exact decreasing
    have ordered := zero.prepareCrossingWindows_order_of_velocity_neg one avoidsZero avoidsOne
      startZero finishZero startOne finishOne negative
    exact .inr ⟨onePrepared, zeroPrepared,
      oneWindow.complementSeparations zeroWindow (Or.inr rfl) startOne startZero oneAnchor zeroAnchor ordered, ordered⟩

/-- Two-event preparation retains both complete original crossing packets in the actual selected order. -/
theorem prepareCrossingComplements_crossings {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (zero : ProjectionCollision segment slope 0) (one : ProjectionCollision segment slope 1)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1) :
    match zero.prepareCrossingComplements one avoidsZero avoidsOne startZero finishZero startOne finishOne with
    | .inl packet =>
        packet.1 = zero.prepareCrossingOverlap avoidsZero avoidsOne (Or.inl rfl) startZero finishZero ∧
          packet.2.1 = one.prepareCrossingOverlap avoidsZero avoidsOne (Or.inr rfl) startOne finishOne
    | .inr packet =>
        packet.1 = one.prepareCrossingOverlap avoidsZero avoidsOne (Or.inr rfl) startOne finishOne ∧
          packet.2.1 = zero.prepareCrossingOverlap avoidsZero avoidsOne (Or.inl rfl) startZero finishZero := by
  unfold prepareCrossingComplements
  by_cases positive : 0 < segment.projectionVelocity slope
  · rewrite [dif_pos positive]
    exact ⟨rfl, rfl⟩
  · rewrite [dif_neg positive]
    exact ⟨rfl, rfl⟩

end Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision
