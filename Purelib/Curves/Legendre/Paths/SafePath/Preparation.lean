module

public import Purelib.Curves.Legendre.Paths.AxisSegment.Preparation
import Purelib.Curves.Legendre.Paths.SafePath
import Purelib.Curves.Legendre.Paths.Path.Refinement
import Purelib.Curves.Legendre.Paths.Path
import Purelib.Curves.Legendre.Paths.Frame.Overlap
import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Curves.Legendre.Paths.AxisSegment.Window
import Purelib.Curves.Legendre.Paths.AxisSegment
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.List.Append
import Purelib.Topology.Knot.Braid.Basic

/-!
# Original finite safe-path preparation in one internally selected chart

The same original vertex family computes one chart for all retained axes.
Every original axis prepares its actual frames and path in that chart, and
an actual common-owner comparison joins the head's target frame to the
prepared original tail's source frame. Physical refinement binds the output
to the whole same original safe path, including its retained segment order.
-/

public section

namespace Purelib.Curves.Legendre.Paths.SafePath

open Purelib.Data.Gaussian.Coordinates
open Purelib.Data.Rat.Fraction.Order
open Purelib.Topology.Knot

/-- Actual original endpoint frames and their prepared path, retaining its shared chart and original physical parent. -/
abbrev PreparedPath {start finish : Gaussian} (original : SafePath start finish) (slope : Coordinate) :=
  Σ source : Frame start, Σ target : Frame finish,
    {prepared : Path source target //
      source.InChart slope ∧ target.InChart slope ∧ prepared.RefinesSafePath original}

namespace PreparedPath

/-- Read the same actual original source frame retained by this whole-path preparation. -/
@[expose] def sourceFrame {start finish : Gaussian} {original : SafePath start finish} {slope : Coordinate}
    (prepared : original.PreparedPath slope) : Frame start := prepared.1

/-- Read the same actual original target frame retained by this whole-path preparation. -/
@[expose] def targetFrame {start finish : Gaussian} {original : SafePath start finish} {slope : Coordinate}
    (prepared : original.PreparedPath slope) : Frame finish := prepared.2.1

/-- Read the stored original prepared path without preparing any segment or frame again. -/
@[expose] def path {start finish : Gaussian} {original : SafePath start finish} {slope : Coordinate}
    (prepared : original.PreparedPath slope) : Path prepared.sourceFrame prepared.targetFrame := prepared.2.2.val

/-- The same actual stored source frame retains the displayed shared chart and logical branch order. -/
theorem sourceFrame_inChart {start finish : Gaussian} {original : SafePath start finish} {slope : Coordinate}
    (prepared : original.PreparedPath slope) : prepared.sourceFrame.InChart slope := prepared.2.2.property.1

/-- The same actual stored target frame retains the displayed shared chart and logical branch order. -/
theorem targetFrame_inChart {start finish : Gaussian} {original : SafePath start finish} {slope : Coordinate}
    (prepared : original.PreparedPath slope) : prepared.targetFrame.InChart slope := prepared.2.2.property.2.1

/-- The actual stored path retains a complete ordered axis refinement of every original safe-path segment. -/
theorem path_refinesSafePath {start finish : Gaussian} {original : SafePath start finish} {slope : Coordinate}
    (prepared : original.PreparedPath slope) : prepared.path.RefinesSafePath original := prepared.2.2.property.2.2

/-- Every point of the original retained finite safe path occurs on this same actual stored prepared path. -/
theorem path_visits {start finish : Gaussian} {original : SafePath start finish} {slope : Coordinate}
    (prepared : original.PreparedPath slope) {point : Gaussian} (visited : original.Visits point) :
    prepared.path.Visits point := prepared.path_refinesSafePath.visits visited

/-- Reverse the retained preparation of the same original finite safe path without preparing its frames again.

The exact original endpoint frames exchange places in the same chart.
Every stored segment, owner overlap and clearance uses its original reversal;
physical refinement is proved against the original reversed safe path.
-/
@[expose] def reverse {start finish : Gaussian} {original : SafePath start finish} {slope : Coordinate}
    (prepared : original.PreparedPath slope) : original.reverse.PreparedPath slope :=
  ⟨prepared.targetFrame, prepared.sourceFrame, prepared.path.reverse,
    prepared.targetFrame_inChart, prepared.sourceFrame_inChart, prepared.path_refinesSafePath.reverse⟩

/-- The reversed preparation retains exactly the two original endpoint frames in the opposite order. -/
theorem reverse_frames {start finish : Gaussian} {original : SafePath start finish} {slope : Coordinate}
    (prepared : original.PreparedPath slope) :
    prepared.reverse.sourceFrame = prepared.targetFrame ∧ prepared.reverse.targetFrame = prepared.sourceFrame :=
  ⟨rfl, rfl⟩

/-- Read the actual reversed stored path without constructing another preparation or endpoint owner. -/
theorem reverse_path {start finish : Gaussian} {original : SafePath start finish} {slope : Coordinate}
    (prepared : original.PreparedPath slope) : prepared.reverse.path = prepared.path.reverse := rfl

/-- The retained reversed preparation has the inverse of its original ordered signed word. -/
theorem reverse_word {start finish : Gaussian} {original : SafePath start finish} {slope : Coordinate}
    (prepared : original.PreparedPath slope) : prepared.reverse.path.word = prepared.path.word.inverse :=
  Path.word_reverse prepared.path

/-- Reversal transports the actual target root owner by the original backward owner map. -/
theorem reverse_ownerTransport {start finish : Gaussian} {original : SafePath start finish} {slope : Coordinate}
    (prepared : original.PreparedPath slope) (index : prepared.targetFrame.chamber.Index) :
    prepared.reverse.path.ownerTransport.forward index = prepared.path.ownerTransport.backward index :=
  Path.ownerTransport_reverse prepared.path index

/-- Every original physical path point remains on the same retained reversed preparation. -/
theorem reverse_visits {start finish : Gaussian} {original : SafePath start finish} {slope : Coordinate}
    (prepared : original.PreparedPath slope) {point : Gaussian} (visited : original.Visits point) :
    prepared.reverse.path.Visits point := (prepared.path_visits visited).reverse

/-- Prepend an actual original-axis preparation to the same prepared original safe tail in their shared chart.

The head's actual target frame and the tail's actual source frame compute
one original common-owner comparison. Its geometry is the same original
axis restricted at its endpoint. The stored head, join and tail path are
folded once, retaining the original safe-path parent and physical refinement.
-/
@[expose] def prepend {start middle finish : Gaussian} (segment : AxisSegment start middle)
    (safe : AxisSegment.Safe segment) {tail : SafePath middle finish} {slope : Coordinate}
    {left : Frame start} {center : Frame middle} (head : Path left center)
    (sourceChart : left.InChart slope) (targetChart : center.InChart slope)
    (headRefinement : head.RefinesAxis segment 0 1) (remaining : tail.PreparedPath slope) :
    (SafePath.cons segment safe tail).PreparedPath slope := by
  let comparison := center.prepareOverlap remaining.sourceFrame
  let geometry := (segment.restrict 1 1).castParameters segment.pointAt_one segment.pointAt_one
  let joined := comparison.toSegmentInChart geometry targetChart remaining.sourceFrame_inChart
  let prepared := head.append (Path.cons joined remaining.path)
  refine ⟨left, remaining.targetFrame, prepared, sourceChart, remaining.targetFrame_inChart, ?_⟩
  have joinRefinement : (Path.cons joined (Path.nil remaining.sourceFrame)).RefinesAxis segment 1 1 :=
    Path.RefinesAxis.single segment joined (Basic.le_refl _) (by
      intro parameter
      rewrite [Frame.PreparedOverlap.toSegmentInChart_geometry, AxisSegment.castParameters_pointAt,
        AxisSegment.restrict_pointAt]
      rfl)
  have whole := Path.RefinesSafePath.cons segment safe (headRefinement.append segment joinRefinement)
    remaining.path_refinesSafePath
  rewrite [Path.append_assoc] at whole
  exact whole

/-- The original head/tail preparation retains its same actual source and target frames. -/
theorem prepend_frames {start middle finish : Gaussian} (segment : AxisSegment start middle)
    (safe : AxisSegment.Safe segment) {tail : SafePath middle finish} {slope : Coordinate}
    {left : Frame start} {center : Frame middle} (head : Path left center)
    (sourceChart : left.InChart slope) (targetChart : center.InChart slope)
    (headRefinement : head.RefinesAxis segment 0 1) (remaining : tail.PreparedPath slope) :
    (prepend segment safe head sourceChart targetChart headRefinement remaining).sourceFrame = left ∧
      (prepend segment safe head sourceChart targetChart headRefinement remaining).targetFrame =
        remaining.targetFrame :=
  ⟨rfl, rfl⟩

/-- The complete stored head/tail path reads back to its same original head, actual computed join and retained tail. -/
theorem prepend_path {start middle finish : Gaussian} (segment : AxisSegment start middle)
    (safe : AxisSegment.Safe segment) {tail : SafePath middle finish} {slope : Coordinate}
    {left : Frame start} {center : Frame middle} (head : Path left center)
    (sourceChart : left.InChart slope) (targetChart : center.InChart slope)
    (headRefinement : head.RefinesAxis segment 0 1) (remaining : tail.PreparedPath slope) :
    (prepend segment safe head sourceChart targetChart headRefinement remaining).path =
      let comparison := center.prepareOverlap remaining.sourceFrame
      let geometry := (segment.restrict 1 1).castParameters segment.pointAt_one segment.pointAt_one
      let joined := comparison.toSegmentInChart geometry targetChart remaining.sourceFrame_inChart
      head.append (Path.cons joined remaining.path) := rfl

/-- The complete original head/tail fold retains only the concatenated words of its actual stored head and tail.

The common-owner join remains part of the same actual path. Its computed
stationary event contributes no word, and the original path append retains
the stored head and tail words in their original traversal order.
-/
theorem prepend_word {start middle finish : Gaussian} (segment : AxisSegment start middle)
    (safe : AxisSegment.Safe segment) {tail : SafePath middle finish} {slope : Coordinate}
    {left : Frame start} {center : Frame middle} (head : Path left center)
    (sourceChart : left.InChart slope) (targetChart : center.InChart slope)
    (headRefinement : head.RefinesAxis segment 0 1) (remaining : tail.PreparedPath slope) :
    (prepend segment safe head sourceChart targetChart headRefinement remaining).path.word =
      head.word ++ remaining.path.word := by
  let comparison := center.prepareOverlap remaining.sourceFrame
  let geometry := (segment.restrict 1 1).castParameters segment.pointAt_one segment.pointAt_one
  let joined := comparison.toSegmentInChart geometry targetChart remaining.sourceFrame_inChart
  change (head.append (Path.cons joined remaining.path)).word = _
  rewrite [Path.word_append]
  rfl

end PreparedPath

/-- Prepare the whole same original finite safe path in a displayed chart separating its retained vertices.

The original head and tail are each prepared once. Their actual endpoint
frames derive a stationary common-owner join at the original middle
parameter. Appending those stored paths preserves an ordered physical
refinement of every original head, including the constant comparison.
Intrinsic start regularity supplies the frame of an empty original path.
-/
@[expose] def preparePathAt : {start finish : Gaussian} → (original : SafePath start finish) →
    (slope : Coordinate) → (nonzero : start ≠ 0) → (notOne : start ≠ 1) →
    (∀ index : Fin (original.stepCount + 1),
      (Rotation.rotate slope (original.vertices index)).re ≠ 0 ∧
        (Rotation.rotate slope (original.vertices index)).re ≠ 1) → original.PreparedPath slope
  | _, _, .nil point, slope, nonzero, notOne, separated => by
      have pointSeparated := separated 0
      rewrite [vertices_source, Rotation.rotate_real] at pointSeparated
      let frame := Frame.ofProjection point nonzero notOne slope pointSeparated
      have chart := Frame.ofProjection_inChart point nonzero notOne slope pointSeparated
      exact ⟨frame, frame, Path.nil frame, chart, chart, Path.RefinesSafePath.nil frame⟩
  | _, _, .cons segment safe tail, slope, nonzero, notOne, separated => by
      have sourceSeparated := separated 0
      rewrite [vertices_source] at sourceSeparated
      have tailSeparated : ∀ index : Fin (tail.stepCount + 1),
          (Rotation.rotate slope (tail.vertices index)).re ≠ 0 ∧
            (Rotation.rotate slope (tail.vertices index)).re ≠ 1 := by
        intro index
        have reading := separated index.succ
        rewrite [vertices_tail] at reading
        exact reading
      have targetSeparated := tailSeparated 0
      rewrite [tail.vertices_source] at targetSeparated
      have tailNonzero := safe.avoidsZero.avoids 1 (by decide) (by decide)
      have tailNotOne := safe.avoidsOne.avoids 1 (by decide) (by decide)
      rewrite [segment.pointAt_one] at tailNonzero tailNotOne
      let head := segment.preparePathAt slope safe.avoidsZero.avoids safe.avoidsOne.avoids
        sourceSeparated.1 targetSeparated.1 sourceSeparated.2 targetSeparated.2
      have headChart := segment.preparePathAt_inChart slope safe.avoidsZero.avoids safe.avoidsOne.avoids
        sourceSeparated.1 targetSeparated.1 sourceSeparated.2 targetSeparated.2
      let remaining := preparePathAt tail slope tailNonzero tailNotOne tailSeparated
      have headRefinement := segment.preparePathAt_refinesAxis slope safe.avoidsZero.avoids safe.avoidsOne.avoids
        sourceSeparated.1 targetSeparated.1 sourceSeparated.2 targetSeparated.2
      exact PreparedPath.prepend segment safe head.2.2 headChart.1 headChart.2 headRefinement remaining

/-- The actual shared-chart preparation has at most two braid generators per original retained axis.

Each actual head preparation contributes at most its two original reading
events. The original common-owner join is stationary, and the same actual
tail retains its own bound. Structural concatenation counts these actual
word contributions without counting subdivisions or replacing the path.
-/
theorem preparePathAt_word_length_le : {start finish : Gaussian} → (original : SafePath start finish) →
    (slope : Coordinate) → (nonzero : start ≠ 0) → (notOne : start ≠ 1) →
    (separated : ∀ index : Fin (original.stepCount + 1),
      (Rotation.rotate slope (original.vertices index)).re ≠ 0 ∧
        (Rotation.rotate slope (original.vertices index)).re ≠ 1) →
    (original.preparePathAt slope nonzero notOne separated).path.word.length ≤ 2 * original.stepCount
  | _, _, .nil point, _, _, _, _ => by
      change (0 : Nat) ≤ 2 * 0
      decide
  | _, _, .cons segment safe tail, slope, nonzero, notOne, separated => by
      have sourceSeparated := separated 0
      rewrite [vertices_source] at sourceSeparated
      have tailSeparated : ∀ index : Fin (tail.stepCount + 1),
          (Rotation.rotate slope (tail.vertices index)).re ≠ 0 ∧
            (Rotation.rotate slope (tail.vertices index)).re ≠ 1 := by
        intro index
        have reading := separated index.succ
        rewrite [vertices_tail] at reading
        exact reading
      have targetSeparated := tailSeparated 0
      rewrite [tail.vertices_source] at targetSeparated
      have tailNonzero := safe.avoidsZero.avoids 1 (by decide) (by decide)
      have tailNotOne := safe.avoidsOne.avoids 1 (by decide) (by decide)
      rewrite [segment.pointAt_one] at tailNonzero tailNotOne
      let head := segment.preparePathAt slope safe.avoidsZero.avoids safe.avoidsOne.avoids
        sourceSeparated.1 targetSeparated.1 sourceSeparated.2 targetSeparated.2
      have headChart := segment.preparePathAt_inChart slope safe.avoidsZero.avoids safe.avoidsOne.avoids
        sourceSeparated.1 targetSeparated.1 sourceSeparated.2 targetSeparated.2
      let remaining := preparePathAt tail slope tailNonzero tailNotOne tailSeparated
      have headRefinement := segment.preparePathAt_refinesAxis slope safe.avoidsZero.avoids safe.avoidsOne.avoids
        sourceSeparated.1 targetSeparated.1 sourceSeparated.2 targetSeparated.2
      change
        (PreparedPath.prepend segment safe head.2.2 headChart.1 headChart.2 headRefinement remaining).path.word.length ≤
          2 * (tail.stepCount + 1)
      rewrite [PreparedPath.prepend_word, Data.List.Append.length_append]
      have headBound := segment.preparePathAt_word_length_le slope safe.avoidsZero.avoids safe.avoidsOne.avoids
        sourceSeparated.1 targetSeparated.1 sourceSeparated.2 targetSeparated.2
      have tailBound := preparePathAt_word_length_le tail slope tailNonzero tailNotOne tailSeparated
      calc
        head.2.2.word.length + remaining.path.word.length ≤ 2 + 2 * tail.stepCount :=
          Nat.add_le_add headBound tailBound
        _ = 2 * (tail.stepCount + 1) :=
          (Nat.add_comm 2 (2 * tail.stepCount)).trans (Nat.mul_succ 2 tail.stepCount).symm

/-- Charts paying every original vertex cost prepare the same complete ordered signed word of the original safe path.

Each actual head uses its original axis comparison. The computed owner
joins remain stationary in their own charts, and structural concatenation
compares the same actual tail. Frames, windows, covers and collision
parameters stay with their distinct original prepared paths.
-/
theorem preparePathAt_word_eq_of_slopeCost : {start finish : Gaussian} → (original : SafePath start finish) →
    (first last : Coordinate) → (nonzero : start ≠ 0) → (notOne : start ≠ 1) →
    (firstSeparated : ∀ index : Fin (original.stepCount + 1),
      (Rotation.rotate first (original.vertices index)).re ≠ 0 ∧
        (Rotation.rotate first (original.vertices index)).re ≠ 1) →
    (lastSeparated : ∀ index : Fin (original.stepCount + 1),
      (Rotation.rotate last (original.vertices index)).re ≠ 0 ∧
        (Rotation.rotate last (original.vertices index)).re ≠ 1) →
    (firstPaid : ∀ index : Fin (original.stepCount + 1), Projection.slopeCost (original.vertices index) < first) →
    (lastPaid : ∀ index : Fin (original.stepCount + 1), Projection.slopeCost (original.vertices index) < last) →
    (original.preparePathAt first nonzero notOne firstSeparated).path.word =
      (original.preparePathAt last nonzero notOne lastSeparated).path.word
  | _, _, .nil _, _, _, _, _, _, _, _, _ => by
      change ([] : List (Braid.Generator 3)) = []
      rfl
  | _, _, .cons segment safe tail, first, last, nonzero, notOne,
      firstSeparated, lastSeparated, firstPaid, lastPaid => by
      have sourceFirst := firstSeparated 0
      have sourceLast := lastSeparated 0
      rewrite [vertices_source] at sourceFirst sourceLast
      have tailFirstSeparated : ∀ index : Fin (tail.stepCount + 1),
          (Rotation.rotate first (tail.vertices index)).re ≠ 0 ∧
            (Rotation.rotate first (tail.vertices index)).re ≠ 1 := by
        intro index
        have reading := firstSeparated index.succ
        rewrite [vertices_tail] at reading
        exact reading
      have tailLastSeparated : ∀ index : Fin (tail.stepCount + 1),
          (Rotation.rotate last (tail.vertices index)).re ≠ 0 ∧
            (Rotation.rotate last (tail.vertices index)).re ≠ 1 := by
        intro index
        have reading := lastSeparated index.succ
        rewrite [vertices_tail] at reading
        exact reading
      have targetFirst := tailFirstSeparated 0
      have targetLast := tailLastSeparated 0
      rewrite [tail.vertices_source] at targetFirst targetLast
      have tailFirstPaid : ∀ index : Fin (tail.stepCount + 1), Projection.slopeCost (tail.vertices index) < first := by
        intro index
        have payment := firstPaid index.succ
        rewrite [vertices_tail] at payment
        exact payment
      have tailLastPaid : ∀ index : Fin (tail.stepCount + 1), Projection.slopeCost (tail.vertices index) < last := by
        intro index
        have payment := lastPaid index.succ
        rewrite [vertices_tail] at payment
        exact payment
      have sourceFirstPaid := firstPaid 0
      have sourceLastPaid := lastPaid 0
      rewrite [vertices_source] at sourceFirstPaid sourceLastPaid
      have targetFirstPaid := tailFirstPaid 0
      have targetLastPaid := tailLastPaid 0
      rewrite [tail.vertices_source] at targetFirstPaid targetLastPaid
      have tailNonzero := safe.avoidsZero.avoids 1 (by decide) (by decide)
      have tailNotOne := safe.avoidsOne.avoids 1 (by decide) (by decide)
      rewrite [segment.pointAt_one] at tailNonzero tailNotOne
      let firstHead := segment.preparePathAt first safe.avoidsZero.avoids safe.avoidsOne.avoids
        sourceFirst.1 targetFirst.1 sourceFirst.2 targetFirst.2
      let lastHead := segment.preparePathAt last safe.avoidsZero.avoids safe.avoidsOne.avoids
        sourceLast.1 targetLast.1 sourceLast.2 targetLast.2
      have firstChart := segment.preparePathAt_inChart first safe.avoidsZero.avoids safe.avoidsOne.avoids
        sourceFirst.1 targetFirst.1 sourceFirst.2 targetFirst.2
      have lastChart := segment.preparePathAt_inChart last safe.avoidsZero.avoids safe.avoidsOne.avoids
        sourceLast.1 targetLast.1 sourceLast.2 targetLast.2
      have firstRefinement := segment.preparePathAt_refinesAxis first safe.avoidsZero.avoids safe.avoidsOne.avoids
        sourceFirst.1 targetFirst.1 sourceFirst.2 targetFirst.2
      have lastRefinement := segment.preparePathAt_refinesAxis last safe.avoidsZero.avoids safe.avoidsOne.avoids
        sourceLast.1 targetLast.1 sourceLast.2 targetLast.2
      let firstTail := preparePathAt tail first tailNonzero tailNotOne tailFirstSeparated
      let lastTail := preparePathAt tail last tailNonzero tailNotOne tailLastSeparated
      change
        (PreparedPath.prepend segment safe firstHead.2.2 firstChart.1 firstChart.2
          firstRefinement firstTail).path.word =
          (PreparedPath.prepend segment safe lastHead.2.2 lastChart.1 lastChart.2 lastRefinement lastTail).path.word
      rewrite [PreparedPath.prepend_word, PreparedPath.prepend_word]
      have heads := segment.preparePathAt_word_eq_of_slopeCost first last safe.avoidsZero.avoids safe.avoidsOne.avoids
        sourceFirst.1 targetFirst.1 sourceFirst.2 targetFirst.2 sourceLast.1 targetLast.1 sourceLast.2 targetLast.2
        sourceFirstPaid targetFirstPaid sourceLastPaid targetLastPaid
      have tails := preparePathAt_word_eq_of_slopeCost tail first last tailNonzero tailNotOne
        tailFirstSeparated tailLastSeparated tailFirstPaid tailLastPaid
      exact congrArg₂ (fun headWord tailWord => headWord ++ tailWord) heads tails

/-- Prepare the whole original finite safe path using one chart computed internally from its same actual vertices.

Intrinsic start regularity handles an empty path. The retained segment
safety data proves every later vertex regular, so the computed chart
separates every vertex and supplies all axis and join preparation conditions.
No root frame, chart, subdivision or physical refinement is supplied.
-/
@[expose] def preparePath {start finish : Gaussian} (original : SafePath start finish)
    (nonzero : start ≠ 0) (notOne : start ≠ 1) : original.PreparedPath original.projectionSlope :=
  original.preparePathAt original.projectionSlope nonzero notOne (original.projectionSlope_separates nonzero notOne)

/-- The internally charted original finite-path preparation has at most two braid generators per original axis. -/
theorem preparePath_word_length_le {start finish : Gaussian} (original : SafePath start finish)
    (nonzero : start ≠ 0) (notOne : start ≠ 1) :
    (original.preparePath nonzero notOne).path.word.length ≤ 2 * original.stepCount :=
  original.preparePathAt_word_length_le original.projectionSlope nonzero notOne
    (original.projectionSlope_separates nonzero notOne)

/-- Every chart paying the original vertex costs prepares the same word as the internally computed whole-path chart.

Intrinsic start regularity and the original safe axes derive all endpoint
reading exclusions. The original finite vertex family computes the other
chart and pays each of its costs internally. Both actual prepared paths
retain their own geometric caches and read the same ordered signed word.
-/
theorem preparePath_word_eq_of_slopeCost {start finish : Gaussian} (original : SafePath start finish)
    (slope : Coordinate) (nonzero : start ≠ 0) (notOne : start ≠ 1)
    (paid : ∀ index : Fin (original.stepCount + 1), Projection.slopeCost (original.vertices index) < slope) :
    (original.preparePathAt slope nonzero notOne
      (original.vertices_separated_of_slopeCost slope nonzero notOne paid)).path.word =
        (original.preparePath nonzero notOne).path.word :=
  original.preparePathAt_word_eq_of_slopeCost slope original.projectionSlope nonzero notOne
    (original.vertices_separated_of_slopeCost slope nonzero notOne paid)
    (original.projectionSlope_separates nonzero notOne) paid
    (Projection.slopeCost_lt_forParameters original.vertices)

/-- Internally retained safety and preparation caches for the same original finite indexed axis family.

The original existing safe path retains the exact input axes in order.
Its same actual preparation supplies the computed chart, endpoint frames,
physical refinement and point coverage; neither cache is a caller input.
-/
abbrev PreparedAxes (size : Nat) (points : Fin (size + 1) → Gaussian)
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)) :=
  Σ original : {path : SafePath (points 0) (points ⟨size, Nat.lt_succ_self size⟩) //
      path.FollowsAxes size points axes}, original.val.PreparedPath original.val.projectionSlope

namespace PreparedAxes

/-- Read the same actual safe-path cache derived internally from the original input axes. -/
@[expose] def original {size : Nat} {points : Fin (size + 1) → Gaussian}
    {axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)}
    (prepared : PreparedAxes size points axes) : SafePath (points 0) (points ⟨size, Nat.lt_succ_self size⟩) :=
  prepared.1.val

/-- The stored safety cache retains each complete original axis in its original finite input order. -/
theorem original_followsAxes {size : Nat} {points : Fin (size + 1) → Gaussian}
    {axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)}
    (prepared : PreparedAxes size points axes) : prepared.original.FollowsAxes size points axes := prepared.1.property

/-- Read the same stored whole-path preparation without computing any safety or preparation again. -/
@[expose] def preparation {size : Nat} {points : Fin (size + 1) → Gaussian}
    {axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)}
    (prepared : PreparedAxes size points axes) : prepared.original.PreparedPath prepared.original.projectionSlope :=
  prepared.2

/-- Read the actual source frame of the same internally retained preparation. -/
@[expose] def sourceFrame {size : Nat} {points : Fin (size + 1) → Gaussian}
    {axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)}
    (prepared : PreparedAxes size points axes) : Frame (points 0) := prepared.preparation.sourceFrame

/-- Read the actual target frame of the same internally retained preparation. -/
@[expose] def targetFrame {size : Nat} {points : Fin (size + 1) → Gaussian}
    {axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)}
    (prepared : PreparedAxes size points axes) : Frame (points ⟨size, Nat.lt_succ_self size⟩) :=
  prepared.preparation.targetFrame

/-- Read the actual stored prepared path of the original finite input family. -/
@[expose] def path {size : Nat} {points : Fin (size + 1) → Gaussian}
    {axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)}
    (prepared : PreparedAxes size points axes) : Path prepared.sourceFrame prepared.targetFrame :=
  prepared.preparation.path

/-- The internally retained safety cache contains exactly the original number of input axes. -/
theorem original_stepCount {size : Nat} {points : Fin (size + 1) → Gaussian}
    {axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)}
    (prepared : PreparedAxes size points axes) : prepared.original.stepCount = size :=
  prepared.original_followsAxes.stepCount

/-- Every stored vertex retains its same original input ordinal and Gaussian parameter. -/
theorem original_vertices {size : Nat} {points : Fin (size + 1) → Gaussian}
    {axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)}
    (prepared : PreparedAxes size points axes) (index : Fin (size + 1)) :
    prepared.original.vertices
      (Fin.cast (congrArg (fun count : Nat => count + 1) prepared.original_stepCount).symm index) = points index :=
  prepared.original_followsAxes.vertices index

/-- Both actual prepared endpoint frames retain the same internally computed chart and logical branch order. -/
theorem inChart {size : Nat} {points : Fin (size + 1) → Gaussian}
    {axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)}
    (prepared : PreparedAxes size points axes) :
    prepared.sourceFrame.InChart prepared.original.projectionSlope ∧
      prepared.targetFrame.InChart prepared.original.projectionSlope :=
  ⟨prepared.preparation.sourceFrame_inChart, prepared.preparation.targetFrame_inChart⟩

/-- The actual stored prepared path physically refines the same internally retained original safe path. -/
theorem path_refinesSafePath {size : Nat} {points : Fin (size + 1) → Gaussian}
    {axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)}
    (prepared : PreparedAxes size points axes) : prepared.path.RefinesSafePath prepared.original :=
  prepared.preparation.path_refinesSafePath

/-- Every original input unit-axis point occurs on the actual internally prepared path. -/
theorem path_visits_axis {size : Nat} {points : Fin (size + 1) → Gaussian}
    {axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)}
    (prepared : PreparedAxes size points axes) (index : Fin size) (parameter : Coordinate)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) : prepared.path.Visits ((axes index).pointAt parameter) :=
  prepared.preparation.path_visits (prepared.original_followsAxes.visits index parameter inside)

/-- An empty original input family prepares no artificial axis or comparison segment. -/
theorem empty_stepCount {points : Fin 1 → Gaussian} {axes : (index : Fin 0) →
    AxisSegment (points index.castSucc) (points index.succ)} (prepared : PreparedAxes 0 points axes) :
    prepared.path.stepCount = 0 := by
  have refinement := prepared.path_refinesSafePath
  rewrite [prepared.original_followsAxes.nil_eq] at refinement
  exact Path.RefinesSafePath.nil_data refinement

end PreparedAxes

/-- Prepare the same original finite indexed axis family from intrinsic regularity and whole-unit singular avoidance.

The original safe path and every clearance are computed internally once.
That actual cache supplies the original vertex family, computed chart and
whole-path preparation. The result retains both actual caches, all original
axis ordinals, their physical refinement and complete unit-point coverage.
No clearance, frame, successful search, subdivision or braid is an input.
-/
@[expose] def prepareAxes (size : Nat) (points : Fin (size + 1) → Gaussian)
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ))
    (avoidsZero : ∀ index : Fin size, (axes index).Avoids 0) (avoidsOne : ∀ index : Fin size, (axes index).Avoids 1)
    (nonzero : points 0 ≠ 0) (notOne : points 0 ≠ 1) : PreparedAxes size points axes :=
  let original := ofAxisSegments size points axes avoidsZero avoidsOne
  let follows := ofAxisSegments_followsAxes size points axes avoidsZero avoidsOne
  let prepared := original.preparePath nonzero notOne
  ⟨⟨original, follows⟩, prepared⟩

/-- Intrinsic preparation stores the complete original internally computed safety fold. -/
theorem prepareAxes_original (size : Nat) (points : Fin (size + 1) → Gaussian)
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ))
    (avoidsZero : ∀ index : Fin size, (axes index).Avoids 0) (avoidsOne : ∀ index : Fin size, (axes index).Avoids 1)
    (nonzero : points 0 ≠ 0) (notOne : points 0 ≠ 1) :
    (prepareAxes size points axes avoidsZero avoidsOne nonzero notOne).original =
      ofAxisSegments size points axes avoidsZero avoidsOne := rfl

/-- Intrinsic preparation retains its actual original whole-path preparation without rebuilding either cache. -/
theorem prepareAxes_preparation (size : Nat) (points : Fin (size + 1) → Gaussian)
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ))
    (avoidsZero : ∀ index : Fin size, (axes index).Avoids 0) (avoidsOne : ∀ index : Fin size, (axes index).Avoids 1)
    (nonzero : points 0 ≠ 0) (notOne : points 0 ≠ 1) :
    (prepareAxes size points axes avoidsZero avoidsOne nonzero notOne).preparation =
      (ofAxisSegments size points axes avoidsZero avoidsOne).preparePath nonzero notOne := rfl

/-- Intrinsic finite-axis preparation derives its actual two-generators-per-input-axis bound internally. -/
theorem prepareAxes_word_length_le (size : Nat) (points : Fin (size + 1) → Gaussian)
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ))
    (avoidsZero : ∀ index : Fin size, (axes index).Avoids 0) (avoidsOne : ∀ index : Fin size, (axes index).Avoids 1)
    (nonzero : points 0 ≠ 0) (notOne : points 0 ≠ 1) :
    (prepareAxes size points axes avoidsZero avoidsOne nonzero notOne).path.word.length ≤ 2 * size := by
  let original := ofAxisSegments size points axes avoidsZero avoidsOne
  calc
    (prepareAxes size points axes avoidsZero avoidsOne nonzero notOne).path.word.length ≤ 2 * original.stepCount :=
      original.preparePath_word_length_le nonzero notOne
    _ = 2 * size := congrArg (fun count : Nat => 2 * count)
      (ofAxisSegments_stepCount size points axes avoidsZero avoidsOne)

/-- Check and prepare the whole original finite axis family without any caller regularity or preparation certificate.

Exact source checks also cover an empty family. The same original whole-unit
axis checker either retains an actual singular collision at its original
finite index or returns its computed safety cache. A success prepares and
stores that exact cache, with its actual frames, path and physical readbacks.
Invalidity identifies the violated source condition or original axis point.
-/
@[expose] def checkPrepareAxes (size : Nat) (points : Fin (size + 1) → Gaussian)
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)) :
    PreparedAxes size points axes ⊕
      ({excluded : Gaussian // (excluded = 0 ∨ excluded = 1) ∧ points 0 = excluded} ⊕
        (Σ index : Fin size, AxisSegment.Collision (axes index) 0 ⊕ AxisSegment.Collision (axes index) 1)) :=
  if atZero : points 0 = 0 then
    .inr (.inl ⟨0, Or.inl rfl, atZero⟩)
  else if atOne : points 0 = 1 then
    .inr (.inl ⟨1, Or.inr rfl, atOne⟩)
  else
    match checkAxisSegments size points axes with
    | .inl original => .inl ⟨original, original.val.preparePath atZero atOne⟩
    | .inr collision => .inr (.inr collision)

/-- Every actual checked success has at most two braid generators per original input axis.

The same returned safety cache retains its original finite count. Its
actual whole-path preparation provides the word bound, including all
crossing windows and owner comparisons. Invalidity introduces no prepared
path or word claim.
-/
theorem checkPrepareAxes_word_length_le (size : Nat) (points : Fin (size + 1) → Gaussian)
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)) :
    match checkPrepareAxes size points axes with
    | .inl prepared => prepared.path.word.length ≤ 2 * size
    | .inr _ => True := by
  unfold checkPrepareAxes
  by_cases atZero : points 0 = 0
  · rewrite [dif_pos atZero]
    exact True.intro
  · rewrite [dif_neg atZero]
    by_cases atOne : points 0 = 1
    · rewrite [dif_pos atOne]
      exact True.intro
    · rewrite [dif_neg atOne]
      cases checkAxisSegments size points axes with
      | inl original =>
          calc
            (original.val.preparePath atZero atOne).path.word.length ≤ 2 * original.val.stepCount :=
              original.val.preparePath_word_length_le atZero atOne
            _ = 2 * size := congrArg (fun count : Nat => 2 * count) original.property.stepCount
      | inr collision => exact True.intro

/-- The checked frontend retains the complete actual safety-check outcome at every regular original source.

A success reads the same actual stored safe path and its original geometric
readback from the checker. An axis failure retains the same original indexed
collision. Source invalidity cannot occur under the two supplied intrinsic
source exclusions; no equality to a recomputed clearance replaces the cache.
-/
theorem checkPrepareAxes_safety (size : Nat) (points : Fin (size + 1) → Gaussian)
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ))
    (nonzero : points 0 ≠ 0) (notOne : points 0 ≠ 1) :
    match checkPrepareAxes size points axes with
    | .inl prepared => checkAxisSegments size points axes = .inl ⟨prepared.original, prepared.original_followsAxes⟩
    | .inr (.inl _) => False
    | .inr (.inr collision) => checkAxisSegments size points axes = .inr collision := by
  unfold checkPrepareAxes
  rewrite [dif_neg nonzero, dif_neg notOne]
  cases checkAxisSegments size points axes with
  | inl original => rfl
  | inr collision => rfl

/-- Intrinsic whole-unit admissibility guarantees success of the same complete checked finite-axis preparation.

The exact checked result supplies its own success witness. A source
invalidity would violate an original source exclusion. Each returned axis
collision contradicts its same original axis's whole-unit avoidance at the
actual retained unit parameter, so no successful-attempt certificate is an
additional assumption.
-/
theorem checkPrepareAxes_succeeds (size : Nat) (points : Fin (size + 1) → Gaussian)
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ))
    (avoidsZero : ∀ index : Fin size, (axes index).Avoids 0) (avoidsOne : ∀ index : Fin size, (axes index).Avoids 1)
    (nonzero : points 0 ≠ 0) (notOne : points 0 ≠ 1) :
    ∃ prepared : PreparedAxes size points axes, checkPrepareAxes size points axes = .inl prepared := by
  cases checkPrepareAxes size points axes with
  | inl prepared => exact ⟨prepared, rfl⟩
  | inr invalid =>
      cases invalid with
      | inl source =>
          rcases source.property.1 with atZero | atOne
          · exact False.elim (nonzero (source.property.2.trans atZero))
          · exact False.elim (notOne (source.property.2.trans atOne))
      | inr entry =>
          rcases entry with ⟨index, collision⟩
          cases collision with
          | inl zero =>
              exact False.elim (avoidsZero index zero.parameter zero.nonnegative zero.atMostOne zero.hits)
          | inr one =>
              exact False.elim (avoidsOne index one.parameter one.nonnegative one.atMostOne one.hits)

end Purelib.Curves.Legendre.Paths.SafePath
