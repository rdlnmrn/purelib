module

public import Purelib.Curves.Legendre.Paths.Projection
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Rat.Interval.Gap
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Data.Rat.Bounds.Abs
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.ConvexCombination
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Projected collisions of original axis segments

The retained rational chart sends the original axis parametrization to an
affine real segment. Its endpoint interval determines whether a prescribed
reading occurs, with an exact parameter or a proof of absence. Intrinsic
avoidance of a fixed real branch preserves nonzero signed height there.
-/

public section

namespace Purelib.Curves.Legendre.Paths.AxisSegment

open Purelib.Data
open Purelib.Data.Gaussian.Coordinates
open Purelib.Data.Rat
open Fraction.Order

/-- The real projection of the original axis parametrization interpolates its original endpoint readings. -/
theorem pointAt_projection {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope parameter : Coordinate) :
    (Rotation.rotate slope (segment.pointAt parameter)).re =
      (Rotation.rotate slope start).re +
        parameter * ((Rotation.rotate slope finish).re - (Rotation.rotate slope start).re) := by
  rewrite [Rotation.rotate_real, Rotation.rotate_real, Rotation.rotate_real]
  cases segment <;> dsimp only [pointAt, gaussian] <;> ring1

/-- The original projected endpoint readings form one retained closed rational interval.

The minimum and maximum retain both orientations and stationary segments.
They use the same chart applied to the original Gaussian endpoints. -/
@[expose] def projectionBounds {start finish : Gaussian} (_segment : AxisSegment start finish)
    (slope : Coordinate) : Interval.Bounds :=
  let first := (Rotation.rotate slope start).re
  let last := (Rotation.rotate slope finish).re
  ⟨min first last, max first last, (Basic.min_le_left _ _).trans (Basic.le_max_left _ _)⟩

/-- Read the exact affine projection velocity from the same original endpoint readings in the retained chart. -/
@[expose] def projectionVelocity {start finish : Gaussian} (_segment : AxisSegment start finish)
    (slope : Coordinate) : Coordinate :=
  (Rotation.rotate slope finish).re - (Rotation.rotate slope start).re

/-- Positive charts preserve the strict sign of the original axis projection velocity.

Horizontal axes retain their original real difference. Vertical axes
multiply their original imaginary difference by the positive chart slope.
Both constructions therefore select the same traversal direction.
-/
theorem projectionVelocity_pos_iff_of_positive_slopes {start finish : Gaussian} (segment : AxisSegment start finish)
    (first last : Coordinate) (firstPositive : 0 < first) (lastPositive : 0 < last) :
    (0 < segment.projectionVelocity first ↔ 0 < segment.projectionVelocity last) := by
  cases segment with
  | horizontal source target height =>
      have same : (AxisSegment.horizontal source target height).projectionVelocity first =
          (AxisSegment.horizontal source target height).projectionVelocity last := by
        unfold projectionVelocity
        rewrite [Rotation.rotate_real, Rotation.rotate_real, Rotation.rotate_real, Rotation.rotate_real]
        change (target + first * height) - (source + first * height) =
          (target + last * height) - (source + last * height)
        ring1
      exact ⟨fun positive => same ▸ positive, fun positive => same.symm ▸ positive⟩
  | vertical real source target =>
      have velocity (slope : Coordinate) : (AxisSegment.vertical real source target).projectionVelocity slope =
          slope * (target - source) := by
        unfold projectionVelocity
        rewrite [Rotation.rotate_real, Rotation.rotate_real]
        change (real + slope * target) - (real + slope * source) = _
        ring1
      rewrite [velocity first, velocity last]
      exact ⟨fun positive => Arithmetic.mul_pos_direct lastPositive
        (Arithmetic.pos_of_mul_pos_right_direct positive firstPositive.le),
        fun positive => Arithmetic.mul_pos_direct firstPositive
          (Arithmetic.pos_of_mul_pos_right_direct positive lastPositive.le)⟩

/-- Charts paying both original endpoint costs contain the same prescribed unit reading in their projected intervals.

Each endpoint retains both comparisons with the unit reading. The two
directed interval descriptions transfer those exact comparisons, without
identifying different chart coordinates or their collision parameters.
-/
theorem projectionBounds_contains_iff_of_slopeCost {start finish : Gaussian} (segment : AxisSegment start finish)
    (first last reading : Coordinate)
    (startFirst : Paths.Projection.slopeCost start < first) (finishFirst : Paths.Projection.slopeCost finish < first)
    (startLast : Paths.Projection.slopeCost start < last) (finishLast : Paths.Projection.slopeCost finish < last)
    (nonnegative : 0 ≤ reading) (atMostOne : reading ≤ 1) :
    ((segment.projectionBounds first).Contains reading ↔ (segment.projectionBounds last).Contains reading) := by
  have source := Paths.Projection.reading_comparisons_of_slopeCost start first last reading
    startFirst startLast nonnegative atMostOne
  have target := Paths.Projection.reading_comparisons_of_slopeCost finish first last reading
    finishFirst finishLast nonnegative atMostOne
  rewrite [← Rotation.rotate_real first start, ← Rotation.rotate_real last start] at source
  rewrite [← Rotation.rotate_real first finish, ← Rotation.rotate_real last finish] at target
  change (min (Rotation.rotate first start).re (Rotation.rotate first finish).re ≤ reading ∧
    reading ≤ max (Rotation.rotate first start).re (Rotation.rotate first finish).re) ↔
      (min (Rotation.rotate last start).re (Rotation.rotate last finish).re ≤ reading ∧
        reading ≤ max (Rotation.rotate last start).re (Rotation.rotate last finish).re)
  constructor
  · intro inside
    apply (Interval.ConvexCombination.between_endpoints_iff _ _ _).mpr
    cases (Interval.ConvexCombination.between_endpoints_iff _ _ _).mp inside with
    | inl forward => exact Or.inl ⟨source.1.mp forward.1, target.2.mp forward.2⟩
    | inr reverse => exact Or.inr ⟨target.1.mp reverse.1, source.2.mp reverse.2⟩
  · intro inside
    apply (Interval.ConvexCombination.between_endpoints_iff _ _ _).mpr
    cases (Interval.ConvexCombination.between_endpoints_iff _ _ _).mp inside with
    | inl forward => exact Or.inl ⟨source.1.mpr forward.1, target.2.mpr forward.2⟩
    | inr reverse => exact Or.inr ⟨target.1.mpr reverse.1, source.2.mpr reverse.2⟩

/-- The difference of two actual projection readings is their parameter difference times the original velocity. -/
theorem projectionDifference {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope source target : Coordinate) :
    (Rotation.rotate slope (segment.pointAt target)).re - (Rotation.rotate slope (segment.pointAt source)).re =
      (target - source) * segment.projectionVelocity slope := by
  rewrite [segment.pointAt_projection, segment.pointAt_projection]
  unfold projectionVelocity
  ring1

/-- Strictly ordered original projection readings give the same parameter order when the velocity is positive. -/
theorem parameter_lt_of_projection_lt_of_velocity_pos {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope source target : Coordinate) (positive : 0 < segment.projectionVelocity slope)
    (ordered : (Rotation.rotate slope (segment.pointAt source)).re <
      (Rotation.rotate slope (segment.pointAt target)).re) : source < target := by
  apply Arithmetic.lt_of_sub_pos_direct
  apply Arithmetic.lt_of_mul_lt_mul_right_direct (c := segment.projectionVelocity slope) _ positive
  calc
    0 * segment.projectionVelocity slope = 0 := by ring1
    _ < (Rotation.rotate slope (segment.pointAt target)).re - (Rotation.rotate slope (segment.pointAt source)).re :=
      Arithmetic.sub_pos_direct ordered
    _ = (target - source) * segment.projectionVelocity slope := segment.projectionDifference slope source target

/-- Reversely ordered original projection readings give increasing parameter order when the velocity is negative. -/
theorem parameter_lt_of_projection_gt_of_velocity_neg {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope source target : Coordinate) (negative : segment.projectionVelocity slope < 0)
    (ordered : (Rotation.rotate slope (segment.pointAt target)).re <
      (Rotation.rotate slope (segment.pointAt source)).re) : source < target := by
  have positive : 0 < -segment.projectionVelocity slope := by
    simpa only [neg_zero] using Arithmetic.neg_lt_neg_direct negative
  apply Arithmetic.lt_of_sub_pos_direct
  apply Arithmetic.lt_of_mul_lt_mul_right_direct (c := -segment.projectionVelocity slope) _ positive
  calc
    0 * -segment.projectionVelocity slope = 0 := by ring1
    _ < (Rotation.rotate slope (segment.pointAt source)).re - (Rotation.rotate slope (segment.pointAt target)).re :=
      Arithmetic.sub_pos_direct ordered
    _ = (target - source) * -segment.projectionVelocity slope := by
      rewrite [segment.projectionDifference slope target source]
      ring1

/-- Every original unit-interval point has its real reading inside the retained projected interval. -/
theorem pointAt_projection_contains {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope parameter : Coordinate) (nonnegative : 0 ≤ parameter) (atMostOne : parameter ≤ 1) :
    (segment.projectionBounds slope).Contains (Rotation.rotate slope (segment.pointAt parameter)).re := by
  rewrite [pointAt_projection]
  exact Purelib.Geometry.Rational.Box.coordinate_between
    ⟨Basic.min_le_left _ _, Basic.le_max_left _ _⟩
    ⟨Basic.min_le_right _ _, Basic.le_max_right _ _⟩ ⟨nonnegative, atMostOne⟩

/-- A safe horizontal axis separates both fixed readings throughout any chart paying its endpoint costs.

Positive or negative constant height puts both endpoint readings on the
same outer side of zero and one. Their actual projected interval contains
every original unit point. At zero height, an exact projected hit would be
the original excluded Gaussian parameter itself, contrary to unit avoidance.
-/
theorem horizontal_projection_separates (first last height slope : Coordinate)
    (avoidsZero : (AxisSegment.horizontal first last height).Avoids 0)
    (avoidsOne : (AxisSegment.horizontal first last height).Avoids 1)
    (firstPaid : Paths.Projection.slopeCost (gaussian first height) < slope)
    (lastPaid : Paths.Projection.slopeCost (gaussian last height) < slope)
    (parameter : Coordinate) (nonnegative : 0 ≤ parameter) (atMostOne : parameter ≤ 1) :
    (Rotation.rotate slope ((AxisSegment.horizontal first last height).pointAt parameter)).re ≠ 0 ∧
      (Rotation.rotate slope ((AxisSegment.horizontal first last height).pointAt parameter)).re ≠ 1 := by
  let segment := AxisSegment.horizontal first last height
  have inside := segment.pointAt_projection_contains slope parameter nonnegative atMostOne
  rcases lt_trichotomy height 0 with negative | real | positive
  · have sourceBelow : (Rotation.rotate slope (gaussian first height)).re < 0 := by
      rewrite [Rotation.rotate_real]
      exact Paths.Projection.reading_below_zero _ _ firstPaid negative
    have targetBelow : (Rotation.rotate slope (gaussian last height)).re < 0 := by
      rewrite [Rotation.rotate_real]
      exact Paths.Projection.reading_below_zero _ _ lastPaid negative
    have actualBelow := inside.2.trans_lt (Basic.max_lt sourceBelow targetBelow)
    exact ⟨actualBelow.ne, ((actualBelow.trans (by decide : (0 : Coordinate) < 1))).ne⟩
  · subst height
    have realPoint : (segment.pointAt parameter).im = 0 := rfl
    have reading := (Rotation.rotate_real slope (segment.pointAt parameter)).trans
      (Paths.Projection.reading_of_real (segment.pointAt parameter) slope realPoint)
    constructor
    · intro hits
      exact avoidsZero parameter nonnegative atMostOne (Gaussian.Basic.ext (reading.symm.trans hits) realPoint)
    · intro hits
      exact avoidsOne parameter nonnegative atMostOne (Gaussian.Basic.ext (reading.symm.trans hits) realPoint)
  · have sourceAbove : 1 < (Rotation.rotate slope (gaussian first height)).re := by
      rewrite [Rotation.rotate_real]
      exact Paths.Projection.reading_above_one _ _ firstPaid positive
    have targetAbove : 1 < (Rotation.rotate slope (gaussian last height)).re := by
      rewrite [Rotation.rotate_real]
      exact Paths.Projection.reading_above_one _ _ lastPaid positive
    have actualAbove := (Basic.lt_min sourceAbove targetAbove).trans_le inside.1
    exact ⟨(((by decide : (0 : Coordinate) < 1).trans actualAbove)).ne', actualAbove.ne'⟩

/-- Compute the original affine parameter of a prescribed real reading in the retained chart.

The rational affine inverse handles either orientation. A stationary pair
uses its original total division and returns zero. -/
@[expose] def projectionParameter {start finish : Gaussian} (_segment : AxisSegment start finish)
    (slope reading : Coordinate) : Coordinate :=
  Interval.ConvexCombination.segmentParameter
    (Rotation.rotate slope start).re (Rotation.rotate slope finish).re reading

/-- A contained reading has its computed original parameter in the closed unit interval. -/
theorem projectionParameter_bounds {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope reading : Coordinate) (inside : (segment.projectionBounds slope).Contains reading) :
    0 ≤ segment.projectionParameter slope reading ∧ segment.projectionParameter slope reading ≤ 1 :=
  Interval.ConvexCombination.segmentParameter_bounds _ _ _ inside

/-- The computed original parameter attains the prescribed contained reading in the same chart. -/
theorem projectionParameter_hits {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope reading : Coordinate) (inside : (segment.projectionBounds slope).Contains reading) :
    (Rotation.rotate slope (segment.pointAt (segment.projectionParameter slope reading))).re = reading := by
  rewrite [pointAt_projection]
  exact Interval.ConvexCombination.segmentParameter_interpolates _ _ _ inside

/-- A nonstationary projected segment has only one original parameter at a prescribed contained reading. -/
theorem projectionParameter_unique {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope reading : Coordinate) (inside : (segment.projectionBounds slope).Contains reading)
    (nonstationary : (Rotation.rotate slope start).re ≠ (Rotation.rotate slope finish).re)
    (parameter : Coordinate) (hits : (Rotation.rotate slope (segment.pointAt parameter)).re = reading) :
    parameter = segment.projectionParameter slope reading := by
  rewrite [pointAt_projection] at hits
  exact Interval.ConvexCombination.parameter_eq_of_interpolation nonstationary
    (hits.trans (Interval.ConvexCombination.segmentParameter_interpolates _ _ _ inside).symm)

/-- A nonzero chart slope preserves nonstationarity of every original nonstationary axis segment.

Horizontal pieces keep their real endpoint difference. Vertical pieces
multiply the imaginary endpoint difference by the same nonzero slope. -/
theorem projection_nonstationary {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope : Coordinate) (slopeNonzero : slope ≠ 0) (different : start ≠ finish) :
    (Rotation.rotate slope start).re ≠ (Rotation.rotate slope finish).re := by
  intro same
  rewrite [Rotation.rotate_real, Rotation.rotate_real] at same
  apply different
  cases segment with
  | horizontal first last height =>
      apply Gaussian.Basic.ext
      · change first = last
        calc
          first = (first + slope * height) - slope * height := by ring1
          _ = (last + slope * height) - slope * height := congrArg (fun value => value - slope * height) same
          _ = last := by ring1
      · rfl
  | vertical real first last =>
      apply Gaussian.Basic.ext
      · rfl
      · change first = last
        apply Fraction.Field.mul_right_cancel_of_ne slopeNonzero
        calc
          first * slope = (real + slope * first) - real := by ring1
          _ = (real + slope * last) - real := congrArg (fun value => value - real) same
          _ = last * slope := by ring1

/-- An original unit-interval parameter attaining one prescribed real reading in a retained projection chart. -/
abbrev ProjectionCollision {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope reading : Coordinate) :=
  {parameter : Coordinate // 0 ≤ parameter ∧ parameter ≤ 1 ∧
    (Rotation.rotate slope (segment.pointAt parameter)).re = reading}

namespace ProjectionCollision

/-- Retain an original displayed unit parameter at its same actual projection reading.

The parameter and original endpoint-indexed segment are retained directly.
Its own exact projection reading supplies the collision equation, including
a stationary projection for which the affine inverse is not unique. -/
@[expose] def ofParameter {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope parameter : Coordinate) (bounds : 0 ≤ parameter ∧ parameter ≤ 1) :
    ProjectionCollision segment slope (Rotation.rotate slope (segment.pointAt parameter)).re :=
  ⟨parameter, bounds.1, bounds.2, rfl⟩

/-- Construct the original projected collision at the computed parameter of a contained reading. -/
@[expose] def ofContainedReading {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope reading : Coordinate) (inside : (segment.projectionBounds slope).Contains reading) :
    ProjectionCollision segment slope reading :=
  let parameter := segment.projectionParameter slope reading
  let retained := segment.projectionParameter_bounds slope reading inside
  ⟨parameter, retained.1, retained.2, segment.projectionParameter_hits slope reading inside⟩

/-- A collision constructed from the original projected interval retains that same computed parameter. -/
theorem ofContainedReading_parameter {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope reading : Coordinate) (inside : (segment.projectionBounds slope).Contains reading) :
    (ofContainedReading segment slope reading inside).val = segment.projectionParameter slope reading := rfl

end ProjectionCollision

/-- A positive cached distance from a prescribed reading to the original projected endpoint interval.

The retained segment, slope and reading index the actual interval. Its
exact computed gap is retained together with positivity; whole-segment
containment transports that same cached gap to every original parameter. -/
abbrev ProjectionClearance {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope reading : Coordinate) :=
  {value : Coordinate // value = Interval.Gap.gapFrom (segment.projectionBounds slope) reading ∧ 0 < value}

namespace ProjectionClearance

/-- Read the actual cached positive gap of the original projected endpoint interval. -/
@[expose] def gap {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (clearance : ProjectionClearance segment slope reading) : Coordinate := clearance.val

/-- The cached projection gap is the exact original endpoint-interval gap from the same prescribed reading. -/
theorem gap_eq {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (clearance : ProjectionClearance segment slope reading) :
    clearance.gap = Interval.Gap.gapFrom (segment.projectionBounds slope) reading := clearance.property.1

/-- The same cached original projection gap is strictly positive. -/
theorem positive {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (clearance : ProjectionClearance segment slope reading) : 0 < clearance.gap := clearance.property.2

/-- Compute the exact original projection clearance when its endpoint interval excludes the prescribed reading. -/
@[expose] def ofNotContained {start finish : Gaussian} (segment : AxisSegment start finish) (slope reading : Coordinate)
    (outside : ¬ (segment.projectionBounds slope).Contains reading) : ProjectionClearance segment slope reading :=
  ⟨Interval.Gap.gapFrom (segment.projectionBounds slope) reading, rfl,
    Interval.Gap.gapFrom_positive _ _ outside⟩

/-- Compute the original positive projection clearance from exact avoidance on the whole unit segment.

A contained endpoint-interval reading would have the original computed
unit parameter attaining it. The supplied intrinsic avoidance excludes
that explicit witness, so the existing interval-gap constructor computes
the same actual positive clearance without a numerical bound or search.
-/
@[expose] def ofAvoidance {start finish : Gaussian} (segment : AxisSegment start finish) (slope reading : Coordinate)
    (misses : ∀ parameter : Coordinate, 0 ≤ parameter → parameter ≤ 1 →
      (Rotation.rotate slope (segment.pointAt parameter)).re ≠ reading) : ProjectionClearance segment slope reading :=
  ofNotContained segment slope reading (fun inside =>
    let collision := ProjectionCollision.ofContainedReading segment slope reading inside
    misses collision.val collision.property.1 collision.property.2.1 collision.property.2.2)

/-- Every original unit parameter's projection displacement pays the same retained positive gap. -/
theorem pays {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (clearance : ProjectionClearance segment slope reading) (parameter : Coordinate)
    (nonnegative : 0 ≤ parameter) (atMostOne : parameter ≤ 1) :
    clearance.gap ≤ Fraction.abs ((Rotation.rotate slope (segment.pointAt parameter)).re - reading) := by
  rewrite [clearance.gap_eq]
  exact Interval.Gap.gapFrom_le_abs _ _ (segment.pointAt_projection_contains slope parameter nonnegative atMostOne)

/-- The positive original projection gap excludes its prescribed reading at every original unit parameter. -/
theorem misses {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (clearance : ProjectionClearance segment slope reading) (parameter : Coordinate)
    (nonnegative : 0 ≤ parameter) (atMostOne : parameter ≤ 1) :
    (Rotation.rotate slope (segment.pointAt parameter)).re ≠ reading := by
  intro same
  have paid := clearance.pays parameter nonnegative atMostOne
  rewrite [same, show reading - reading = 0 by ring1,
    Bounds.Abs.abs_of_nonnegative (by decide : (0 : Coordinate) ≤ 0)] at paid
  exact lt_irrefl _ (clearance.positive.trans_le paid)

/-- A retained projection clearance excludes collisions in every chart paying the same original endpoint costs.

A collision in the other chart puts its reading in that original projected
endpoint interval. The interval comparison constructs an actual unit
collision in the clearance's chart, which its positive cached gap excludes.
-/
theorem excludes_collision_of_slopeCost {start finish : Gaussian} {segment : AxisSegment start finish}
    {first last reading : Coordinate} (clearance : ProjectionClearance segment first reading)
    (collision : ProjectionCollision segment last reading)
    (startFirst : Paths.Projection.slopeCost start < first) (finishFirst : Paths.Projection.slopeCost finish < first)
    (startLast : Paths.Projection.slopeCost start < last) (finishLast : Paths.Projection.slopeCost finish < last)
    (nonnegative : 0 ≤ reading) (atMostOne : reading ≤ 1) : False := by
  have inside := segment.pointAt_projection_contains last collision.val collision.property.1 collision.property.2.1
  rewrite [collision.property.2.2] at inside
  have compared := segment.projectionBounds_contains_iff_of_slopeCost first last reading
    startFirst finishFirst startLast finishLast nonnegative atMostOne
  let original := ProjectionCollision.ofContainedReading segment first reading (compared.mpr inside)
  exact clearance.misses original.val original.property.1 original.property.2.1 original.property.2.2

end ProjectionClearance

/-- Compute an original projected collision or its positive whole-segment projection clearance.

The original endpoint interval decides the result. Success retains the
computed affine parameter with its bounds and exact reading. Absence
retains that same interval's computed positive gap, which pays every
original unit parameter and excludes the prescribed reading throughout. -/
@[expose] def checkProjectionCollision {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope reading : Coordinate) :
    ProjectionCollision segment slope reading ⊕ ProjectionClearance segment slope reading :=
  let bounds := segment.projectionBounds slope
  if inside : bounds.Contains reading then
    .inl (ProjectionCollision.ofContainedReading segment slope reading inside)
  else
    .inr (ProjectionClearance.ofNotContained segment slope reading inside)

namespace ProjectionCollision

/-- A collision whose reading misses the original start has distinct projected endpoint readings. -/
theorem endpoints_distinct {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : ProjectionCollision segment slope reading)
    (startMisses : (Rotation.rotate slope start).re ≠ reading) :
    (Rotation.rotate slope start).re ≠ (Rotation.rotate slope finish).re := by
  intro same
  have hits := collision.property.2.2
  rewrite [pointAt_projection] at hits
  have collapsed : (Rotation.rotate slope start).re + collision.val *
      ((Rotation.rotate slope finish).re - (Rotation.rotate slope start).re) = (Rotation.rotate slope start).re := by
    rewrite [same]
    ring1
  exact startMisses (collapsed.symm.trans hits)

/-- An original projected event missed by the start has nonzero affine projection velocity. -/
theorem projectionVelocity_ne_zero {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (startMisses : (Rotation.rotate slope start).re ≠ reading) : segment.projectionVelocity slope ≠ 0 := by
  intro zero
  have same : (Rotation.rotate slope finish).re = (Rotation.rotate slope start).re := by
    calc
      _ = segment.projectionVelocity slope + (Rotation.rotate slope start).re := by
        unfold projectionVelocity
        ring1
      _ = 0 + (Rotation.rotate slope start).re := congrArg (fun value => value + (Rotation.rotate slope start).re) zero
      _ = (Rotation.rotate slope start).re := by ring1
  exact collision.endpoints_distinct startMisses same.symm

/-- Relative projection reading equals original parameter displacement times the same retained affine velocity.

The collision's exact reading fixes the affine anchor. Subtracting that
same anchor reading leaves the original parameter displacement multiplied
by the original endpoint-reading difference. -/
theorem relativeReading {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : ProjectionCollision segment slope reading) (parameter : Coordinate) :
    (Rotation.rotate slope (segment.pointAt parameter)).re - reading =
      (parameter - collision.val) * segment.projectionVelocity slope := by
  calc
    _ = (Rotation.rotate slope (segment.pointAt parameter)).re -
        (Rotation.rotate slope (segment.pointAt collision.val)).re :=
      congrArg (fun value => (Rotation.rotate slope (segment.pointAt parameter)).re - value) collision.property.2.2.symm
    _ = _ := by
      rewrite [pointAt_projection, pointAt_projection]
      unfold projectionVelocity
      ring1

/-- Before an original collision, positive projection velocity gives a reading below that same event. -/
theorem reading_lt_of_before_of_velocity_pos {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading) (parameter : Coordinate)
    (before : parameter < collision.val) (positive : 0 < segment.projectionVelocity slope) :
    (Rotation.rotate slope (segment.pointAt parameter)).re < reading := by
  apply Arithmetic.lt_of_sub_neg_direct
  rewrite [collision.relativeReading]
  exact Arithmetic.mul_neg_of_neg_of_pos_direct (Arithmetic.sub_neg_direct before) positive

/-- After an original collision, positive projection velocity gives a reading above that same event. -/
theorem reading_gt_of_after_of_velocity_pos {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading) (parameter : Coordinate)
    (after : collision.val < parameter) (positive : 0 < segment.projectionVelocity slope) :
    reading < (Rotation.rotate slope (segment.pointAt parameter)).re := by
  apply Arithmetic.lt_of_sub_pos_direct
  rewrite [collision.relativeReading]
  exact Arithmetic.mul_pos_direct (Arithmetic.sub_pos_direct after) positive

/-- Before an original collision, negative projection velocity gives a reading above that same event. -/
theorem reading_gt_of_before_of_velocity_neg {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading) (parameter : Coordinate)
    (before : parameter < collision.val) (negative : segment.projectionVelocity slope < 0) :
    reading < (Rotation.rotate slope (segment.pointAt parameter)).re := by
  apply Arithmetic.lt_of_sub_pos_direct
  rewrite [collision.relativeReading]
  exact Arithmetic.mul_pos_of_neg_of_neg_direct (Arithmetic.sub_neg_direct before) negative

/-- After an original collision, negative projection velocity gives a reading below that same event. -/
theorem reading_lt_of_after_of_velocity_neg {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading) (parameter : Coordinate)
    (after : collision.val < parameter) (negative : segment.projectionVelocity slope < 0) :
    (Rotation.rotate slope (segment.pointAt parameter)).re < reading := by
  apply Arithmetic.lt_of_sub_neg_direct
  rewrite [collision.relativeReading]
  exact Arithmetic.mul_neg_of_pos_of_neg_direct (Arithmetic.sub_pos_direct after) negative

/-- Every original affine parameter hitting this same reading equals the retained collision parameter.

The original endpoint readings are distinct when the start misses the
collision reading. Their exact affine inverse then identifies every hit
with the same original unit-interval collision parameter. -/
theorem parameter_eq {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : ProjectionCollision segment slope reading)
    (startMisses : (Rotation.rotate slope start).re ≠ reading) (parameter : Coordinate)
    (hits : (Rotation.rotate slope (segment.pointAt parameter)).re = reading) : parameter = collision.val := by
  have inside := segment.pointAt_projection_contains slope collision.val collision.property.1 collision.property.2.1
  rewrite [collision.property.2.2] at inside
  have different := collision.endpoints_distinct startMisses
  exact (segment.projectionParameter_unique slope reading inside different parameter hits).trans
    (segment.projectionParameter_unique slope reading inside different collision.val collision.property.2.2).symm

/-- A collision is strictly interior when the original chart misses the prescribed reading at both endpoints. -/
theorem interior {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : ProjectionCollision segment slope reading)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading) :
    0 < collision.val ∧ collision.val < 1 := by
  have notZero : collision.val ≠ 0 := by
    intro same
    have hits := collision.property.2.2
    rewrite [same, pointAt_zero] at hits
    exact startMisses hits
  have notOne : collision.val ≠ 1 := by
    intro same
    have hits := collision.property.2.2
    rewrite [same, pointAt_one] at hits
    exact finishMisses hits
  exact ⟨⟨collision.property.1,
    fun reverse => notZero (Basic.le_antisymm _ _ reverse collision.property.1)⟩,
    ⟨collision.property.2.1,
    fun reverse => notOne (Basic.le_antisymm _ _ collision.property.2.1 reverse)⟩⟩

/-- A projected collision has nonzero original imaginary height when the actual segment avoids that real branch. -/
theorem imaginary_nonzero {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : ProjectionCollision segment slope reading) (avoids : segment.Avoids (gaussian reading 0)) :
    (segment.pointAt collision.val).im ≠ 0 := by
  intro zero
  apply avoids collision.val collision.property.1 collision.property.2.1
  apply Gaussian.Basic.ext
  · have hits := collision.property.2.2
    rewrite [Rotation.rotate_real, zero, Fraction.Field.mul_zero_direct] at hits
    change (segment.pointAt collision.val).re = reading
    exact (show (segment.pointAt collision.val).re + 0 = (segment.pointAt collision.val).re by ring1) ▸ hits
  · exact zero

/-- The actual signed height above the fixed real branch is the original height times the positive chart scale. -/
theorem relativeHeight {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : ProjectionCollision segment slope reading) :
    (Rotation.rotate slope (segment.pointAt collision.val)).im + slope * reading =
      (1 + slope ^ 2) * (segment.pointAt collision.val).im := by
  have equalReadings : (Rotation.rotate slope (segment.pointAt collision.val)).re =
      (Rotation.rotate slope (gaussian reading 0)).re := by
    calc
      _ = reading := collision.property.2.2
      _ = (Rotation.rotate slope (gaussian reading 0)).re := by
        rewrite [Rotation.rotate_real]
        change reading = reading + slope * 0
        ring1
  have relative := Rotation.relative_imaginary_of_real_eq slope equalReadings
  rewrite [Rotation.rotate_imaginary slope (gaussian reading 0)] at relative
  change _ - (0 - slope * reading) = (1 + slope ^ 2) * (_ - 0) at relative
  calc
    _ = (Rotation.rotate slope (segment.pointAt collision.val)).im - (0 - slope * reading) := by ring1
    _ = (1 + slope ^ 2) * ((segment.pointAt collision.val).im - 0) := relative
    _ = _ := by ring1

/-- The positive chart scale preserves the strict sign of the original collision's imaginary coordinate. -/
theorem relativeHeight_pos_iff {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate}
    (collision : ProjectionCollision segment slope reading) :
    (0 < (Rotation.rotate slope (segment.pointAt collision.val)).im + slope * reading ↔
      0 < (segment.pointAt collision.val).im) := by
  rewrite [collision.relativeHeight]
  exact ⟨fun positive => Arithmetic.pos_of_mul_pos_right_direct positive (Rotation.scale_positive slope).le,
    fun positive => Arithmetic.mul_pos_direct (Rotation.scale_positive slope) positive⟩

/-- Collisions of the same original axis with the same reading have equal imaginary signs in positive charts.

Horizontal axes retain one imaginary coordinate. At a vertical collision,
the positive slope times the actual imaginary coordinate is the reading
minus the same fixed real coordinate, so both charts give the same sign.
-/
theorem imaginary_pos_iff_of_positive_slopes {start finish : Gaussian} {segment : AxisSegment start finish}
    {first last reading : Coordinate} (left : ProjectionCollision segment first reading)
    (right : ProjectionCollision segment last reading) (firstPositive : 0 < first) (lastPositive : 0 < last) :
    (0 < (segment.pointAt left.val).im ↔ 0 < (segment.pointAt right.val).im) := by
  cases segment with
  | horizontal source target height => exact Iff.rfl
  | vertical real source target =>
      have leftReading : first * ((AxisSegment.vertical real source target).pointAt left.val).im = reading - real := by
        have hits := left.property.2.2
        rewrite [Rotation.rotate_real] at hits
        change real + first * ((AxisSegment.vertical real source target).pointAt left.val).im = reading at hits
        calc
          _ = (real + first * ((AxisSegment.vertical real source target).pointAt left.val).im) - real := by ring1
          _ = reading - real := congrArg (fun value => value - real) hits
      have rightReading : last * ((AxisSegment.vertical real source target).pointAt right.val).im = reading - real := by
        have hits := right.property.2.2
        rewrite [Rotation.rotate_real] at hits
        change real + last * ((AxisSegment.vertical real source target).pointAt right.val).im = reading at hits
        calc
          _ = (real + last * ((AxisSegment.vertical real source target).pointAt right.val).im) - real := by ring1
          _ = reading - real := congrArg (fun value => value - real) hits
      constructor
      · intro positive
        have scaled := Arithmetic.mul_pos_direct firstPositive positive
        have transported := (leftReading.trans rightReading.symm) ▸ scaled
        exact Arithmetic.pos_of_mul_pos_right_direct transported lastPositive.le
      · intro positive
        have scaled := Arithmetic.mul_pos_direct lastPositive positive
        have transported := (rightReading.trans leftReading.symm) ▸ scaled
        exact Arithmetic.pos_of_mul_pos_right_direct transported firstPositive.le

/-- Intrinsic branch avoidance makes the collision's actual signed height nonzero in the retained chart. -/
theorem relativeHeight_nonzero {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoids : segment.Avoids (gaussian reading 0)) :
    (Rotation.rotate slope (segment.pointAt collision.val)).im + slope * reading ≠ 0 := by
  rewrite [collision.relativeHeight]
  exact Fraction.Field.mul_ne_zero_direct (Rotation.scale_positive slope).ne' (collision.imaginary_nonzero avoids)

end ProjectionCollision

end Purelib.Curves.Legendre.Paths.AxisSegment
