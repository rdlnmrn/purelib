module

public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Bridges
import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Curves.Legendre.Paths.Frame.Gaps
import Purelib.Curves.Legendre.Paths.Preparation
import Purelib.Geometry.Rational.Box.Square.Centered.Rotation
import Purelib.Geometry.Rational.Box.Rotation
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Data.Rat.Bounds.Abs
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-!
# Height-derived caps for original collision windows

Intrinsic avoidance makes the actual signed collision height nonzero.
Its magnitude and the retained chart width compute a positive cap for
the original anchor-frame constructor. The same cap pays the two-box
vertical width and bounds the one-box projected half-width by a quarter.
-/

public section

namespace Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Coordinates
open Purelib.Geometry.Rational
open Fraction.Order

/-- Read the magnitude of the original collision's actual height relative to the fixed real branch. -/
@[expose] def heightMagnitude {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading) : Coordinate :=
  Fraction.abs ((Rotation.rotate slope (segment.pointAt collision.val)).im + slope * reading)

/-- Intrinsic avoidance makes the same original collision-height magnitude strictly positive. -/
theorem heightMagnitude_positive {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoids : segment.Avoids (gaussian reading 0)) : 0 < collision.heightMagnitude := by
  have nonnegative := Arithmetic.abs_nonneg_direct
    ((Rotation.rotate slope (segment.pointAt collision.val)).im + slope * reading)
  have nonzero := Bounds.Abs.abs_ne_zero_direct (collision.relativeHeight_nonzero avoids)
  exact ⟨nonnegative, fun reverse => nonzero (Basic.le_antisymm _ _ reverse nonnegative)⟩

/-- The retained chart's one-box half-width factor is strictly positive. -/
private theorem chartWidth_positive (slope : Coordinate) : 0 < 1 + Fraction.abs slope :=
  Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide) (Arithmetic.abs_nonneg_direct slope)

/-- Compute a positive original anchor-radius cap from the actual collision height and retained chart width.

The height allocation bounds the two original rotated square half-widths
strictly below the signed-height magnitude. The unit allocation bounds each
half-width by a quarter, separating the other fixed projected reading. -/
@[expose] def heightCap {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoids : segment.Avoids (gaussian reading 0)) : {value : Coordinate // 0 < value} :=
  let denominator := 4 * (1 + Fraction.abs slope)
  let positive := Arithmetic.mul_pos_direct (by decide : (0 : Coordinate) < 4)
    (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide) (Arithmetic.abs_nonneg_direct slope))
  ⟨min (1 / denominator) (collision.heightMagnitude / denominator),
    Basic.lt_min (Field.div_pos_direct (by decide) positive)
      (Field.div_pos_direct (collision.heightMagnitude_positive avoids) positive)⟩

/-- Every radius below the same computed height cap pays the actual two-box vertical enclosure width. -/
theorem heightCap_pays_width {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoids : segment.Avoids (gaussian reading 0)) (radius : Coordinate)
    (small : radius ≤ (collision.heightCap avoids).val) :
    2 * ((1 + Fraction.abs slope) * radius) < collision.heightMagnitude := by
  have denominatorPositive := Arithmetic.mul_pos_direct (by decide : (0 : Coordinate) < 4)
    (chartWidth_positive slope)
  have paid := (Field.le_div_iff_pos denominatorPositive).mp (small.trans (Basic.min_le_right _ _))
  have half : 2 * ((1 + Fraction.abs slope) * radius) ≤ collision.heightMagnitude / 2 :=
    (Field.le_div_iff_pos (by decide : (0 : Coordinate) < 2)).mpr (by
      calc
        _ = radius * (4 * (1 + Fraction.abs slope)) := by ring1
        _ ≤ collision.heightMagnitude := paid)
  exact half.trans_lt (Field.half_lt_self (collision.heightMagnitude_positive avoids))

/-- Every radius below the same computed cap has projected half-width at most one quarter. -/
theorem heightCap_width_le_quarter {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoids : segment.Avoids (gaussian reading 0)) (radius : Coordinate)
    (small : radius ≤ (collision.heightCap avoids).val) :
    (1 + Fraction.abs slope) * radius ≤ 1 / 4 := by
  have denominatorPositive := Arithmetic.mul_pos_direct (by decide : (0 : Coordinate) < 4)
    (chartWidth_positive slope)
  have paid := (Field.le_div_iff_pos denominatorPositive).mp (small.trans (Basic.min_le_left _ _))
  apply (Field.le_div_iff_pos (by decide : (0 : Coordinate) < 4)).mpr
  calc
    _ = radius * (4 * (1 + Fraction.abs slope)) := by ring1
    _ ≤ 1 := paid

/-- Prepare the original owner window with its internally computed collision-height and chart-width cap.

The actual zero or one event and intrinsic branch avoidance determine the
positive cap. The original window constructor consumes it while retaining
its original frame, side cache, radius and parameter interval owners. -/
@[expose] def prepareCrossingWindow {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading) : OwnerWindow collision := by
  have avoids : segment.Avoids (gaussian reading 0) := by
    rcases fixed with zero | one
    · subst reading
      exact avoidsZero
    · subst reading
      exact avoidsOne
  let cap := collision.heightCap avoids
  exact collision.prepareOwnerWindow avoidsZero avoidsOne cap

/-- The internally capped crossing window strictly straddles its same original affine event.

The endpoint exclusions put the collision inside the original unit interval.
Its actual positive height cap then gives strict containment in the retained
root-derived window, with no supplied cut or numerical radius.
-/
theorem prepareCrossingWindow_anchor_interior {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading) :
    let window := collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses
    window.parameters.lower < collision.val ∧ collision.val < window.parameters.upper := by
  have avoids : segment.Avoids (gaussian reading 0) := by
    rcases fixed with zero | one
    · subst reading
      exact avoidsZero
    · subst reading
      exact avoidsOne
  exact collision.prepareOwnerWindow_anchor_interior avoidsZero avoidsOne
    (collision.interior startMisses finishMisses) (collision.heightCap avoids)

/-- The computed crossing window retains the original point frame with its same height-derived cap.

Any intrinsic avoidance witness for the identified real branch computes
the same cap data. The original frame's owners, coefficient reference and
squarefree and maximality certificates are those of that same capped
point construction. -/
theorem prepareCrossingWindow_frame {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (avoids : segment.Avoids (gaussian reading 0)) :
    (collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses).frame =
      Paths.Frame.ofParameter (segment.pointAt collision.val)
        (avoidsZero collision.val collision.property.1 collision.property.2.1)
        (avoidsOne collision.val collision.property.1 collision.property.2.1) (collision.heightCap avoids) :=
  collision.prepareOwnerWindow_frame avoidsZero avoidsOne (collision.heightCap avoids)

/-- Every original labelled crossing-window owner retains its actual capped branch square. -/
theorem prepareCrossingWindow_owner_box {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (avoids : segment.Avoids (gaussian reading 0)) (label : Fin 3) :
    ((collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses).frame.rootOwner label).box =
      branchBoxes (segment.pointAt collision.val) (projectionSlope (segment.pointAt collision.val))
        (projectionSlope_separates _
          (avoidsZero collision.val collision.property.1 collision.property.2.1)
          (avoidsOne collision.val collision.property.1 collision.property.2.1))
        (cap := collision.heightCap avoids) label := by
  rewrite [prepareCrossingWindow_frame collision avoidsZero avoidsOne fixed startMisses finishMisses avoids]
  unfold Paths.Frame.rootOwner
  exact Paths.Frame.ofParameter_owner_box _ _ _ label (collision.heightCap avoids)

/-- Positive collision height orders the same original fixed-branch and moving-branch owner enclosures.

The logical label identifies the actual fixed real branch. Both retained
boxes are the original anchor squares with the computed height cap; the
strict paid height difference places the fixed box wholly below the moving
box in the retained chart. -/
theorem prepareCrossingWindow_height_above {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (avoids : segment.Avoids (gaussian reading 0)) (label : Fin 3)
    (fixedPoint : branchPoint (segment.pointAt collision.val) label = gaussian reading 0)
    (positive : 0 < (Rotation.rotate slope (segment.pointAt collision.val)).im + slope * reading) :
    let window := collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses
    (Box.Rotation.enclosure slope (window.frame.rootOwner label).box).yUpper <
      (Box.Rotation.enclosure slope (window.frame.rootOwner 1).box).yLower := by
  dsimp only
  let cap := collision.heightCap avoids
  let radius := branchRadius (segment.pointAt collision.val) (projectionSlope (segment.pointAt collision.val)) cap
  rewrite [prepareCrossingWindow_owner_box collision avoidsZero avoidsOne fixed startMisses finishMisses avoids,
    prepareCrossingWindow_owner_box collision avoidsZero avoidsOne fixed startMisses finishMisses avoids,
    branchBoxes_eq (cap := cap), branchBoxes_eq (cap := cap)]
  apply Box.Rotation.enclosure_centeredSquare_ySeparated
  rewrite [fixedPoint]
  change 2 * ((1 + Fraction.abs slope) * radius) <
    (Rotation.rotate slope (segment.pointAt collision.val)).im - (Rotation.rotate slope (gaussian reading 0)).im
  have paid := collision.heightCap_pays_width avoids radius (branchRadius_le_cap _ _ cap)
  have absolute : collision.heightMagnitude =
      (Rotation.rotate slope (segment.pointAt collision.val)).im + slope * reading :=
    Bounds.Abs.abs_of_nonnegative positive.le
  rewrite [absolute] at paid
  rewrite [Rotation.rotate_imaginary slope (gaussian reading 0)]
  change 2 * ((1 + Fraction.abs slope) * radius) <
    (Rotation.rotate slope (segment.pointAt collision.val)).im - (0 - slope * reading)
  exact paid.trans_eq (by ring1)

/-- Negative collision height orders the same original moving-branch and fixed-branch owner enclosures.

The logical label identifies the actual fixed real branch. The same capped
anchor squares retain the opposite strict vertical order: the moving box
lies wholly below the fixed box in the retained chart. -/
theorem prepareCrossingWindow_height_below {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (avoids : segment.Avoids (gaussian reading 0)) (label : Fin 3)
    (fixedPoint : branchPoint (segment.pointAt collision.val) label = gaussian reading 0)
    (negative : (Rotation.rotate slope (segment.pointAt collision.val)).im + slope * reading < 0) :
    let window := collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses
    (Box.Rotation.enclosure slope (window.frame.rootOwner 1).box).yUpper <
      (Box.Rotation.enclosure slope (window.frame.rootOwner label).box).yLower := by
  dsimp only
  let cap := collision.heightCap avoids
  let radius := branchRadius (segment.pointAt collision.val) (projectionSlope (segment.pointAt collision.val)) cap
  rewrite [prepareCrossingWindow_owner_box collision avoidsZero avoidsOne fixed startMisses finishMisses avoids,
    prepareCrossingWindow_owner_box collision avoidsZero avoidsOne fixed startMisses finishMisses avoids,
    branchBoxes_eq (cap := cap), branchBoxes_eq (cap := cap)]
  apply Box.Rotation.enclosure_centeredSquare_ySeparated
  rewrite [fixedPoint]
  change 2 * ((1 + Fraction.abs slope) * radius) <
    (Rotation.rotate slope (gaussian reading 0)).im - (Rotation.rotate slope (segment.pointAt collision.val)).im
  have paid := collision.heightCap_pays_width avoids radius (branchRadius_le_cap _ _ cap)
  have absolute : collision.heightMagnitude =
      -((Rotation.rotate slope (segment.pointAt collision.val)).im + slope * reading) :=
    Bounds.Abs.abs_of_nonpositive negative.le
  rewrite [absolute] at paid
  rewrite [Rotation.rotate_imaginary slope (gaussian reading 0)]
  change 2 * ((1 + Fraction.abs slope) * radius) <
    (0 - slope * reading) - (Rotation.rotate slope (segment.pointAt collision.val)).im
  exact paid.trans_eq (by ring1)

/-- Every original point of the computed crossing window stays within a quarter of the same event reading.

The moving branch remains inside its actual retained anchor-owner box.
That original square's rotated enclosure and the computed cap bound its
whole projected interval, including both actual window endpoints. -/
theorem prepareCrossingWindow_reading_bounds {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (avoids : segment.Avoids (gaussian reading 0)) (parameter : Coordinate)
    (inside : (collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses).parameters.Contains
      parameter) :
    reading - 1 / 4 ≤ (Rotation.rotate slope (segment.pointAt parameter)).re ∧
      (Rotation.rotate slope (segment.pointAt parameter)).re ≤ reading + 1 / 4 := by
  let window := collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses
  let cap := collision.heightCap avoids
  let radius := branchRadius (segment.pointAt collision.val) (projectionSlope (segment.pointAt collision.val)) cap
  have contained := Box.Rotation.enclosure_contains slope (window.frame.rootOwner 1).box
    (window.root_strictContains parameter inside 1).contains
  have bounds := And.intro contained.1 contained.2.1
  rewrite [prepareCrossingWindow_owner_box collision avoidsZero avoidsOne fixed startMisses finishMisses avoids,
    branchBoxes_eq (cap := cap), Box.Rotation.enclosure_centeredSquare] at bounds
  change (Rotation.rotate slope (segment.pointAt collision.val)).re - (1 + Fraction.abs slope) * radius ≤
      (Rotation.rotate slope (segment.pointAt parameter)).re ∧
    (Rotation.rotate slope (segment.pointAt parameter)).re ≤
      (Rotation.rotate slope (segment.pointAt collision.val)).re + (1 + Fraction.abs slope) * radius at bounds
  rewrite [collision.property.2.2] at bounds
  have width := collision.heightCap_width_le_quarter avoids radius (branchRadius_le_cap _ _ cap)
  exact ⟨(Arithmetic.sub_le_sub_left_direct width reading).trans bounds.1,
    bounds.2.trans (Arithmetic.add_le_add_direct le_rfl width)⟩

/-- Every original point of the computed crossing window misses the other fixed projected reading.

The quarter-unit projected interval around the identified zero or one event
excludes the opposite reading throughout the same original window. -/
theorem prepareCrossingWindow_misses_other_reading {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (avoids : segment.Avoids (gaussian reading 0)) (parameter : Coordinate)
    (inside : (collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses).parameters.Contains
      parameter) :
    (Rotation.rotate slope (segment.pointAt parameter)).re ≠ 1 - reading := by
  have bounds := collision.prepareCrossingWindow_reading_bounds avoidsZero avoidsOne fixed startMisses finishMisses
    avoids parameter inside
  intro hits
  rewrite [hits] at bounds
  rcases fixed with zero | one
  · subst reading
    have upper : (1 : Coordinate) ≤ 1 / 4 := bounds.2
    exact lt_irrefl _ ((by decide : (1 / 4 : Coordinate) < 1).trans_le upper)
  · subst reading
    have lower : (1 - 1 / 4 : Coordinate) ≤ 0 := bounds.1
    exact lt_irrefl _ ((by decide : (0 : Coordinate) < 1 - 1 / 4).trans_le lower)

/-- Both actual endpoints of the internally capped crossing window separate the three original branch projections.

Affine injectivity excludes the event reading at either endpoint. The same
quarter-unit broad-owner interval excludes the other fixed reading. Both
endpoint regularity certificates are therefore derived from the original
event and intrinsic branch avoidance. -/
theorem prepareCrossingWindow_endpoints_separate {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (avoids : segment.Avoids (gaussian reading 0)) :
    let window := collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses
    ((Rotation.rotate slope (segment.pointAt window.parameters.lower)).re ≠ 0 ∧
      (Rotation.rotate slope (segment.pointAt window.parameters.lower)).re ≠ 1) ∧
    ((Rotation.rotate slope (segment.pointAt window.parameters.upper)).re ≠ 0 ∧
      (Rotation.rotate slope (segment.pointAt window.parameters.upper)).re ≠ 1) := by
  let window := collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses
  have event := collision.prepareOwnerWindow_endpoints_miss avoidsZero avoidsOne startMisses finishMisses
    (collision.heightCap avoids)
  have lower := collision.prepareCrossingWindow_misses_other_reading avoidsZero avoidsOne fixed startMisses finishMisses
    avoids window.parameters.lower ⟨le_rfl, window.parameters.valid⟩
  have upper := collision.prepareCrossingWindow_misses_other_reading avoidsZero avoidsOne fixed startMisses finishMisses
    avoids window.parameters.upper ⟨window.parameters.valid, le_rfl⟩
  rcases fixed with zero | one
  · subst reading
    exact ⟨⟨event.1, lower⟩, ⟨event.2, upper⟩⟩
  · subst reading
    exact ⟨⟨lower, event.1⟩, ⟨upper, event.2⟩⟩

/-- The original zero-crossing window lies strictly before the one-crossing window in positive projection direction.

Every original point of the zero window projects at most one quarter,
and every point of the one window projects at least three quarters.
The same positive affine velocity transports that strict reading gap
to the actual computed upper and lower parameter endpoints.
-/
theorem prepareCrossingWindows_order_of_velocity_pos {start finish : Gaussian}
    {segment : AxisSegment start finish} {slope : Coordinate}
    (zero : ProjectionCollision segment slope 0) (one : ProjectionCollision segment slope 1)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1)
    (positive : 0 < segment.projectionVelocity slope) :
    (zero.prepareCrossingWindow avoidsZero avoidsOne (Or.inl rfl) startZero finishZero).parameters.upper <
      (one.prepareCrossingWindow avoidsZero avoidsOne (Or.inr rfl) startOne finishOne).parameters.lower := by
  let first := zero.prepareCrossingWindow avoidsZero avoidsOne (Or.inl rfl) startZero finishZero
  let last := one.prepareCrossingWindow avoidsZero avoidsOne (Or.inr rfl) startOne finishOne
  have firstReading := zero.prepareCrossingWindow_reading_bounds avoidsZero avoidsOne (Or.inl rfl)
    startZero finishZero avoidsZero first.parameters.upper ⟨first.parameters.valid, le_rfl⟩
  have lastReading := one.prepareCrossingWindow_reading_bounds avoidsZero avoidsOne (Or.inr rfl)
    startOne finishOne avoidsOne last.parameters.lower ⟨le_rfl, last.parameters.valid⟩
  apply segment.parameter_lt_of_projection_lt_of_velocity_pos
    slope first.parameters.upper last.parameters.lower positive
  exact firstReading.2.trans_lt ((by decide : (0 + 1 / 4 : Coordinate) < 1 - 1 / 4).trans_le lastReading.1)

/-- The original one-crossing window lies strictly before the zero-crossing window in negative projection direction.

Their actual quarter-unit projection ranges retain the same strict gap.
The negative affine velocity reverses reading order, so the original
one-window upper parameter precedes the zero-window lower parameter.
-/
theorem prepareCrossingWindows_order_of_velocity_neg {start finish : Gaussian}
    {segment : AxisSegment start finish} {slope : Coordinate}
    (zero : ProjectionCollision segment slope 0) (one : ProjectionCollision segment slope 1)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (startZero : (Rotation.rotate slope start).re ≠ 0) (finishZero : (Rotation.rotate slope finish).re ≠ 0)
    (startOne : (Rotation.rotate slope start).re ≠ 1) (finishOne : (Rotation.rotate slope finish).re ≠ 1)
    (negative : segment.projectionVelocity slope < 0) :
    (one.prepareCrossingWindow avoidsZero avoidsOne (Or.inr rfl) startOne finishOne).parameters.upper <
      (zero.prepareCrossingWindow avoidsZero avoidsOne (Or.inl rfl) startZero finishZero).parameters.lower := by
  let first := one.prepareCrossingWindow avoidsZero avoidsOne (Or.inr rfl) startOne finishOne
  let last := zero.prepareCrossingWindow avoidsZero avoidsOne (Or.inl rfl) startZero finishZero
  have firstReading := one.prepareCrossingWindow_reading_bounds avoidsZero avoidsOne (Or.inr rfl)
    startOne finishOne avoidsOne first.parameters.upper ⟨first.parameters.valid, le_rfl⟩
  have lastReading := zero.prepareCrossingWindow_reading_bounds avoidsZero avoidsOne (Or.inl rfl)
    startZero finishZero avoidsZero last.parameters.lower ⟨le_rfl, last.parameters.valid⟩
  apply segment.parameter_lt_of_projection_gt_of_velocity_neg
    slope first.parameters.upper last.parameters.lower negative
  exact lastReading.2.trans_lt ((by decide : (0 + 1 / 4 : Coordinate) < 1 - 1 / 4).trans_le firstReading.1)

end Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision
