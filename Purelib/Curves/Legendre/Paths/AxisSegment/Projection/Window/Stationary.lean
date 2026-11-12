module

public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Overlap
public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Separation
public import Purelib.Approximation.Rational.Grid.Basic
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Samples
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window
import Purelib.Curves.Legendre.Paths.Preparation
import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Curves.Legendre.Paths.Frame.Gaps
import Purelib.Curves.Legendre.Paths
import Purelib.Geometry.Rational.Box.Rotation
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Tactic.Ring

/-!
# Original owner windows with separated projected readings

An original unit anchor has a separating chart. Its computed chart
radius caps the same original point-frame constructor. The root-derived
window retains the original anchor owners and their same side and radius
caches, and their broad boxes are strictly ordered in that retained chart.
-/

public section

namespace Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Data.Gaussian.Coordinates
open Fraction.Order

/-- Prepare the original owner window in its same separating projection chart at any original unit anchor.

Intrinsic branch avoidance computes the original frame in the displayed
separating chart. Its retained owners, gaps and side cache determine the
displacement allowance in that same chart. Constant
projections and stationary original segments are included. -/
@[expose] def prepareStationaryWindow {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (anchor : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (separated : (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 0 ∧
      (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 1) : OwnerWindow anchor :=
  OwnerWindow.ofFrame anchor (Paths.Frame.ofProjection (segment.pointAt anchor.val)
    (avoidsZero anchor.val anchor.property.1 anchor.property.2.1)
    (avoidsOne anchor.val anchor.property.1 anchor.property.2.1) slope separated)

/-- The original stationary-window frame retains its complete constructor in the same separating projection chart. -/
theorem prepareStationaryWindow_frame {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (anchor : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (separated : (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 0 ∧
      (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 1) :
    (anchor.prepareStationaryWindow avoidsZero avoidsOne separated).frame =
      Paths.Frame.ofProjection (segment.pointAt anchor.val)
        (avoidsZero anchor.val anchor.property.1 anchor.property.2.1)
        (avoidsOne anchor.val anchor.property.1 anchor.property.2.1) slope separated := rfl

/-- The original stationary window retains one quarter of its same chart's computed branch radius.

The moving root's original centered-square gap equals that chart radius.
Both cached outside sides are paid by this same retained root-owner gap,
so their original displacement minimum has this exact value. -/
theorem prepareStationaryWindow_radius {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (anchor : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (separated : (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 0 ∧
      (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 1) :
    (anchor.prepareStationaryWindow avoidsZero avoidsOne separated).radius =
      branchRadius (segment.pointAt anchor.val) slope / 4 := by
  let window := anchor.prepareStationaryWindow avoidsZero avoidsOne separated
  have sides : window.sides = window.frame.movingSides := rfl
  rewrite [window.radius_eq, sides, Paths.Frame.displacementRadius_movingSides,
    prepareStationaryWindow_frame, Paths.Frame.ofProjection_branchGap]
  rfl

/-- A projection-gap floor pays an explicit lower bound for the actual retained stationary-window allowance.

The original chart radius dominates its unit-capped gap allocation.
The exact cached displacement-radius identity transports one quarter
of that same computed scalar floor to the actual original window. -/
theorem prepareStationaryWindow_radius_lower_bound {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (anchor : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (separated : (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 0 ∧
      (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 1)
    (floor : Coordinate) (below : floor ≤ branchProjectionGap (segment.pointAt anchor.val) slope) :
    min 1 (floor / (2 * (1 + Fraction.abs slope) + 1)) / 4 ≤
      (anchor.prepareStationaryWindow avoidsZero avoidsOne separated).radius := by
  rewrite [prepareStationaryWindow_radius]
  exact Field.div_le_div_of_cross (by decide) (by decide)
    (Arithmetic.mul_le_mul_of_nonneg_right_direct (branchRadius_lower_bound _ _ _ below) (by decide))

/-- The actual original broad stationary-window owners have strict order in the same retained separating chart.

The original projection constructor retains its actual centered squares
and their same computed chart radius. Its original box-order law pays
the two-enclosure width against each increasing original projection gap. -/
theorem prepareStationaryWindow_xOrdered {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (anchor : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (separated : (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 0 ∧
      (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 1)
    (left right : Fin 3) (ordered : left.val < right.val) :
    let window := anchor.prepareStationaryWindow avoidsZero avoidsOne separated
    let order := branchOrder (segment.pointAt anchor.val) slope
    (Box.Rotation.enclosure slope (window.frame.rootOwner (order.forward left)).box).xUpper <
      (Box.Rotation.enclosure slope (window.frame.rootOwner (order.forward right)).box).xLower := by
  dsimp only
  rewrite [prepareStationaryWindow_frame]
  unfold Paths.Frame.rootOwner
  rewrite [Paths.Frame.ofProjection_owner_box, Paths.Frame.ofProjection_owner_box]
  exact branchBoxes_xOrdered _ _ separated left right ordered

/-- The same anchor order strictly orders the actual branch readings at every original stationary-window parameter.

Each actual branch stays in its same retained broad owner box. Those boxes'
strict rotated enclosure order therefore orders their actual contained
branch readings throughout the original window. -/
theorem prepareStationaryWindow_readings_ordered {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (anchor : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (separated : (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 0 ∧
      (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 1)
    (parameter : Coordinate)
    (inside : (anchor.prepareStationaryWindow avoidsZero avoidsOne separated).parameters.Contains parameter)
    (left right : Fin 3) (ordered : left.val < right.val) :
    let order := branchOrder (segment.pointAt anchor.val) slope
    (branchProjection (segment.pointAt parameter) (order.forward left) slope).re <
      (branchProjection (segment.pointAt parameter) (order.forward right) slope).re := by
  let window := anchor.prepareStationaryWindow avoidsZero avoidsOne separated
  let order := branchOrder (segment.pointAt anchor.val) slope
  have leftContains := Box.Rotation.enclosure_contains slope (window.frame.rootOwner (order.forward left)).box
    (window.root_strictContains parameter inside (order.forward left)).contains
  have rightContains := Box.Rotation.enclosure_contains slope (window.frame.rootOwner (order.forward right)).box
    (window.root_strictContains parameter inside (order.forward right)).contains
  have gap := anchor.prepareStationaryWindow_xOrdered avoidsZero avoidsOne separated left right ordered
  exact (leftContains.2.1.trans_lt gap).trans_le rightContains.1

/-- Different original logical branches have distinct actual readings throughout the same stationary window.

The retained anchor-order bijection sends the two original labels to
distinct projected positions. Their actual strict reading order in one
of the two directions excludes equality without selecting new roots. -/
theorem prepareStationaryWindow_readings_distinct {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (anchor : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (separated : (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 0 ∧
      (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 1)
    (parameter : Coordinate)
    (inside : (anchor.prepareStationaryWindow avoidsZero avoidsOne separated).parameters.Contains parameter)
    (left right : Fin 3) (different : left ≠ right) :
    (branchProjection (segment.pointAt parameter) left slope).re ≠
      (branchProjection (segment.pointAt parameter) right slope).re := by
  let order := branchOrder (segment.pointAt anchor.val) slope
  intro same
  rcases lt_trichotomy (order.backward left).val (order.backward right).val with increasing | equal | decreasing
  · have ordered := anchor.prepareStationaryWindow_readings_ordered avoidsZero avoidsOne separated parameter
      inside (order.backward left) (order.backward right) increasing
    dsimp only at ordered
    rewrite [order.forward_backward, order.forward_backward] at ordered
    exact lt_irrefl _ (ordered.trans_eq same.symm)
  · have equalIndices := Fin.ext equal
    have equalLabels := congrArg order.forward equalIndices
    rewrite [order.forward_backward, order.forward_backward] at equalLabels
    exact different equalLabels
  · have ordered := anchor.prepareStationaryWindow_readings_ordered avoidsZero avoidsOne separated parameter
      inside (order.backward right) (order.backward left) decreasing
    dsimp only at ordered
    rewrite [order.forward_backward, order.forward_backward] at ordered
    exact lt_irrefl _ (ordered.trans_eq same)

/-- Every original stationary-window parameter has the same chart's three branch readings separated.

The original fixed branch readings remain zero and one. Pairwise reading
distinctness excludes those exact values for the actual moving branch,
including constant projections and stationary original segments. -/
theorem prepareStationaryWindow_separates {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (anchor : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (separated : (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 0 ∧
      (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 1)
    (parameter : Coordinate)
    (inside : (anchor.prepareStationaryWindow avoidsZero avoidsOne separated).parameters.Contains parameter) :
    (segment.pointAt parameter).re + slope * (segment.pointAt parameter).im ≠ 0 ∧
      (segment.pointAt parameter).re + slope * (segment.pointAt parameter).im ≠ 1 := by
  have zero := anchor.prepareStationaryWindow_readings_distinct avoidsZero avoidsOne separated parameter inside
    1 0 (by decide)
  have one := anchor.prepareStationaryWindow_readings_distinct avoidsZero avoidsOne separated parameter inside
    1 2 (by decide)
  have zeroReading : (branchProjection (segment.pointAt parameter) 0 slope).re = 0 := by
    rewrite [branchProjection, branchPoint_zero, Rotation.rotate_real]
    change 0 + slope * 0 = 0
    ring1
  have oneReading : (branchProjection (segment.pointAt parameter) 2 slope).re = 1 := by
    rewrite [branchProjection, branchPoint_two, Rotation.rotate_real]
    change 1 + slope * 0 = 1
    ring1
  rewrite [zeroReading] at zero
  rewrite [oneReading] at one
  rewrite [branchProjection, branchPoint_one, Rotation.rotate_real] at zero one
  exact ⟨zero, one⟩

/-- The original computed logical branch order stays equal to its anchor order throughout the stationary window.

The actual contained readings retain the strict order of the original
anchor boxes. The moving branch therefore stays in the same one of the
three intervals separated by the original fixed zero and one readings. -/
theorem prepareStationaryWindow_order {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (anchor : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (separated : (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 0 ∧
      (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 1)
    (parameter : Coordinate)
    (inside : (anchor.prepareStationaryWindow avoidsZero avoidsOne separated).parameters.Contains parameter) :
    branchOrder (segment.pointAt parameter) slope = branchOrder (segment.pointAt anchor.val) slope := by
  have first := anchor.prepareStationaryWindow_readings_ordered avoidsZero avoidsOne separated parameter
    inside 0 1 (by decide)
  have second := anchor.prepareStationaryWindow_readings_ordered avoidsZero avoidsOne separated parameter
    inside 1 2 (by decide)
  dsimp only at first second
  have zeroReading : (branchProjection (segment.pointAt parameter) 0 slope).re = 0 := by
    rewrite [branchProjection, branchPoint_zero, Rotation.rotate_real]
    change 0 + slope * 0 = 0
    ring1
  have oneReading : (branchProjection (segment.pointAt parameter) 2 slope).re = 1 := by
    rewrite [branchProjection, branchPoint_two, Rotation.rotate_real]
    change 1 + slope * 0 = 1
    ring1
  have anchorZero : (branchProjection (segment.pointAt anchor.val) 1 slope).re ≠ 0 := by
    rewrite [branchProjection, branchPoint_one, Rotation.rotate_real]
    exact separated.1
  have anchorOne : (branchProjection (segment.pointAt anchor.val) 1 slope).re ≠ 1 := by
    rewrite [branchProjection, branchPoint_one, Rotation.rotate_real]
    exact separated.2
  rcases lt_trichotomy (branchProjection (segment.pointAt anchor.val) 1 slope).re 0 with negative | equal | positive
  · have order := branchOrder_of_negative (segment.pointAt anchor.val) slope negative
    rewrite [order] at first
    change (branchProjection (segment.pointAt parameter) 1 slope).re <
      (branchProjection (segment.pointAt parameter) 0 slope).re at first
    rewrite [zeroReading] at first
    exact (branchOrder_of_negative _ _ first).trans order.symm
  · exact (anchorZero equal).elim
  · rcases lt_trichotomy (branchProjection (segment.pointAt anchor.val) 1 slope).re 1 with between | equal | above
    · have order := branchOrder_of_between (segment.pointAt anchor.val) slope positive between
      rewrite [order] at first second
      change (branchProjection (segment.pointAt parameter) 0 slope).re <
        (branchProjection (segment.pointAt parameter) 1 slope).re at first
      change (branchProjection (segment.pointAt parameter) 1 slope).re <
        (branchProjection (segment.pointAt parameter) 2 slope).re at second
      rewrite [zeroReading] at first
      rewrite [oneReading] at second
      exact (branchOrder_of_between _ _ first second).trans order.symm
    · exact (anchorOne equal).elim
    · have order := branchOrder_of_above_one (segment.pointAt anchor.val) slope above
      rewrite [order] at second
      change (branchProjection (segment.pointAt parameter) 2 slope).re <
        (branchProjection (segment.pointAt parameter) 1 slope).re at second
      rewrite [oneReading] at second
      exact (branchOrder_of_above_one _ _ second).trans order.symm

/-- Compute the original stationary window and its two endpoint sample frames from the same intrinsic avoidance.

The original window is computed once. Its all-parameter chart separation
supplies the original sample constructor at both retained endpoints, with
caps and refinements computed from those same original broad owners. -/
@[expose] def prepareStationarySamples {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (anchor : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (separated : (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 0 ∧
      (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 1) : WindowSamples anchor := by
  let window := anchor.prepareStationaryWindow avoidsZero avoidsOne separated
  let lowerInside : window.parameters.Contains window.parameters.lower := ⟨le_rfl, window.parameters.valid⟩
  let upperInside : window.parameters.Contains window.parameters.upper := ⟨window.parameters.valid, le_rfl⟩
  exact ⟨window,
    window.samplesAt window.parameters.lower lowerInside
      (anchor.prepareStationaryWindow_separates avoidsZero avoidsOne separated _ lowerInside),
    window.samplesAt window.parameters.upper upperInside
      (anchor.prepareStationaryWindow_separates avoidsZero avoidsOne separated _ upperInside)⟩

/-- Original stationary endpoint-sample preparation retains its same complete original owner window. -/
theorem prepareStationarySamples_window {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (anchor : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (separated : (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 0 ∧
      (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 1) :
    (anchor.prepareStationarySamples avoidsZero avoidsOne separated).1 =
      anchor.prepareStationaryWindow avoidsZero avoidsOne separated := rfl

/-- Compute the original stationary projected overlap from intrinsic avoidance and an original separating unit anchor.

The original window, two sample frames and bridge family are each computed
once. The all-parameter anchor-order law makes the same original chamber
matching preserve projected positions, so the original overlap is stationary. -/
@[expose] def prepareStationaryOverlap {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (anchor : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (separated : (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 0 ∧
      (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 1) : PreparedWindow anchor := by
  let prepared := anchor.prepareStationarySamples avoidsZero avoidsOne separated
  let window := prepared.1
  let lowerInside : window.parameters.Contains window.parameters.lower := ⟨le_rfl, window.parameters.valid⟩
  let upperInside : window.parameters.Contains window.parameters.upper := ⟨window.parameters.valid, le_rfl⟩
  let bridges := window.bridgesAt window.parameters.lower window.parameters.upper lowerInside upperInside
  have lowerOrder := anchor.prepareStationaryWindow_order avoidsZero avoidsOne separated _ lowerInside
  have upperOrder := anchor.prepareStationaryWindow_order avoidsZero avoidsOne separated _ upperInside
  have orders (position : Fin 3) :
      (branchOrder (segment.pointAt window.parameters.lower) slope).forward position =
        (branchOrder (segment.pointAt window.parameters.upper) slope).forward position := by
    rewrite [lowerOrder, upperOrder]
    rfl
  exact ⟨prepared, bridges, bridges.stationaryOverlap prepared.2.1 prepared.2.2 lowerInside upperInside orders⟩

/-- Stationary overlap preparation retains the same complete original window and endpoint sample packet. -/
theorem prepareStationaryOverlap_samples {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (anchor : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (separated : (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 0 ∧
      (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 1) :
    (anchor.prepareStationaryOverlap avoidsZero avoidsOne separated).samples =
      anchor.prepareStationarySamples avoidsZero avoidsOne separated := rfl

/-- The computed original stationary projected overlap retains the original stationary event. -/
theorem prepareStationaryOverlap_event {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (anchor : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (separated : (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 0 ∧
      (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 1) :
    (anchor.prepareStationaryOverlap avoidsZero avoidsOne separated).overlap.event = .stationary := rfl

/-- The original stationary overlap retains the same complete original chamber overlap and cached bridge family. -/
theorem prepareStationaryOverlap_chamber {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (anchor : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1)
    (separated : (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 0 ∧
      (segment.pointAt anchor.val).re + slope * (segment.pointAt anchor.val).im ≠ 1) :
    let prepared := anchor.prepareStationaryOverlap avoidsZero avoidsOne separated
    prepared.overlap.chamberOverlap = prepared.bridges.chamberOverlap prepared.samples.2.1 prepared.samples.2.2
      ⟨le_rfl, prepared.samples.1.parameters.valid⟩ ⟨prepared.samples.1.parameters.valid, le_rfl⟩ := rfl

end Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision

namespace Purelib.Curves.Legendre.Paths.AxisSegment

/-- Compute an original stationary piece at any retained unit parameter from intrinsic branch avoidance.

The original point chart is selected from the actual parameter value.
Intrinsic avoidance proves its separation internally. That same chart,
anchor and original root-window constructor supply the endpoint samples,
cached bridge family and original stationary projected overlap. -/
@[expose] def prepareStationaryAt {start finish : Gaussian} (segment : AxisSegment start finish)
    (parameter : Coordinate) (bounds : 0 ≤ parameter ∧ parameter ≤ 1)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) :
    ProjectionCollision.PreparedWindow (ProjectionCollision.ofParameter segment
      (projectionSlope (segment.pointAt parameter)) parameter bounds) := by
  let anchor := ProjectionCollision.ofParameter segment (projectionSlope (segment.pointAt parameter)) parameter bounds
  have separated := projectionSlope_separates (segment.pointAt parameter)
    (avoidsZero parameter bounds.1 bounds.2) (avoidsOne parameter bounds.1 bounds.2)
  exact anchor.prepareStationaryOverlap avoidsZero avoidsOne separated

/-- Original unit-parameter preparation retains the complete original sample packet in its internally selected chart. -/
theorem prepareStationaryAt_samples {start finish : Gaussian} (segment : AxisSegment start finish)
    (parameter : Coordinate) (bounds : 0 ≤ parameter ∧ parameter ≤ 1)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) :
    (segment.prepareStationaryAt parameter bounds avoidsZero avoidsOne).samples =
      ProjectionCollision.prepareStationarySamples
        (ProjectionCollision.ofParameter segment (projectionSlope (segment.pointAt parameter)) parameter bounds)
        avoidsZero avoidsOne (projectionSlope_separates (segment.pointAt parameter)
          (avoidsZero parameter bounds.1 bounds.2) (avoidsOne parameter bounds.1 bounds.2)) := rfl

/-- Intrinsic unit-parameter preparation constructs the original stationary projected event. -/
theorem prepareStationaryAt_event {start finish : Gaussian} (segment : AxisSegment start finish)
    (parameter : Coordinate) (bounds : 0 ≤ parameter ∧ parameter ≤ 1)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) :
    (segment.prepareStationaryAt parameter bounds avoidsZero avoidsOne).overlap.event = .stationary := rfl

/-- The original stationary piece at parameter zero begins at that exact original unit endpoint. -/
theorem prepareStationaryAt_lower_zero {start finish : Gaussian} (segment : AxisSegment start finish)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) :
    (segment.prepareStationaryAt 0 (by constructor <;> decide)
      avoidsZero avoidsOne).samples.1.parameters.lower = 0 := by
  rewrite [prepareStationaryAt_samples, ProjectionCollision.prepareStationarySamples_window]
  exact ProjectionCollision.prepareOwnerWindow_lower_zero _ avoidsZero avoidsOne rfl _

/-- The original stationary piece at parameter one ends at that exact original unit endpoint. -/
theorem prepareStationaryAt_upper_one {start finish : Gaussian} (segment : AxisSegment start finish)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) :
    (segment.prepareStationaryAt 1 (by constructor <;> decide)
      avoidsZero avoidsOne).samples.1.parameters.upper = 1 := by
  rewrite [prepareStationaryAt_samples, ProjectionCollision.prepareStationarySamples_window]
  exact ProjectionCollision.prepareOwnerWindow_upper_one _ avoidsZero avoidsOne rfl _

end Purelib.Curves.Legendre.Paths.AxisSegment

namespace Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionSeparation

open Purelib.Approximation.Rational
open Purelib.Data
open Purelib.Data.Rat
open Fraction.Order

/-- Compute a positive uniform displacement-radius floor from the same two original projection clearances.

The original shared chart's enclosure cost converts its cached projection
gap into a unit-capped branch radius. One quarter of that same allocation
pays the original stationary-window allowance at every unit parameter. -/
@[expose] def radiusFloor {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) : {value : Coordinate // 0 < value} :=
  ⟨min 1 (separation.gap / (2 * (1 + Fraction.abs slope) + 1)) / 4, by
    have costNonnegative : 0 ≤ 2 * (1 + Fraction.abs slope) :=
      Arithmetic.mul_nonneg_direct (by decide)
        (Arithmetic.add_le_add_direct (by decide : (0 : Coordinate) ≤ 1) (Arithmetic.abs_nonneg_direct slope))
    have costPositive := Arithmetic.add_pos_of_nonneg_of_pos_direct costNonnegative (by decide : (0 : Coordinate) < 1)
    exact Field.div_pos_direct
      (Basic.lt_min (by decide) (Field.div_pos_direct separation.positive costPositive)) (by decide)⟩

/-- Prepare the original stationary owner window at a unit parameter from its same retained projection clearances.

The two original clearance outcomes derive physical branch avoidance and
chart separation internally. The actual anchor, chart, frame owners and
side caches remain those of the original stationary-window constructor. -/
@[expose] def windowAt {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (parameter : Coordinate)
    (bounds : 0 ≤ parameter ∧ parameter ≤ 1) :
    ProjectionCollision.OwnerWindow (ProjectionCollision.ofParameter segment slope parameter bounds) :=
  (ProjectionCollision.ofParameter segment slope parameter bounds).prepareStationaryWindow
    separation.avoidsZero separation.avoidsOne (separation.separates parameter bounds.1 bounds.2)

/-- The uniform floor pays the actual retained original window radius at every original unit parameter. -/
theorem radiusFloor_le_windowAt {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (parameter : Coordinate)
    (bounds : 0 ≤ parameter ∧ parameter ≤ 1) :
    separation.radiusFloor.val ≤ (separation.windowAt parameter bounds).radius :=
  (ProjectionCollision.ofParameter segment slope parameter bounds).prepareStationaryWindow_radius_lower_bound
    separation.avoidsZero separation.avoidsOne (separation.separates parameter bounds.1 bounds.2) separation.gap
      (separation.pays parameter bounds.1 bounds.2)

/-- Compute the original uniform parameter allocation from the actual velocity and retained positive radius floor.

The squared radius floor is divided by the original squared endpoint
velocity plus one. Its unit cap matches the original window allocation
and remains positive, including stationary original segments. -/
@[expose] def parameterAllocation {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) : {value : Coordinate // 0 < value} :=
  ⟨min 1 (separation.radiusFloor.val ^ 2 / (Gaussian.Norm.Basic.normSq (finish - start) + 1)),
    Basic.lt_min (by decide) (Field.div_pos_direct
      (Arithmetic.exact_rational_sq_pos separation.radiusFloor.property.ne')
      (Arithmetic.add_pos_of_nonneg_of_pos_direct (Gaussian.Norm.Basic.normSq_nonneg _) (by decide)))⟩

/-- Select an original finite grid count from the same computed positive uniform parameter allocation. -/
@[expose] def subdivisionCount {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) : Nat :=
  Grid.Basic.gridDenominator separation.parameterAllocation.val

/-- The computed original subdivision count is strictly positive. -/
theorem subdivisionCount_positive {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) : 0 < separation.subdivisionCount :=
  Grid.Basic.gridDenominator_pos _

/-- The computed finite grid half-mesh is strictly below its same retained original parameter allocation. -/
theorem halfMesh_lt_allocation {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) :
    (1 / 2 : Coordinate) / (separation.subdivisionCount : Coordinate) < separation.parameterAllocation.val :=
  Grid.Basic.half_reciprocal_gridDenominator_lt separation.parameterAllocation.property

/-- The uniform parameter allocation is paid by each actual original anchor window's same velocity allocation.

The retained radius floor bounds that window's actual positive radius.
Squaring, dividing by the same original incremented velocity cost and
capping at one preserves this quantitative comparison. -/
theorem parameterAllocation_le_windowAt {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (parameter : Coordinate)
    (bounds : 0 ≤ parameter ∧ parameter ≤ 1) :
    separation.parameterAllocation.val ≤
      min 1 ((separation.windowAt parameter bounds).radius ^ 2 /
        (Gaussian.Norm.Basic.normSq (finish - start) + 1)) := by
  have squares := Arithmetic.pow_le_pow_direct separation.radiusFloor.property.le
    (separation.radiusFloor_le_windowAt parameter bounds) 2
  have costPositive := Arithmetic.add_pos_of_nonneg_of_pos_direct
    (Gaussian.Norm.Basic.normSq_nonneg (finish - start)) (by decide : (0 : Coordinate) < 1)
  exact Basic.min_le_min le_rfl (Field.div_le_div_of_cross costPositive costPositive
    (Arithmetic.mul_le_mul_of_nonneg_right_direct squares costPositive.le))

end Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionSeparation
