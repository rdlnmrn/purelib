module

import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Height
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Samples
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Crossing
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Overlap
import Purelib.RootIsolation.Progressive.Braid.Projected.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.Data.Rat.Interval.Basic
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
import Purelib.Curves.Legendre.Paths.AxisSegment.Window
import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Curves.Legendre.Paths.Frame.Gaps
import Purelib.Curves.Legendre.Paths.Preparation
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Geometry.Rational.Box.Rotation

/-! # Binding height-derived caps in the original retained crossing chart -/

namespace TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Height

open Purelib.Curves.Legendre.Paths
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Coordinates
open Purelib.Geometry.Rational

/-- The same original horizontal branch crosses reading zero in the retained slope-three chart. -/
def segment : AxisSegment (gaussian (-(23 / 8)) 1) (gaussian (-(25 / 8)) 1) :=
  .horizontal (-(23 / 8)) (-(25 / 8)) 1

/-- The original segment intrinsically excludes zero at every unit parameter. -/
theorem avoidsZero : segment.Avoids 0 := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (1 : Coordinate) ≠ 0) imaginary

/-- The original segment intrinsically excludes one at every unit parameter. -/
theorem avoidsOne : segment.Avoids 1 := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (1 : Coordinate) ≠ 0) imaginary

/-- The original event parameter is computed from its actual projected endpoint interval. -/
def collision : segment.ProjectionCollision 3 0 :=
  AxisSegment.ProjectionCollision.ofContainedReading segment 3 0 (by constructor <;> decide +kernel)

/-- The positive cap is computed from the original collision height and same retained slope. -/
def cap : {value : Coordinate // 0 < value} := collision.heightCap avoidsZero

/-- The unit reading allocation binds the actual computed slope-three cap at one sixteenth. -/
example : cap.val = 1 / 16 := by decide +kernel

/-- The actual signed collision-height magnitude is ten in the same original chart. -/
example : collision.heightMagnitude = 10 := by decide +kernel

/-- Prepare the original window from intrinsic avoidance and the fixed zero event, with no supplied cap. -/
def window : AxisSegment.ProjectionCollision.OwnerWindow collision :=
  collision.prepareCrossingWindow avoidsZero avoidsOne (Or.inl rfl) (by decide) (by decide)

/-- The crossing producer consumes the same computed cap in the original owner-window constructor. -/
example : window.frame =
    (collision.prepareOwnerWindow avoidsZero avoidsOne cap).frame := rfl

/-- The same capped original window has both actual endpoints missing the retained collision reading. -/
example : (Rotation.rotate 3 (segment.pointAt window.parameters.lower)).re ≠ 0 ∧
    (Rotation.rotate 3 (segment.pointAt window.parameters.upper)).re ≠ 0 :=
  collision.prepareOwnerWindow_endpoints_miss avoidsZero avoidsOne (by decide) (by decide) cap

/-- The original anchor owner's actual box consumes the binding cap instead of its broader default radius. -/
example : (window.frame.rootOwner 1).box.xLower = -(49 / 16) := by
  have same : window.frame =
      (collision.prepareOwnerWindow avoidsZero avoidsOne cap).frame := rfl
  rewrite [same, AxisSegment.ProjectionCollision.prepareOwnerWindow_frame (cap := cap)]
  unfold Frame.rootOwner
  rewrite [Frame.ofParameter_owner_box (cap := cap)]
  decide +kernel

/-- The same internally capped original radius pays the actual two-box vertical width. -/
example : 2 * ((1 + Fraction.abs 3) * branchRadius (segment.pointAt collision.val)
    (projectionSlope (segment.pointAt collision.val)) cap) < collision.heightMagnitude :=
  collision.heightCap_pays_width avoidsZero _ (branchRadius_le_cap _ _ cap)

/-- That same radius bounds each original rotated enclosure's half-width by a quarter. -/
example : (1 + Fraction.abs 3) * branchRadius (segment.pointAt collision.val)
    (projectionSlope (segment.pointAt collision.val)) cap ≤ 1 / 4 :=
  collision.heightCap_width_le_quarter avoidsZero _ (branchRadius_le_cap _ _ cap)

/-- The actual slope-three anchor boxes retain the strict fixed-below-moving order of the positive collision. -/
example : (Box.Rotation.enclosure 3 (window.frame.rootOwner 0).box).yUpper <
    (Box.Rotation.enclosure 3 (window.frame.rootOwner 1).box).yLower :=
  collision.prepareCrossingWindow_height_above avoidsZero avoidsOne (Or.inl rfl) (by decide) (by decide)
    avoidsZero 0 rfl (by decide +kernel)

/-- The same internally computed window excludes the other fixed reading at every retained original parameter. -/
example (parameter : Coordinate) (inside : window.parameters.Contains parameter) :
    (Rotation.rotate 3 (segment.pointAt parameter)).re ≠ 1 :=
  collision.prepareCrossingWindow_misses_other_reading avoidsZero avoidsOne (Or.inl rfl) (by decide) (by decide)
    avoidsZero parameter inside

/-- Both endpoint sample frames are computed from intrinsic avoidance without supplied endpoint chart certificates. -/
def prepared : AxisSegment.ProjectionCollision.WindowSamples collision :=
  collision.prepareCrossingSamples avoidsZero avoidsOne (Or.inl rfl) (by decide) (by decide)

/-- Automatic preparation retains the complete same original height-derived window. -/
example : prepared.1 = window := collision.prepareCrossingSamples_window _ _ _ _ _

/-- The computed original endpoint samples share the same actual retained projection chart. -/
example : prepared.2.1.val.projectionSlope = 3 ∧ prepared.2.2.val.projectionSlope = 3 :=
  ⟨prepared.2.1.property.1, prepared.2.2.property.1⟩

/-- Both computed sample families refine the original window owners at every same logical branch label. -/
example (label : Fin 3) :
    (prepared.2.1.val.rootOwner label).box.Refines (prepared.1.frame.rootOwner label).box ∧
      (prepared.2.2.val.rootOwner label).box.Refines (prepared.1.frame.rootOwner label).box :=
  ⟨prepared.2.1.property.2.2.1 label, prepared.2.2.property.2.2.1 label⟩

/-- Materialize the same original bridge family between the two automatically computed endpoint sample parameters. -/
def bridges : AxisSegment.ProjectionCollision.OwnerWindow.BridgesAt prepared.1
    prepared.1.parameters.lower prepared.1.parameters.upper :=
  prepared.1.bridgesAt _ _ ⟨le_rfl, prepared.1.parameters.valid⟩ ⟨prepared.1.parameters.valid, le_rfl⟩

/-- The actual retained overlap bridges use the same original owner boxes at their computed projected positions. -/
example (position : Fin 3) :
    ((bridges.chamberOverlap prepared.2.1 prepared.2.2 ⟨le_rfl, prepared.1.parameters.valid⟩
      ⟨prepared.1.parameters.valid, le_rfl⟩).bridge
        ((bridges.sourceFrame prepared.2.1 ⟨le_rfl, prepared.1.parameters.valid⟩).projected.ownerIndex position)).box =
      (prepared.1.frame.rootOwner
        ((branchOrder (segment.pointAt prepared.1.parameters.lower) 3).forward position)).box :=
  bridges.chamberOverlap_bridge_box_at_position _ _ _ _ position

/-- The same computed generator transports the actual original chamber-owner matching in projected position order. -/
example (position : Fin 3) :
    (bridges.chamberOverlap prepared.2.1 prepared.2.2 ⟨le_rfl, prepared.1.parameters.valid⟩
      ⟨prepared.1.parameters.valid, le_rfl⟩).matching.forward
        ((bridges.sourceFrame prepared.2.1 ⟨le_rfl, prepared.1.parameters.valid⟩).projected.ownerIndex position) =
      (bridges.targetFrame prepared.2.2 ⟨prepared.1.parameters.valid, le_rfl⟩).projected.ownerIndex
        (collision.generator.permutation.forward position) :=
  bridges.chamberOverlap_matching_positions prepared.2.1 prepared.2.2
    ⟨le_rfl, prepared.1.parameters.valid⟩ ⟨prepared.1.parameters.valid, le_rfl⟩ collision.generator.permutation
    (fun selected => collision.crossingWindow_orders_permutation
      avoidsZero avoidsOne (Or.inl rfl) (by decide) (by decide) avoidsZero selected) position

namespace Lower

/-- The original branch crosses reading zero at negative height in the same slope-three chart. -/
def segment : AxisSegment (gaussian (25 / 8) (-1)) (gaussian (23 / 8) (-1)) :=
  .horizontal (25 / 8) (23 / 8) (-1)

/-- The original negative-height segment intrinsically excludes zero. -/
theorem avoidsZero : segment.Avoids 0 := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (-1 : Coordinate) ≠ 0) imaginary

/-- The original negative-height segment intrinsically excludes one. -/
theorem avoidsOne : segment.Avoids 1 := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (-1 : Coordinate) ≠ 0) imaginary

/-- Compute the original negative-height zero event from the same chart's exact endpoint interval. -/
def collision : segment.ProjectionCollision 3 0 :=
  AxisSegment.ProjectionCollision.ofContainedReading segment 3 0 (by constructor <;> decide +kernel)

/-- Prepare the same original owner-window objects from the negative-height event and intrinsic avoidance. -/
def window : AxisSegment.ProjectionCollision.OwnerWindow collision :=
  collision.prepareCrossingWindow avoidsZero avoidsOne (Or.inl rfl) (by decide +kernel) (by decide +kernel)

/-- The actual slope-three boxes retain the strict moving-below-fixed order of the negative collision. -/
example : (Box.Rotation.enclosure 3 (window.frame.rootOwner 1).box).yUpper <
    (Box.Rotation.enclosure 3 (window.frame.rootOwner 0).box).yLower :=
  collision.prepareCrossingWindow_height_below avoidsZero avoidsOne (Or.inl rfl) (by decide +kernel) (by decide +kernel)
    avoidsZero 0 rfl (by decide +kernel)

end Lower

namespace TwoEvents

/-- The original vertical segment crosses both projected fixed readings while keeping its actual real coordinate. -/
def segment : AxisSegment (gaussian (-1 / 2) (-1)) (gaussian (-1 / 2) 2) := .vertical (-1 / 2) (-1) 2

/-- The original fixed negative real coordinate excludes the physical branch zero at every parameter. -/
theorem avoidsZero : segment.Avoids 0 := by
  intro parameter _ _ same
  have real := congrArg (fun point : Gaussian => point.re) same
  exact (by decide : (-1 / 2 : Coordinate) ≠ 0) real

/-- The same original fixed real coordinate excludes the physical branch one at every parameter. -/
theorem avoidsOne : segment.Avoids 1 := by
  intro parameter _ _ same
  have real := congrArg (fun point : Gaussian => point.re) same
  exact (by decide : (-1 / 2 : Coordinate) ≠ 1) real

/-- The exact original checker computes the zero collision in its retained slope-one chart. -/
def zero : segment.ProjectionCollision 1 0 :=
  AxisSegment.ProjectionCollision.ofContainedReading segment 1 0 (by constructor <;> decide +kernel)

/-- The exact original checker computes the one collision in the same retained chart. -/
def one : segment.ProjectionCollision 1 1 :=
  AxisSegment.ProjectionCollision.ofContainedReading segment 1 1 (by constructor <;> decide +kernel)

/-- Both original event parameters retain the exact original affine inverse. -/
example : zero.val = 1 / 2 ∧ one.val = 5 / 6 := by constructor <;> decide +kernel

/-- The original zero-crossing window is prepared from its event and intrinsic physical avoidance. -/
def zeroWindow : AxisSegment.ProjectionCollision.OwnerWindow zero :=
  zero.prepareCrossingWindow avoidsZero avoidsOne (Or.inl rfl) (by decide +kernel) (by decide +kernel)

/-- The original one-crossing window keeps its own event, parameter and actual root-derived data. -/
def oneWindow : AxisSegment.ProjectionCollision.OwnerWindow one :=
  one.prepareCrossingWindow avoidsZero avoidsOne (Or.inr rfl) (by decide +kernel) (by decide +kernel)

/-- The actual independently prepared windows are strictly disjoint in the original positive parameter order. -/
example : zeroWindow.parameters.upper < oneWindow.parameters.lower :=
  zero.prepareCrossingWindows_order_of_velocity_pos one avoidsZero avoidsOne
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Reverse the original axis direction while retaining the same physical branch-avoidance data. -/
def reversed := segment.reverse

/-- The original reversed checker computes its actual zero event. -/
def reverseZero : reversed.ProjectionCollision 1 0 :=
  AxisSegment.ProjectionCollision.ofContainedReading reversed 1 0 (by constructor <;> decide +kernel)

/-- The original reversed checker computes its actual one event. -/
def reverseOne : reversed.ProjectionCollision 1 1 :=
  AxisSegment.ProjectionCollision.ofContainedReading reversed 1 1 (by constructor <;> decide +kernel)

/-- The reversed original event parameters retain the affine complementary values. -/
example : reverseZero.val = 1 / 2 ∧ reverseOne.val = 1 / 6 := by constructor <;> decide +kernel

/-- Prepare the reversed zero window using the same original avoidance transports. -/
def reverseZeroWindow : AxisSegment.ProjectionCollision.OwnerWindow reverseZero :=
  reverseZero.prepareCrossingWindow avoidsZero.reverse avoidsOne.reverse (Or.inl rfl)
    (by decide +kernel) (by decide +kernel)

/-- Prepare the reversed one window using the same original avoidance transports. -/
def reverseOneWindow : AxisSegment.ProjectionCollision.OwnerWindow reverseOne :=
  reverseOne.prepareCrossingWindow avoidsZero.reverse avoidsOne.reverse (Or.inr rfl)
    (by decide +kernel) (by decide +kernel)

/-- Negative original velocity orders the actual one window before the actual zero window, with a strict gap. -/
example : reverseOneWindow.parameters.upper < reverseZeroWindow.parameters.lower :=
  reverseZero.prepareCrossingWindows_order_of_velocity_neg reverseOne avoidsZero.reverse avoidsOne.reverse
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end TwoEvents

end TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Height
