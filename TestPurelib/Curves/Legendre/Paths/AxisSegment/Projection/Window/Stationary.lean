module

import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Stationary
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Overlap
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Samples
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Bridges
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
import Purelib.Curves.Legendre.Paths.AxisSegment.Window
import Purelib.Curves.Legendre.Paths.Preparation
import Purelib.Curves.Legendre.Paths
import Purelib.Geometry.Rational.Box.Rotation
import Purelib.RootIsolation.Progressive.Braid.Projected.Overlap
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Original stationary overlaps on constant projections and stationary segments -/

namespace TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Stationary

open Purelib.Curves.Legendre.Paths
open Purelib.Geometry.Rational
open Purelib.Data.Gaussian.Coordinates
open Purelib.Data.Rat.Fraction.Order

/-- The original vertical segment has constant real projection and distinct physical endpoints. -/
def original : AxisSegment (gaussian (1 / 2) (-1 / 8)) (gaussian (1 / 2) (1 / 8)) :=
  .vertical (1 / 2) (-1 / 8) (1 / 8)

/-- Its fixed real coordinate intrinsically excludes zero at every original parameter. -/
theorem avoidsZero : original.Avoids 0 := by
  intro parameter _ _ same
  have real := congrArg (fun point : Gaussian => point.re) same
  exact (by decide : (1 / 2 : Coordinate) ≠ 0) real

/-- Its fixed real coordinate intrinsically excludes one at every original parameter. -/
theorem avoidsOne : original.Avoids 1 := by
  intro parameter _ _ same
  have real := congrArg (fun point : Gaussian => point.re) same
  exact (by decide : (1 / 2 : Coordinate) ≠ 1) real

/-- The original midpoint is retained at its own reading even though the affine projection is constant. -/
def anchor : original.ProjectionCollision 0 (Rotation.rotate 0 (original.pointAt (1 / 2))).re :=
  AxisSegment.ProjectionCollision.ofParameter original 0 (1 / 2) (by constructor <;> decide)

/-- The midpoint's displayed zero-slope chart separates its original three branch readings. -/
theorem separated : (original.pointAt anchor.val).re + 0 * (original.pointAt anchor.val).im ≠ 0 ∧
    (original.pointAt anchor.val).re + 0 * (original.pointAt anchor.val).im ≠ 1 := by
  constructor <;> decide +kernel

/-- Compute the original retained broad-owner window without endpoint-miss certificates. -/
def window : AxisSegment.ProjectionCollision.OwnerWindow anchor :=
  anchor.prepareStationaryWindow avoidsZero avoidsOne separated

/-- The actual original broad boxes are strictly ordered in the retained constant-projection chart. -/
example (left right : Fin 3) (ordered : left.val < right.val) :
    (Box.Rotation.enclosure 0 (window.frame.rootOwner
      ((branchOrder (original.pointAt anchor.val) 0).forward left)).box).xUpper <
    (Box.Rotation.enclosure 0 (window.frame.rootOwner
      ((branchOrder (original.pointAt anchor.val) 0).forward right)).box).xLower :=
  anchor.prepareStationaryWindow_xOrdered avoidsZero avoidsOne separated left right ordered

/-- Every retained original parameter keeps the computed anchor's complete branch-order bijection. -/
example (parameter : Coordinate) (inside : window.parameters.Contains parameter) :
    branchOrder (original.pointAt parameter) 0 = branchOrder (original.pointAt anchor.val) 0 :=
  anchor.prepareStationaryWindow_order avoidsZero avoidsOne separated parameter inside

/-- Compute the original stationary overlap from the same interior anchor and intrinsic branch avoidance. -/
def prepared : AxisSegment.ProjectionCollision.PreparedWindow anchor :=
  anchor.prepareStationaryOverlap avoidsZero avoidsOne separated

/-- Constant projection produces the actual original stationary event. -/
example : prepared.overlap.event = .stationary :=
  anchor.prepareStationaryOverlap_event avoidsZero avoidsOne separated

/-- Both automatically computed endpoint sample frames refine the same retained broad-owner window. -/
example (label : Fin 3) :
    (prepared.samples.2.1.val.rootOwner label).box.Refines (prepared.samples.1.frame.rootOwner label).box ∧
      (prepared.samples.2.2.val.rootOwner label).box.Refines (prepared.samples.1.frame.rootOwner label).box :=
  ⟨prepared.samples.2.1.property.2.2.1 label, prepared.samples.2.2.property.2.2.1 label⟩

/-- The original chamber-owner matching preserves the actual original projected positions. -/
example (position : Fin 3) : prepared.overlap.chamberOverlap.matching.forward
    (prepared.sourceFrame.projected.ownerIndex position) = prepared.targetFrame.projected.ownerIndex position :=
  prepared.overlap.matching_order position

/-- The original overlap retains its same complete cached bridge family and chamber overlap. -/
example : prepared.overlap.chamberOverlap = prepared.bridges.chamberOverlap prepared.samples.2.1 prepared.samples.2.2
    ⟨le_rfl, prepared.samples.1.parameters.valid⟩ ⟨prepared.samples.1.parameters.valid, le_rfl⟩ :=
  anchor.prepareStationaryOverlap_chamber avoidsZero avoidsOne separated

/-- The same original overlap constructs a safe segment with internally computed bridge clearance. -/
def segment : Segment prepared.sourceFrame prepared.targetFrame := prepared.toSegment

/-- Its retained geometry is the original affine restriction between the same window endpoints. -/
example : segment.geometry =
    original.restrict prepared.samples.1.parameters.lower prepared.samples.1.parameters.upper := rfl

/-- Its original projected-overlap certificate is the same complete cached stationary overlap. -/
example : segment.projection = prepared.overlap := prepared.toSegment_projection

/-- Deriving safety from the retained window preserves the complete original axis-checker clearance record. -/
example : segment.safe = AxisSegment.Safe.ofAvoidance
    (original.restrict prepared.samples.1.parameters.lower prepared.samples.1.parameters.upper)
    (avoidsZero.restrict _ _
      ⟨prepared.samples.1.bounds.1, prepared.samples.1.parameters.valid.trans prepared.samples.1.bounds.2.2⟩
      ⟨prepared.samples.1.bounds.1.trans prepared.samples.1.parameters.valid, prepared.samples.1.bounds.2.2⟩)
    (avoidsOne.restrict _ _
      ⟨prepared.samples.1.bounds.1, prepared.samples.1.parameters.valid.trans prepared.samples.1.bounds.2.2⟩
      ⟨prepared.samples.1.bounds.1.trans prepared.samples.1.parameters.valid, prepared.samples.1.bounds.2.2⟩) := rfl

/-- Compute the original initial endpoint piece with its projection chart selected internally. -/
def initial := original.prepareStationaryAt 0 (by constructor <;> decide) avoidsZero avoidsOne

/-- The initial piece starts at the actual original parameter zero. -/
example : initial.samples.1.parameters.lower = 0 := original.prepareStationaryAt_lower_zero avoidsZero avoidsOne

/-- The initial piece retains an original stationary event without a caller chart or order certificate. -/
example : initial.overlap.event = .stationary :=
  original.prepareStationaryAt_event 0 (by constructor <;> decide) avoidsZero avoidsOne

/-- Its safe-segment constructor retains the original endpoint piece's same overlap and paid original owners. -/
example : Segment initial.sourceFrame initial.targetFrame := initial.toSegment

/-- Compute the original final endpoint piece from the same intrinsic branch avoidance. -/
def final := original.prepareStationaryAt 1 (by constructor <;> decide) avoidsZero avoidsOne

/-- The final piece ends at the actual original parameter one. -/
example : final.samples.1.parameters.upper = 1 := original.prepareStationaryAt_upper_one avoidsZero avoidsOne

/-- The final endpoint piece also retains its internally derived original stationary event. -/
example : final.overlap.event = .stationary :=
  original.prepareStationaryAt_event 1 (by constructor <;> decide) avoidsZero avoidsOne

/-- Its original safe segment uses the same cached endpoint samples and original bridge family. -/
example : Segment final.sourceFrame final.targetFrame := final.toSegment

namespace Fixed

/-- The original horizontal segment is physically stationary at a regular parameter. -/
def original : AxisSegment (gaussian (1 / 2) 1) (gaussian (1 / 2) 1) := .horizontal (1 / 2) (1 / 2) 1

/-- Its constant imaginary coordinate excludes zero everywhere. -/
theorem avoidsZero : original.Avoids 0 := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (1 : Coordinate) ≠ 0) imaginary

/-- Its constant imaginary coordinate excludes one everywhere. -/
theorem avoidsOne : original.Avoids 1 := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (1 : Coordinate) ≠ 0) imaginary

/-- The original stationary segment retains an interior midpoint at its own exact original reading. -/
def anchor : original.ProjectionCollision 0 (Rotation.rotate 0 (original.pointAt (1 / 2))).re :=
  AxisSegment.ProjectionCollision.ofParameter original 0 (1 / 2) (by constructor <;> decide)

/-- Compute the same original overlap when both physical and projected motions are stationary. -/
def prepared : AxisSegment.ProjectionCollision.PreparedWindow anchor :=
  anchor.prepareStationaryOverlap avoidsZero avoidsOne
    (by constructor <;> decide +kernel)

/-- A physically stationary original segment has the actual original stationary projected event. -/
example : prepared.overlap.event = .stationary :=
  anchor.prepareStationaryOverlap_event avoidsZero avoidsOne
    (by constructor <;> decide +kernel)

/-- The physically stationary original segment also retains a computed original safe segment. -/
example : Segment prepared.sourceFrame prepared.targetFrame := prepared.toSegment

end Fixed

namespace ProjectionTie

/-- The original vertical segment has a zero-reading real-projection tie at every parameter. -/
def original : AxisSegment (gaussian 0 1) (gaussian 0 2) := .vertical 0 1 2

/-- Positive original imaginary coordinates exclude the actual singular zero branch. -/
theorem avoidsZero : original.Avoids 0 := by
  intro parameter nonnegative _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  change (1 : Coordinate) + (2 - 1) * parameter = 0 at imaginary
  rewrite [show (1 : Coordinate) + (2 - 1) * parameter = 1 + parameter by ring1] at imaginary
  exact (Arithmetic.add_pos_of_pos_of_nonneg_direct
    (by decide : (0 : Coordinate) < 1) nonnegative).ne' imaginary

/-- The original fixed real coordinate excludes the actual singular one branch. -/
theorem avoidsOne : original.Avoids 1 := by
  intro parameter _ _ same
  have real := congrArg (fun point : Gaussian => point.re) same
  exact (by decide : (0 : Coordinate) ≠ 1) real

/-- Compute the initial original piece despite its constant tied real projection. -/
def initial := original.prepareStationaryAt 0 (by constructor <;> decide) avoidsZero avoidsOne

/-- The same computed source samples use the internally selected separating slope two. -/
example : initial.samples.2.1.val.projectionSlope = 2 := by
  calc
    _ = projectionSlope (original.pointAt 0) := initial.samples.2.1.property.1
    _ = 2 := by decide +kernel

/-- The original tied-projection initial piece retains its exact original initial unit parameter. -/
example : initial.samples.1.parameters.lower = 0 := original.prepareStationaryAt_lower_zero avoidsZero avoidsOne

/-- It produces a safe original segment without any supplied chart, frame or order certificate. -/
example : Segment initial.sourceFrame initial.targetFrame := initial.toSegment

/-- Compute the final original piece using its actual original endpoint's selected chart. -/
def final := original.prepareStationaryAt 1 (by constructor <;> decide) avoidsZero avoidsOne

/-- The final samples retain the internally selected slope one at the actual parameter two times imaginary unit. -/
example : final.samples.2.2.val.projectionSlope = 1 := by
  calc
    _ = projectionSlope (original.pointAt 1) := final.samples.2.2.property.1
    _ = 1 := by decide +kernel

/-- The original tied-projection final piece retains its exact original final unit parameter. -/
example : final.samples.1.parameters.upper = 1 := original.prepareStationaryAt_upper_one avoidsZero avoidsOne

/-- The final original overlap is stationary in the same internally computed chart as its two endpoint frames. -/
example : final.overlap.event = .stationary :=
  original.prepareStationaryAt_event 1 (by constructor <;> decide) avoidsZero avoidsOne

end ProjectionTie

namespace SharedChart

/-- The original fixed segment lies near a box face while its slope-one projection is well separated. -/
def original : AxisSegment (gaussian (21 / 100) 2) (gaussian (21 / 100) 2) :=
  .horizontal (21 / 100) (21 / 100) 2

/-- The original constant imaginary coordinate intrinsically excludes zero. -/
theorem avoidsZero : original.Avoids 0 := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (2 : Coordinate) ≠ 0) imaginary

/-- That same constant imaginary coordinate intrinsically excludes one. -/
theorem avoidsOne : original.Avoids 1 := by
  intro parameter _ _ same
  have imaginary := congrArg (fun point : Gaussian => point.im) same
  exact (by decide : (2 : Coordinate) ≠ 0) imaginary

/-- Retain the exact original midpoint reading in the displayed common slope-one chart. -/
def anchor : original.ProjectionCollision 1 (Rotation.rotate 1 (original.pointAt (1 / 2))).re :=
  AxisSegment.ProjectionCollision.ofParameter original 1 (1 / 2) (by constructor <;> decide)

/-- The same original chart separates the actual anchor branch readings. -/
theorem separated : (original.pointAt anchor.val).re + 1 * (original.pointAt anchor.val).im ≠ 0 ∧
    (original.pointAt anchor.val).re + 1 * (original.pointAt anchor.val).im ≠ 1 := by
  constructor <;> decide +kernel

/-- Compute the original broad-owner window in that same separating chart. -/
def window := anchor.prepareStationaryWindow avoidsZero avoidsOne separated

/-- The original broad anchor frame keeps the displayed common chart rather than reselecting the real projection. -/
example : window.frame.projectionSlope = 1 := by
  unfold window
  rewrite [AxisSegment.ProjectionCollision.prepareStationaryWindow_frame, Frame.ofProjection_slope]
  rfl

/-- The actual retained allowance is one twentieth, paid by the same chart radius and owner-derived sides. -/
example : window.radius = 1 / 20 := by
  unfold window
  rewrite [AxisSegment.ProjectionCollision.prepareStationaryWindow_radius]
  decide +kernel

/-- The same original window still constructs its complete stationary overlap and paid safe segment. -/
example : Segment
    (anchor.prepareStationaryOverlap avoidsZero avoidsOne separated).sourceFrame
    (anchor.prepareStationaryOverlap avoidsZero avoidsOne separated).targetFrame :=
  (anchor.prepareStationaryOverlap avoidsZero avoidsOne separated).toSegment

end SharedChart

/-- The all-input stationary producer accepts intrinsic avoidance and its separating unit anchor. -/
example {start finish : Gaussian} {source : AxisSegment start finish} {slope reading : Coordinate}
    (anchor : source.ProjectionCollision slope reading)
    (excludesZero : source.Avoids 0) (excludesOne : source.Avoids 1)
    (separated : (source.pointAt anchor.val).re + slope * (source.pointAt anchor.val).im ≠ 0 ∧
      (source.pointAt anchor.val).re + slope * (source.pointAt anchor.val).im ≠ 1) :
    AxisSegment.ProjectionCollision.PreparedWindow anchor :=
  anchor.prepareStationaryOverlap excludesZero excludesOne separated

end TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Stationary
