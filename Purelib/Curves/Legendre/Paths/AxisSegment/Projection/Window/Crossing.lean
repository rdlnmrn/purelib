module

public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Crossing
public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Overlap
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Samples
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Height
import Purelib.Curves.Legendre.Paths.Preparation
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Rat.Interval.Basic
import Purelib.RootIsolation.Progressive.Braid.Projected.Overlap
import Purelib.RootIsolation.Progressive.Braid.Projected.Frame
import Purelib.Geometry.Rational.Box.Rotation
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Fin.Bijection.Transposition
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Topology.Knot.Braid.Event

/-!
# Signed geometry on retained original crossing bridges

The computed adjacent generator orders the actual original chamber bridges.
Their boxes are the same retained anchor owners. The original affine
direction and collision height then supply its signed vertical condition.
-/

public section

namespace Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision

open Purelib.Data
open Purelib.Data.Gaussian.Coordinates
open Purelib.Data.Fin.Bijection
open Purelib.Topology.Knot
open Purelib.RootIsolation
open Purelib.Geometry.Rational

/-- The existing signed crossing-geometry type on the actual retained endpoint samples and original bridge family. -/
abbrev GeometryAt {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    {collision : ProjectionCollision segment slope reading} (prepared : WindowSamples collision)
    (bridges : OwnerWindow.BridgesAt prepared.1 prepared.1.parameters.lower prepared.1.parameters.upper) :=
  Progressive.Braid.Projected.Overlap.CrossingGeometry
    (bridges.sourceFrame prepared.2.1 ⟨le_rfl, prepared.1.parameters.valid⟩).projected
    (bridges.targetFrame prepared.2.2 ⟨prepared.1.parameters.valid, le_rfl⟩).projected
    (bridges.chamberOverlap prepared.2.1 prepared.2.2 ⟨le_rfl, prepared.1.parameters.valid⟩
      ⟨prepared.1.parameters.valid, le_rfl⟩) collision.generator

/-- The internally prepared original window and bridges satisfy their computed generator's actual signed geometry.

Both endpoint sample frames and the original bridge family are retained.
The derived source branch order locates the two actual bridge boxes.
The computed generator's sign selects the strict box order already proved
from the same intrinsic collision height and original anchor-radius cap. -/
theorem prepareCrossingGeometry {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading) :
    let prepared := collision.prepareCrossingSamples avoidsZero avoidsOne fixed startMisses finishMisses
    ∀ bridges : OwnerWindow.BridgesAt prepared.1 prepared.1.parameters.lower prepared.1.parameters.upper,
      GeometryAt prepared bridges := by
  dsimp only
  intro bridges
  let prepared := collision.prepareCrossingSamples avoidsZero avoidsOne fixed startMisses finishMisses
  have avoids : segment.Avoids (gaussian reading 0) := by
    rcases fixed with zero | one
    · subst reading
      exact avoidsZero
    · subst reading
      exact avoidsOne
  have heightNonzero := collision.relativeHeight_nonzero avoids
  have velocityNonzero := collision.projectionVelocity_ne_zero startMisses
  constructor
  change match collision.generator.sign with
    | .positive =>
        (Box.Rotation.enclosure prepared.2.1.val.projectionSlope
          ((bridges.chamberOverlap prepared.2.1 prepared.2.2 ⟨le_rfl, prepared.1.parameters.valid⟩
            ⟨prepared.1.parameters.valid, le_rfl⟩).bridge
            ((bridges.sourceFrame prepared.2.1 ⟨le_rfl, prepared.1.parameters.valid⟩).projected.ownerIndex
              collision.generator.left)).box).yUpper <
          (Box.Rotation.enclosure prepared.2.1.val.projectionSlope
            ((bridges.chamberOverlap prepared.2.1 prepared.2.2 ⟨le_rfl, prepared.1.parameters.valid⟩
              ⟨prepared.1.parameters.valid, le_rfl⟩).bridge
              ((bridges.sourceFrame prepared.2.1 ⟨le_rfl, prepared.1.parameters.valid⟩).projected.ownerIndex
                collision.generator.right)).box).yLower
    | .negative =>
        (Box.Rotation.enclosure prepared.2.1.val.projectionSlope
          ((bridges.chamberOverlap prepared.2.1 prepared.2.2 ⟨le_rfl, prepared.1.parameters.valid⟩
            ⟨prepared.1.parameters.valid, le_rfl⟩).bridge
            ((bridges.sourceFrame prepared.2.1 ⟨le_rfl, prepared.1.parameters.valid⟩).projected.ownerIndex
              collision.generator.right)).box).yUpper <
          (Box.Rotation.enclosure prepared.2.1.val.projectionSlope
            ((bridges.chamberOverlap prepared.2.1 prepared.2.2 ⟨le_rfl, prepared.1.parameters.valid⟩
              ⟨prepared.1.parameters.valid, le_rfl⟩).bridge
              ((bridges.sourceFrame prepared.2.1 ⟨le_rfl, prepared.1.parameters.valid⟩).projected.ownerIndex
                collision.generator.left)).box).yLower
  rewrite [prepared.2.1.property.1]
  rcases lt_trichotomy 0 (segment.projectionVelocity slope) with velocityPositive | velocityZero | velocityNegative
  · have orders := collision.crossingWindow_orders_of_velocity_pos avoidsZero avoidsOne fixed startMisses finishMisses
      avoids velocityPositive
    dsimp only at orders
    rcases lt_trichotomy 0 ((Rotation.rotate slope (segment.pointAt collision.val)).im + slope * reading) with
      heightPositive | heightZero | heightNegative
    · rcases fixed with atZero | atOne
      · subst reading
        rewrite [if_pos rfl] at orders
        unfold generator
        rewrite [if_pos rfl, if_pos heightPositive]
        dsimp only
        rewrite [if_pos velocityPositive]
        dsimp only [Braid.CrossingSign.reverse]
        rewrite [bridges.chamberOverlap_bridge_box_at_position, bridges.chamberOverlap_bridge_box_at_position,
          prepareCrossingSamples_window, orders.1]
        exact collision.prepareCrossingWindow_height_above avoidsZero avoidsOne (Or.inl rfl) startMisses finishMisses
          avoids 0 rfl heightPositive
      · subst reading
        rewrite [if_neg (by decide : (1 : Coordinate) ≠ 0)] at orders
        unfold generator
        rewrite [if_neg (by decide : (1 : Coordinate) ≠ 0), if_pos heightPositive]
        dsimp only
        rewrite [if_pos velocityPositive]
        dsimp only [Braid.CrossingSign.reverse]
        rewrite [bridges.chamberOverlap_bridge_box_at_position, bridges.chamberOverlap_bridge_box_at_position,
          prepareCrossingSamples_window, orders.1]
        exact collision.prepareCrossingWindow_height_above avoidsZero avoidsOne (Or.inr rfl) startMisses finishMisses
          avoids 2 rfl heightPositive
    · exact (heightNonzero heightZero.symm).elim
    · rcases fixed with atZero | atOne
      · subst reading
        rewrite [if_pos rfl] at orders
        unfold generator
        rewrite [if_pos rfl, if_neg (fun positive => lt_asymm positive heightNegative)]
        dsimp only
        rewrite [if_pos velocityPositive]
        dsimp only [Braid.CrossingSign.reverse]
        rewrite [bridges.chamberOverlap_bridge_box_at_position, bridges.chamberOverlap_bridge_box_at_position,
          prepareCrossingSamples_window, orders.1]
        exact collision.prepareCrossingWindow_height_below avoidsZero avoidsOne (Or.inl rfl) startMisses finishMisses
          avoids 0 rfl heightNegative
      · subst reading
        rewrite [if_neg (by decide : (1 : Coordinate) ≠ 0)] at orders
        unfold generator
        rewrite [if_neg (by decide : (1 : Coordinate) ≠ 0),
          if_neg (fun positive => lt_asymm positive heightNegative)]
        dsimp only
        rewrite [if_pos velocityPositive]
        dsimp only [Braid.CrossingSign.reverse]
        rewrite [bridges.chamberOverlap_bridge_box_at_position, bridges.chamberOverlap_bridge_box_at_position,
          prepareCrossingSamples_window, orders.1]
        exact collision.prepareCrossingWindow_height_below avoidsZero avoidsOne (Or.inr rfl) startMisses finishMisses
          avoids 2 rfl heightNegative
  · exact (velocityNonzero velocityZero.symm).elim
  · have orders := collision.crossingWindow_orders_of_velocity_neg avoidsZero avoidsOne fixed startMisses finishMisses
      avoids velocityNegative
    dsimp only at orders
    have velocityNotPositive : ¬ 0 < segment.projectionVelocity slope :=
      fun positive => lt_asymm positive velocityNegative
    rcases lt_trichotomy 0 ((Rotation.rotate slope (segment.pointAt collision.val)).im + slope * reading) with
      heightPositive | heightZero | heightNegative
    · rcases fixed with atZero | atOne
      · subst reading
        rewrite [if_pos rfl] at orders
        unfold generator
        rewrite [if_pos rfl, if_pos heightPositive]
        dsimp only
        rewrite [if_neg velocityNotPositive]
        dsimp only [Braid.CrossingSign.reverse]
        rewrite [bridges.chamberOverlap_bridge_box_at_position, bridges.chamberOverlap_bridge_box_at_position,
          prepareCrossingSamples_window, orders.1]
        exact collision.prepareCrossingWindow_height_above avoidsZero avoidsOne (Or.inl rfl) startMisses finishMisses
          avoids 0 rfl heightPositive
      · subst reading
        rewrite [if_neg (by decide : (1 : Coordinate) ≠ 0)] at orders
        unfold generator
        rewrite [if_neg (by decide : (1 : Coordinate) ≠ 0), if_pos heightPositive]
        dsimp only
        rewrite [if_neg velocityNotPositive]
        dsimp only [Braid.CrossingSign.reverse]
        rewrite [bridges.chamberOverlap_bridge_box_at_position, bridges.chamberOverlap_bridge_box_at_position,
          prepareCrossingSamples_window, orders.1]
        exact collision.prepareCrossingWindow_height_above avoidsZero avoidsOne (Or.inr rfl) startMisses finishMisses
          avoids 2 rfl heightPositive
    · exact (heightNonzero heightZero.symm).elim
    · rcases fixed with atZero | atOne
      · subst reading
        rewrite [if_pos rfl] at orders
        unfold generator
        rewrite [if_pos rfl, if_neg (fun positive => lt_asymm positive heightNegative)]
        dsimp only
        rewrite [if_neg velocityNotPositive]
        dsimp only [Braid.CrossingSign.reverse]
        rewrite [bridges.chamberOverlap_bridge_box_at_position, bridges.chamberOverlap_bridge_box_at_position,
          prepareCrossingSamples_window, orders.1]
        exact collision.prepareCrossingWindow_height_below avoidsZero avoidsOne (Or.inl rfl) startMisses finishMisses
          avoids 0 rfl heightNegative
      · subst reading
        rewrite [if_neg (by decide : (1 : Coordinate) ≠ 0)] at orders
        unfold generator
        rewrite [if_neg (by decide : (1 : Coordinate) ≠ 0),
          if_neg (fun positive => lt_asymm positive heightNegative)]
        dsimp only
        rewrite [if_neg velocityNotPositive]
        dsimp only [Braid.CrossingSign.reverse]
        rewrite [bridges.chamberOverlap_bridge_box_at_position, bridges.chamberOverlap_bridge_box_at_position,
          prepareCrossingSamples_window, orders.1]
        exact collision.prepareCrossingWindow_height_below avoidsZero avoidsOne (Or.inr rfl) startMisses finishMisses
          avoids 2 rfl heightNegative

/-- Compute an original atomic projected crossing from its event, chart and intrinsic branch avoidance.

The original window and both sample frames are computed once and retained.
Its source factors and three original bridges are also materialized once.
The same computed generator, signed bridge geometry and owner-order law
construct the original projected-overlap crossing constructor. No frame,
bridge, signed geometry or braid certificate is supplied. -/
@[expose] def prepareCrossingOverlap {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading) : PreparedWindow collision := by
  let prepared := collision.prepareCrossingSamples avoidsZero avoidsOne fixed startMisses finishMisses
  let window := prepared.1
  let lowerInside : window.parameters.Contains window.parameters.lower := ⟨le_rfl, window.parameters.valid⟩
  let upperInside : window.parameters.Contains window.parameters.upper := ⟨window.parameters.valid, le_rfl⟩
  let bridges := window.bridgesAt window.parameters.lower window.parameters.upper lowerInside upperInside
  let overlap := bridges.chamberOverlap prepared.2.1 prepared.2.2 lowerInside upperInside
  have geometry : GeometryAt prepared bridges :=
    collision.prepareCrossingGeometry avoidsZero avoidsOne fixed startMisses finishMisses bridges
  have avoids : segment.Avoids (gaussian reading 0) := by
    rcases fixed with zero | one
    · subst reading
      exact avoidsZero
    · subst reading
      exact avoidsOne
  have orders (position : Fin 3) :
      (branchOrder (segment.pointAt window.parameters.lower) slope).forward position =
        (branchOrder (segment.pointAt window.parameters.upper) slope).forward
          (collision.generator.permutation.forward position) :=
    collision.crossingWindow_orders_permutation avoidsZero avoidsOne fixed startMisses finishMisses avoids position
  refine ⟨prepared, bridges, .crossing overlap collision.generator geometry ?_⟩
  refine ⟨prepared.2.1.property.1.trans prepared.2.2.property.1.symm, ?_⟩
  intro position
  exact bridges.chamberOverlap_matching_positions prepared.2.1 prepared.2.2 lowerInside upperInside
    collision.generator.permutation orders position

/-- Atomic projected-crossing preparation retains the same complete original window and endpoint sample packet. -/
theorem prepareCrossingOverlap_samples {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading) :
    (collision.prepareCrossingOverlap avoidsZero avoidsOne fixed startMisses finishMisses).1 =
      collision.prepareCrossingSamples avoidsZero avoidsOne fixed startMisses finishMisses := rfl


/-- Automatic projected-crossing preparation extracts the same computed original adjacent generator as its event. -/
theorem prepareCrossingOverlap_event {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading) :
    (collision.prepareCrossingOverlap avoidsZero avoidsOne fixed startMisses finishMisses).overlap.event =
      .crossing collision.generator := rfl

/-- The actual prepared crossing-window segment has exactly the singleton word of its original computed generator. -/
theorem prepareCrossingOverlap_word {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading) :
    (collision.prepareCrossingOverlap avoidsZero avoidsOne fixed startMisses finishMisses).toSegment.crossings =
      [collision.generator] := by
  change (collision.prepareCrossingOverlap avoidsZero avoidsOne fixed startMisses finishMisses).overlap.event.word = _
  rewrite [collision.prepareCrossingOverlap_event avoidsZero avoidsOne fixed startMisses finishMisses]
  rfl

/-- The computed projected overlap retains its same complete original chamber overlap and cached bridge family. -/
theorem prepareCrossingOverlap_chamber {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading) :
    let prepared := collision.prepareCrossingOverlap avoidsZero avoidsOne fixed startMisses finishMisses
    prepared.overlap.chamberOverlap = prepared.bridges.chamberOverlap prepared.samples.2.1 prepared.samples.2.2
      ⟨le_rfl, prepared.samples.1.parameters.valid⟩ ⟨prepared.samples.1.parameters.valid, le_rfl⟩ := rfl

end Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision
