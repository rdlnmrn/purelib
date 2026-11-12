module

public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Height
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window
import Purelib.Curves.Legendre.Paths.Preparation
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Fin.Bijection.Transposition
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Topology.Knot.Braid.Basic

/-!
# Adjacent crossings of original Legendre axis projections

The identified fixed reading determines the adjacent pair. The original
affine projection velocity and signed collision height determine the
crossing orientation. The actual endpoint branch orders come from those
same readings and the internally computed crossing window.
-/

public section

namespace Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision

open Purelib.Data
open Purelib.Data.Gaussian.Coordinates
open Purelib.Data.Fin.Bijection
open Purelib.Data.Rat
open Purelib.Topology.Knot

/-- Compute the adjacent generator from the original fixed reading, affine direction and signed collision height.

Reading zero selects the lower adjacent pair; reading one selects the
upper pair. Positive affine velocity starts the moving branch to the left
of the fixed branch, reversing the sign read from fixed-to-moving height.
Negative velocity starts it to the right and retains that height sign. -/
@[expose] def generator {start finish : Gaussian} {segment : AxisSegment start finish} {slope reading : Coordinate}
    (collision : ProjectionCollision segment slope reading) : Braid.Generator 3 :=
  let index : Fin 2 := if reading = 0 then 0 else 1
  let heightSign : Braid.CrossingSign :=
    if 0 < (Rotation.rotate slope (segment.pointAt collision.val)).im + slope * reading then .positive else .negative
  { index := index
    sign := if 0 < segment.projectionVelocity slope then heightSign.reverse else heightSign }

/-- Positive charts compute the same complete signed generator for collisions of the same original axis and reading.

Both charts preserve the axis velocity sign and the imaginary sign of
their actual collision points. Their positive height scale preserves the
relative height sign, so both original lower/upper index and orientation
are equal even when the actual unit collision parameters differ.
-/
theorem generator_eq_of_positive_slopes {start finish : Gaussian} {segment : AxisSegment start finish}
    {first last reading : Coordinate} (left : ProjectionCollision segment first reading)
    (right : ProjectionCollision segment last reading) (firstPositive : 0 < first) (lastPositive : 0 < last) :
    left.generator = right.generator := by
  have height := left.relativeHeight_pos_iff.trans
    ((left.imaginary_pos_iff_of_positive_slopes right firstPositive lastPositive).trans
      right.relativeHeight_pos_iff.symm)
  have velocity := segment.projectionVelocity_pos_iff_of_positive_slopes first last firstPositive lastPositive
  unfold generator
  dsimp only
  by_cases leftHeight : 0 < (Rotation.rotate first (segment.pointAt left.val)).im + first * reading
  · rewrite [if_pos leftHeight, if_pos (height.mp leftHeight)]
    by_cases leftVelocity : 0 < segment.projectionVelocity first
    · rewrite [if_pos leftVelocity, if_pos (velocity.mp leftVelocity)]
      rfl
    · rewrite [if_neg leftVelocity, if_neg (fun positive => leftVelocity (velocity.mpr positive))]
      rfl
  · rewrite [if_neg leftHeight, if_neg (fun positive => leftHeight (height.mpr positive))]
    by_cases leftVelocity : 0 < segment.projectionVelocity first
    · rewrite [if_pos leftVelocity, if_pos (velocity.mp leftVelocity)]
      rfl
    · rewrite [if_neg leftVelocity, if_neg (fun positive => leftVelocity (velocity.mpr positive))]
      rfl

/-- A zero event computes the original lower adjacent generator index. -/
theorem generator_index_zero {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (collision : ProjectionCollision segment slope 0) : collision.generator.index = 0 := by
  unfold generator
  rewrite [if_pos rfl]
  rfl

/-- A one event computes the original upper adjacent generator index. -/
theorem generator_index_one {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (collision : ProjectionCollision segment slope 1) : collision.generator.index = 1 := by
  unfold generator
  rewrite [if_neg (by decide : (1 : Coordinate) ≠ 0)]
  rfl

/-- Positive projection velocity swaps the actual original endpoint branch orders at the identified fixed reading.

The lower and upper parameter endpoints lie on opposite sides of the
same original event. Their quarter-unit reading bounds exclude the other
fixed reading. Thus zero gives lower-swap then identity, and one gives
identity then upper-swap, in the original logical branch labels. -/
theorem crossingWindow_orders_of_velocity_pos {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (avoids : segment.Avoids (gaussian reading 0)) (positive : 0 < segment.projectionVelocity slope) :
    let window := collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses
    if reading = 0 then
      branchOrder (segment.pointAt window.parameters.lower) slope = Transposition.transposition 0 1 ∧
        branchOrder (segment.pointAt window.parameters.upper) slope = identity 3
    else
      branchOrder (segment.pointAt window.parameters.lower) slope = identity 3 ∧
        branchOrder (segment.pointAt window.parameters.upper) slope = Transposition.transposition 1 2 := by
  let window := collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses
  have anchor := collision.prepareOwnerWindow_anchor_interior avoidsZero avoidsOne
    (collision.interior startMisses finishMisses) (collision.heightCap avoids)
  have before := collision.reading_lt_of_before_of_velocity_pos window.parameters.lower anchor.1 positive
  have after := collision.reading_gt_of_after_of_velocity_pos window.parameters.upper anchor.2 positive
  have lower := collision.prepareCrossingWindow_reading_bounds avoidsZero avoidsOne fixed startMisses finishMisses
    avoids window.parameters.lower ⟨le_rfl, window.parameters.valid⟩
  have upper := collision.prepareCrossingWindow_reading_bounds avoidsZero avoidsOne fixed startMisses finishMisses
    avoids window.parameters.upper ⟨window.parameters.valid, le_rfl⟩
  dsimp only
  rcases fixed with zero | one
  · subst reading
    rewrite [if_pos rfl]
    exact ⟨branchOrder_of_negative _ _ before,
      branchOrder_of_between _ _ after (upper.2.trans_lt (by decide : (0 + 1 / 4 : Coordinate) < 1))⟩
  · subst reading
    rewrite [if_neg (by decide : (1 : Coordinate) ≠ 0)]
    exact ⟨branchOrder_of_between _ _ ((by decide : (0 : Coordinate) < 1 - 1 / 4).trans_le lower.1) before,
      branchOrder_of_above_one _ _ after⟩

/-- Negative projection velocity swaps the same original endpoint branch orders in the opposite direction.

The original lower endpoint is above the event reading and the upper
endpoint below it. Their same quarter-unit bounds give identity then
lower-swap at zero, and upper-swap then identity at one. -/
theorem crossingWindow_orders_of_velocity_neg {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (avoids : segment.Avoids (gaussian reading 0)) (negative : segment.projectionVelocity slope < 0) :
    let window := collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses
    if reading = 0 then
      branchOrder (segment.pointAt window.parameters.lower) slope = identity 3 ∧
        branchOrder (segment.pointAt window.parameters.upper) slope = Transposition.transposition 0 1
    else
      branchOrder (segment.pointAt window.parameters.lower) slope = Transposition.transposition 1 2 ∧
        branchOrder (segment.pointAt window.parameters.upper) slope = identity 3 := by
  let window := collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses
  have anchor := collision.prepareOwnerWindow_anchor_interior avoidsZero avoidsOne
    (collision.interior startMisses finishMisses) (collision.heightCap avoids)
  have before := collision.reading_gt_of_before_of_velocity_neg window.parameters.lower anchor.1 negative
  have after := collision.reading_lt_of_after_of_velocity_neg window.parameters.upper anchor.2 negative
  have lower := collision.prepareCrossingWindow_reading_bounds avoidsZero avoidsOne fixed startMisses finishMisses
    avoids window.parameters.lower ⟨le_rfl, window.parameters.valid⟩
  have upper := collision.prepareCrossingWindow_reading_bounds avoidsZero avoidsOne fixed startMisses finishMisses
    avoids window.parameters.upper ⟨window.parameters.valid, le_rfl⟩
  dsimp only
  rcases fixed with zero | one
  · subst reading
    rewrite [if_pos rfl]
    exact ⟨branchOrder_of_between _ _ before (lower.2.trans_lt (by decide : (0 + 1 / 4 : Coordinate) < 1)),
      branchOrder_of_negative _ _ after⟩
  · subst reading
    rewrite [if_neg (by decide : (1 : Coordinate) ≠ 0)]
    exact ⟨branchOrder_of_above_one _ _ before,
      branchOrder_of_between _ _ ((by decide : (0 : Coordinate) < 1 - 1 / 4).trans_le upper.1) after⟩

/-- The computed adjacent generator gives the actual permutation between the original crossing-window endpoint orders.

The same original affine velocity has one of its two strict signs. The
derived endpoint order cases and the computed lower or upper adjacent
pair identify every original logical label after the generator's actual
position swap. Its crossing sign does not change that permutation. -/
theorem crossingWindow_orders_permutation {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope reading : Coordinate} (collision : ProjectionCollision segment slope reading)
    (avoidsZero : segment.Avoids 0) (avoidsOne : segment.Avoids 1) (fixed : reading = 0 ∨ reading = 1)
    (startMisses : (Rotation.rotate slope start).re ≠ reading)
    (finishMisses : (Rotation.rotate slope finish).re ≠ reading)
    (avoids : segment.Avoids (gaussian reading 0)) (position : Fin 3) :
    let window := collision.prepareCrossingWindow avoidsZero avoidsOne fixed startMisses finishMisses
    (branchOrder (segment.pointAt window.parameters.lower) slope).forward position =
      (branchOrder (segment.pointAt window.parameters.upper) slope).forward
        (collision.generator.permutation.forward position) := by
  have nonzero := collision.projectionVelocity_ne_zero startMisses
  dsimp only
  rcases lt_trichotomy 0 (segment.projectionVelocity slope) with positive | zero | negative
  · have orders := collision.crossingWindow_orders_of_velocity_pos avoidsZero avoidsOne fixed startMisses finishMisses
      avoids positive
    dsimp only at orders
    rcases fixed with atZero | atOne
    · subst reading
      rewrite [if_pos rfl] at orders
      rewrite [orders.1, orders.2]
      rfl
    · subst reading
      rewrite [if_neg (by decide : (1 : Coordinate) ≠ 0)] at orders
      rewrite [orders.1, orders.2]
      change position = Transposition.swapIndices 1 2 (Transposition.swapIndices 1 2 position)
      exact (Transposition.swapIndices_involutive _ _ _).symm
  · exact (nonzero zero.symm).elim
  · have orders := collision.crossingWindow_orders_of_velocity_neg avoidsZero avoidsOne fixed startMisses finishMisses
      avoids negative
    dsimp only at orders
    rcases fixed with atZero | atOne
    · subst reading
      rewrite [if_pos rfl] at orders
      rewrite [orders.1, orders.2]
      change position = Transposition.swapIndices 0 1 (Transposition.swapIndices 0 1 position)
      exact (Transposition.swapIndices_involutive _ _ _).symm
    · subst reading
      rewrite [if_neg (by decide : (1 : Coordinate) ≠ 0)] at orders
      rewrite [orders.1, orders.2]
      rfl

end Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionCollision
