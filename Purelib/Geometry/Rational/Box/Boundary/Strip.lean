module

public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Boundary
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Field.Defs
meta import Purelib.Elab.ConstructiveInjectivity

namespace Purelib.Geometry.Rational.Box.Boundary.Strip

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational.Box

/-- Factored upper bound for the squared distance to a projected boundary point.

The exact rational factor is eight times eight. It is retained as the
common scale comparing a selected boundary projection with the original
small-box anchor and squared radius. -/
@[expose] public def protectedBoundaryDistanceScale : Fraction.Rational := (8 : Fraction.Rational) * 8

/-- Proof-relevant selection of the parent side met by a small box.

The original parent box, width and Gaussian point index the side evidence.
Each constructor retains the corresponding coordinate inequality for the
left, right, bottom or top parent strip, without choosing another point. -/
public inductive BoundaryStripSide
    (ambient : Box) (width : Fraction.Rational) (z : Gaussian.Basic.Canonical) : Type
  /-- Evidence that the point lies no farther than the given width to the right of the left side. -/ | left (inside :
    z.re ≤ ambient.xLower + width)
  /-- Evidence that the point lies no farther than the given width to the left of the right side. -/ | right (inside :
    ambient.xUpper - width ≤ z.re)
  /-- Evidence that the point lies no farther than the given width above the bottom side. -/ | bottom (inside : z.im ≤
    ambient.yLower + width)
  /-- Evidence that the point lies no farther than the given width below the top side. -/ | top (inside : ambient.yUpper
    - width ≤ z.im)

set_option genInjectivity false in
/-- A supplied finite point of the small box and the side it places in the parent strip.

The original point carries its membership in the supplied small box. Its
selected side and coordinate inequality retain contact with the indexed
parent boundary strip at the same width. -/
public structure BoundaryStripWitness
    (ambient small : Box) (width : Fraction.Rational) where
  /-- The retained point witnessing contact with a selected boundary strip. -/ point : Gaussian.Basic.Canonical
  /-- The retained point belongs to the small box. -/ point_mem : small.Contains point
  /-- The chosen parent side together with the corresponding strip inequality. -/ side : BoundaryStripSide ambient width
    point

constructive_injectivity BoundaryStripWitness

set_option genInjectivity false in
/-- Parent-boundary projection with an explicit anchor-distance estimate.

The original ambient and small boxes and radius index the certificate.
The retained point lies on the parent boundary and its squared distance
from the small-box anchor is bounded by the displayed scale times rho squared. -/
public structure NearbyBoundaryPoint
    (ambient small : Box) (rho : Fraction.Rational) where
  /-- The constructed point on the parent boundary. -/ point : Gaussian.Basic.Canonical
  /-- The point belongs to the parent box and one of its sides. -/ boundary : Boundary.OnBoxBoundary ambient point
  /-- The squared distance from the small-box anchor satisfies the retained radius bound. -/ distance :
    Data.Gaussian.Norm.Basic.normSq (point - small.anchor) ≤
    protectedBoundaryDistanceScale * rho ^ 2

constructive_injectivity NearbyBoundaryPoint

/-- Project the supplied strip point to its selected parent side.

The supplied point is projected to its selected left, right, bottom or top
parent side, preserving its other coordinate. The original containment and
diagonal bound control the same selected projection and anchor displacement. -/
@[expose] public def nearbyBoundaryPoint
    {ambient small : Box} {rho : Fraction.Rational}
    (refines : small.Refines ambient)
    (diagonal : small.diagonalSq ≤ rho ^ 2)
    (witness : BoundaryStripWitness ambient small (4 * rho)) :
    NearbyBoundaryPoint ambient small rho := by
  rcases witness with ⟨z, zSmall, side⟩
  have zAmbient := refines.contains zSmall
  have zAnchorDistance := small.normSq_sub_anchor_le zSmall
  have zAnchorBound : Data.Gaussian.Norm.Basic.normSq (z - small.anchor) ≤ rho ^ 2 :=
    zAnchorDistance.trans diagonal
  have projectionFinish : ∀ point : Gaussian.Basic.Canonical,
      Boundary.OnBoxBoundary ambient point →
      Data.Gaussian.Norm.Basic.normSq (point - z) ≤ 16 * rho ^ 2 →
      NearbyBoundaryPoint ambient small rho := by
    intro point boundary projectionBound
    have decomposition : point - small.anchor =
        (point - z) + (z - small.anchor) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;>
        ring1
    have sumBound := Gaussian.Norm.Bounds.normSq_add_le_two (point - z) (z - small.anchor)
    have squareNonnegative :=
      Fraction.Order.Arithmetic.sq_nonneg_direct rho
    have squareLeProjection : rho ^ 2 ≤ 16 * rho ^ 2 := by
      calc
        rho ^ 2 = 1 * rho ^ 2 := by ring1
        _ ≤ 16 * rho ^ 2 :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (Fraction.Cast.Order.natCast_le_direct
              (m := 1) (n := 16) (by decide)) squareNonnegative
    have twoNonnegative : (0 : Fraction.Rational) ≤ 2 :=
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 2) (by decide)).le
    refine ⟨point, boundary, ?_⟩
    rw [decomposition]
    calc
      Data.Gaussian.Norm.Basic.normSq ((point - z) + (z - small.anchor)) ≤
          2 * (Data.Gaussian.Norm.Basic.normSq (point - z) + Data.Gaussian.Norm.Basic.normSq (z - small.anchor))
            := sumBound
      _ ≤ 2 * (16 * rho ^ 2 + rho ^ 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add projectionBound zAnchorBound) (by decide)
      _ ≤ 2 * (16 * rho ^ 2 + 16 * rho ^ 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add (le_refl _) squareLeProjection)
          twoNonnegative
      _ = protectedBoundaryDistanceScale * rho ^ 2 := by
        unfold protectedBoundaryDistanceScale
        ring1
  cases side with
  | left sideBound =>
      let point : Gaussian.Basic.Canonical := ⟨ambient.xLower, z.im⟩
      have deltaNonnegative : 0 ≤ z.re - ambient.xLower :=
        Fraction.Order.Arithmetic.sub_nonneg_direct zAmbient.1
      have deltaBound : z.re - ambient.xLower ≤ 4 * rho := by
        have shifted := Fraction.Order.Arithmetic.sub_le_sub_right_direct sideBound ambient.xLower
        calc
          z.re - ambient.xLower ≤
              ambient.xLower + 4 * rho - ambient.xLower := shifted
          _ = 4 * rho := by ring1
      have squareBound := Fraction.Order.Arithmetic.pow_le_pow_direct
        deltaNonnegative deltaBound 2
      apply projectionFinish point
      · exact ⟨⟨le_rfl, ambient.x_valid, zAmbient.2.2.1,
          zAmbient.2.2.2⟩, Or.inl rfl⟩
      · calc
          Data.Gaussian.Norm.Basic.normSq (point - z) = (z.re - ambient.xLower) ^ 2 := by
            dsimp only [point, Data.Gaussian.Norm.Basic.normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
            ring1
          _ ≤ (4 * rho) ^ 2 := squareBound
          _ = 16 * rho ^ 2 := by ring1
  | right sideBound =>
      let point : Gaussian.Basic.Canonical := ⟨ambient.xUpper, z.im⟩
      have deltaNonnegative : 0 ≤ ambient.xUpper - z.re :=
        Fraction.Order.Arithmetic.sub_nonneg_direct zAmbient.2.1
      have deltaBound : ambient.xUpper - z.re ≤ 4 * rho := by
        have shifted := Fraction.Order.Arithmetic.sub_le_sub_left_direct sideBound ambient.xUpper
        calc
          ambient.xUpper - z.re ≤
              ambient.xUpper - (ambient.xUpper - 4 * rho) := shifted
          _ = 4 * rho := by ring1
      have squareBound := Fraction.Order.Arithmetic.pow_le_pow_direct
        deltaNonnegative deltaBound 2
      apply projectionFinish point
      · exact ⟨⟨ambient.x_valid, le_rfl, zAmbient.2.2.1,
          zAmbient.2.2.2⟩, Or.inr (Or.inl rfl)⟩
      · calc
          Data.Gaussian.Norm.Basic.normSq (point - z) = (ambient.xUpper - z.re) ^ 2 := by
            dsimp only [point, Data.Gaussian.Norm.Basic.normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
            ring1
          _ ≤ (4 * rho) ^ 2 := squareBound
          _ = 16 * rho ^ 2 := by ring1
  | bottom sideBound =>
      let point : Gaussian.Basic.Canonical := ⟨z.re, ambient.yLower⟩
      have deltaNonnegative : 0 ≤ z.im - ambient.yLower :=
        Fraction.Order.Arithmetic.sub_nonneg_direct zAmbient.2.2.1
      have deltaBound : z.im - ambient.yLower ≤ 4 * rho := by
        have shifted := Fraction.Order.Arithmetic.sub_le_sub_right_direct sideBound ambient.yLower
        calc
          z.im - ambient.yLower ≤
              ambient.yLower + 4 * rho - ambient.yLower := shifted
          _ = 4 * rho := by ring1
      have squareBound := Fraction.Order.Arithmetic.pow_le_pow_direct
        deltaNonnegative deltaBound 2
      apply projectionFinish point
      · exact ⟨⟨zAmbient.1, zAmbient.2.1, le_rfl,
          ambient.y_valid⟩, Or.inr (Or.inr (Or.inl rfl))⟩
      · calc
          Data.Gaussian.Norm.Basic.normSq (point - z) = (z.im - ambient.yLower) ^ 2 := by
            dsimp only [point, Data.Gaussian.Norm.Basic.normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
            ring1
          _ ≤ (4 * rho) ^ 2 := squareBound
          _ = 16 * rho ^ 2 := by ring1
  | top sideBound =>
      let point : Gaussian.Basic.Canonical := ⟨z.re, ambient.yUpper⟩
      have deltaNonnegative : 0 ≤ ambient.yUpper - z.im :=
        Fraction.Order.Arithmetic.sub_nonneg_direct zAmbient.2.2.2
      have deltaBound : ambient.yUpper - z.im ≤ 4 * rho := by
        have shifted := Fraction.Order.Arithmetic.sub_le_sub_left_direct sideBound ambient.yUpper
        calc
          ambient.yUpper - z.im ≤
              ambient.yUpper - (ambient.yUpper - 4 * rho) := shifted
          _ = 4 * rho := by ring1
      have squareBound := Fraction.Order.Arithmetic.pow_le_pow_direct
        deltaNonnegative deltaBound 2
      apply projectionFinish point
      · exact ⟨⟨zAmbient.1, zAmbient.2.1, ambient.y_valid,
          le_rfl⟩, Or.inr (Or.inr (Or.inr rfl))⟩
      · calc
          Data.Gaussian.Norm.Basic.normSq (point - z) = (ambient.yUpper - z.im) ^ 2 := by
            dsimp only [point, Data.Gaussian.Norm.Basic.normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
            ring1
          _ ≤ (4 * rho) ^ 2 := squareBound
          _ = 16 * rho ^ 2 := by ring1

end Purelib.Geometry.Rational.Box.Boundary.Strip
