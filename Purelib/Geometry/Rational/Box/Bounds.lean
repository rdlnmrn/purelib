module
public import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Dimensions
public import Purelib.Geometry.Rational.Box.Sample
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Algebra.Group.Negation
import Purelib.Tactic.Ring

/-!
# Quadrance bounds for rational boxes

The original endpoints determine side lengths, a diagonal square and a
coordinate-square maximum. Retained containment and refinement comparisons
control quadrance without replacing the endpoints or Gaussian observations.
-/

open Purelib
open Purelib.Data.Rat
open Purelib.Geometry

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

namespace Purelib.Geometry.Rational.Box

/-- Largest of the four squared endpoint coordinates.

The maximum retains all four original endpoint squares and the same nested
rational maximum operations. It bounds each real and imaginary endpoint square. -/
@[expose] public def coordinateSqBound (B : Rational.Box) : Fraction.Rational :=
  max (max (B.xLower ^ 2) (B.xUpper ^ 2))
    (max (B.yLower ^ 2) (B.yUpper ^ 2))

/-- The maximum of the squared endpoint coordinates is nonnegative.

The lower real endpoint square is nonnegative and lies below both retained
maxima. Their comparisons give a nonnegative floor for the same coordinate bound. -/
public theorem coordinateSqBound_nonneg (B : Rational.Box) : 0 ≤ B.coordinateSqBound := by
  exact (Fraction.Order.Arithmetic.sq_nonneg_direct B.xLower).trans
    ((Fraction.Order.Basic.le_max_left _ _).trans (Fraction.Order.Basic.le_max_left _ _))

/-- The sum of the squared width and height of the box.

The original horizontal and vertical endpoint differences determine the
squared diagonal. Their squares are added without changing the box endpoints. -/
@[expose] public def diagonalSq (B : Rational.Box) : Fraction.Rational :=
  (B.xUpper - B.xLower) ^ 2 + (B.yUpper - B.yLower) ^ 2

/-- The squared box diagonal is nonnegative.

Both squared endpoint differences are nonnegative. Their sum is therefore
nonnegative for every box with the original retained endpoints. -/
public theorem diagonalSq_nonneg (B : Rational.Box) : 0 ≤ B.diagonalSq := by
  exact add_nonneg
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)

/-- Coarse squared Gaussian norm bound for every member of the box.

Twice the largest retained endpoint square bounds the sum of the two
coordinate squares. The same box supplies all four endpoint observations. -/
@[expose] public def normSqBound (B : Rational.Box) : Fraction.Rational := 2 * B.coordinateSqBound

/-- The endpoint-based bound on Gaussian squared norm is nonnegative.

The retained maximum of endpoint squares is nonnegative. Doubling that
original scalar bound preserves its nonnegative floor. -/
public theorem normSqBound_nonneg (B : Rational.Box) : 0 ≤ B.normSqBound :=
  calc
    0 = 0 + 0 := by ring1
    _ ≤ B.coordinateSqBound + B.coordinateSqBound :=
      add_le_add B.coordinateSqBound_nonneg B.coordinateSqBound_nonneg
    _ = B.normSqBound := by
      dsimp only [Geometry.Rational.Box.normSqBound]
      ring1

/-- Every point in the closed box satisfies its endpoint-based squared-norm bound.

The retained containment comparisons place both Gaussian coordinates
between their respective box endpoints. Their endpoint-square bounds add
to at most twice the same maximum. -/
public theorem normSq_le_normSqBound {B : Rational.Box} {z : Data.Gaussian.Basic.Canonical}
    (inside : B.Contains z) : Data.Gaussian.Norm.Basic.normSq z ≤ B.normSqBound := by
  rcases inside with ⟨hxLower, hxUpper, hyLower, hyUpper⟩
  have hre : z.re ^ 2 ≤ B.coordinateSqBound :=
    (Rational.Box.sq_le_endpoint_max hxLower hxUpper).trans (Fraction.Order.Basic.le_max_left _ _)
  have him : z.im ^ 2 ≤ B.coordinateSqBound :=
    (Rational.Box.sq_le_endpoint_max hyLower hyUpper).trans (Fraction.Order.Basic.le_max_right _ _)
  calc
    Data.Gaussian.Norm.Basic.normSq z = z.re ^ 2 + z.im ^ 2 := rfl
    _ ≤ B.coordinateSqBound + B.coordinateSqBound := add_le_add hre him
    _ = B.normSqBound := by
      dsimp only [Geometry.Rational.Box.normSqBound]
      ring1

/-- Every point of a box is within its squared diagonal of the fixed anchor.

Containment makes each displacement from the lower-endpoint anchor
nonnegative and no larger than its original side length. Direct rational
multiplication comparisons bound the sum of their squares. -/
public theorem normSq_sub_anchor_le {B : Rational.Box} {z : Data.Gaussian.Basic.Canonical}
    (inside : B.Contains z) : Data.Gaussian.Norm.Basic.normSq (z - B.anchor) ≤ B.diagonalSq := by
  have xNonnegative : 0 ≤ z.re - B.xLower := Fraction.Order.Arithmetic.sub_nonneg_direct inside.1
  have yNonnegative : 0 ≤ z.im - B.yLower := Fraction.Order.Arithmetic.sub_nonneg_direct inside.2.2.1
  have xBound : z.re - B.xLower ≤ B.xUpper - B.xLower :=
    Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2.1 B.xLower
  have yBound : z.im - B.yLower ≤ B.yUpper - B.yLower :=
    Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2.2.2 B.yLower
  have xSquare : (z.re - B.xLower) ^ 2 ≤
      (B.xUpper - B.xLower) ^ 2 := by
    rw [pow_two, pow_two]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct xBound xBound
      xNonnegative B.widthX_nonneg
  have ySquare : (z.im - B.yLower) ^ 2 ≤
      (B.yUpper - B.yLower) ^ 2 := by
    rw [pow_two, pow_two]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct yBound yBound
      yNonnegative B.widthY_nonneg
  exact add_le_add xSquare ySquare

/-- Any two points of a box are at squared distance at most its squared diagonal.

The two retained points lie in the same box. Each coordinate difference
lies between the negative and positive original side length, so their
squared differences add to at most the squared diagonal. -/
public theorem normSq_sub_le_diagonalSq {B : Rational.Box} {u v : Data.Gaussian.Basic.Canonical}
    (uInside : B.Contains u) (vInside : B.Contains v) :
    Data.Gaussian.Norm.Basic.normSq (u - v) ≤ B.diagonalSq := by
  have xLower : -B.widthX ≤ u.re - v.re := by
    calc
      -B.widthX = B.xLower - B.xUpper := by
        dsimp only [Rational.Box.widthX]
        ring1
      _ ≤ u.re - v.re := Fraction.Order.Arithmetic.sub_le_sub_direct uInside.1 vInside.2.1
  have xUpper : u.re - v.re ≤ B.widthX := by
    exact Fraction.Order.Arithmetic.sub_le_sub_direct uInside.2.1 vInside.1
  have yLower : -B.widthY ≤ u.im - v.im := by
    calc
      -B.widthY = B.yLower - B.yUpper := by
        dsimp only [Rational.Box.widthY]
        ring1
      _ ≤ u.im - v.im := Fraction.Order.Arithmetic.sub_le_sub_direct uInside.2.2.1 vInside.2.2.2
  have yUpper : u.im - v.im ≤ B.widthY := by
    exact Fraction.Order.Arithmetic.sub_le_sub_direct uInside.2.2.2 vInside.2.2.1
  have xSquare := Rational.Box.sq_le_endpoint_max xLower xUpper
  have ySquare := Rational.Box.sq_le_endpoint_max yLower yUpper
  have negXSquare : (-B.widthX) ^ 2 = B.widthX ^ 2 := by ring1
  have negYSquare : (-B.widthY) ^ 2 = B.widthY ^ 2 := by ring1
  rw [negXSquare, Fraction.Order.Basic.max_self] at xSquare
  rw [negYSquare, Fraction.Order.Basic.max_self] at ySquare
  exact add_le_add xSquare ySquare

/-- Box refinement cannot increase horizontal width.

The retained refinement comparisons move the lower real endpoint upward
and the upper real endpoint downward. Subtracting the original endpoints
therefore decreases the horizontal side length. -/
public theorem widthX_le_of_refines {inner outer : Rational.Box}
    (refines : inner.Refines outer) : inner.widthX ≤ outer.widthX :=
  Fraction.Order.Arithmetic.sub_le_sub_direct refines.2.1 refines.1

/-- Box refinement cannot increase vertical width.

The retained refinement comparisons move the lower imaginary endpoint
upward and the upper imaginary endpoint downward. The original vertical
side length therefore cannot increase. -/
public theorem widthY_le_of_refines {inner outer : Rational.Box}
    (refines : inner.Refines outer) : inner.widthY ≤ outer.widthY :=
  Fraction.Order.Arithmetic.sub_le_sub_direct refines.2.2.2 refines.2.2.1

/-- Shrinking a rational box cannot increase its squared diagonal.

Refinement decreases each original side length, and both side lengths
remain nonnegative. Direct multiplication comparisons bound their squares
and hence the sum defining the diagonal. -/
public theorem diagonalSq_le_of_refines {inner outer : Rational.Box}
    (refines : inner.Refines outer) :
    inner.diagonalSq ≤ outer.diagonalSq := by
  have xWidth := Geometry.Rational.Box.widthX_le_of_refines refines
  have yWidth := Geometry.Rational.Box.widthY_le_of_refines refines
  have xSquare : inner.widthX ^ 2 ≤ outer.widthX ^ 2 := by
    rw [pow_two, pow_two]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct xWidth xWidth
      inner.widthX_nonneg outer.widthX_nonneg
  have ySquare : inner.widthY ^ 2 ≤ outer.widthY ^ 2 := by
    rw [pow_two, pow_two]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct yWidth yWidth
      inner.widthY_nonneg outer.widthY_nonneg
  exact add_le_add xSquare ySquare

end Purelib.Geometry.Rational.Box

namespace Purelib.Geometry.Rational.Box.Bounds

/-- The displayed corner opposite the fixed lower-left box anchor.

The original upper real and imaginary endpoints determine this Gaussian
corner. The lower endpoints still determine the unchanged box anchor. -/
@[expose] public def oppositeCorner (box : Rational.Box) : Data.Gaussian.Basic.Canonical :=
  ⟨box.xUpper, box.yUpper⟩

/-- The quadrance between opposite box corners equals the squared box diagonal.

The original lower-endpoint anchor and upper-endpoint corner differ by
the two signed side lengths. Squaring those coordinates gives precisely
the retained squared diagonal. -/
public theorem normSq_anchor_sub_oppositeCorner
    (box : Rational.Box) :
    Data.Gaussian.Norm.Basic.normSq (box.anchor - Geometry.Rational.Box.Bounds.oppositeCorner box) =
      box.diagonalSq := by
  simp only [Rational.Box.anchor, Geometry.Rational.Box.Bounds.oppositeCorner,
    Data.Gaussian.Norm.Basic.normSq,
    Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Geometry.Rational.Box.diagonalSq]
  ring1

end Purelib.Geometry.Rational.Box.Bounds

namespace Purelib.Geometry.Rational.Box

/-- Refining a box cannot increase the maximum squared endpoint coordinate.

Both inner endpoints lie between the original outer endpoints in each
coordinate. Their four square bounds combine under the same nested
maximum operations. -/
public theorem coordinateSqBound_le_of_refines {inner outer : Rational.Box}
    (refines : inner.Refines outer) :
    inner.coordinateSqBound ≤ outer.coordinateSqBound := by
  apply Fraction.Order.Basic.max_le
  · apply Fraction.Order.Basic.max_le
    · exact (Rational.Box.sq_le_endpoint_max refines.1
        (inner.x_valid.trans refines.2.1)).trans (Fraction.Order.Basic.le_max_left _ _)
    · exact (Rational.Box.sq_le_endpoint_max (refines.1.trans inner.x_valid)
        refines.2.1).trans (Fraction.Order.Basic.le_max_left _ _)
  · apply Fraction.Order.Basic.max_le
    · exact (Rational.Box.sq_le_endpoint_max refines.2.2.1
        (inner.y_valid.trans refines.2.2.2)).trans (Fraction.Order.Basic.le_max_right _ _)
    · exact (Rational.Box.sq_le_endpoint_max (refines.2.2.1.trans inner.y_valid)
        refines.2.2.2).trans (Fraction.Order.Basic.le_max_right _ _)

/-- Refining a box cannot increase its endpoint-based Gaussian squared-norm bound.

Refinement decreases the original maximum of endpoint squares.
Multiplication by the same nonnegative factor two preserves the comparison. -/
public theorem normSqBound_le_of_refines {inner outer : Rational.Box}
    (refines : inner.Refines outer) : inner.normSqBound ≤ outer.normSqBound :=
  Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Geometry.Rational.Box.coordinateSqBound_le_of_refines refines) (by decide)

end Purelib.Geometry.Rational.Box
