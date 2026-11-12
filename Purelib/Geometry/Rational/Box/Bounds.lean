module
public import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Rat.Fraction.Square

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

open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Gaussian.Norm

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
@[expose] public def coordinateSqBound (B : Box) : Fraction.Rational :=
  max (max (Fraction.square B.xLower) (Fraction.square B.xUpper))
    (max (Fraction.square B.yLower) (Fraction.square B.yUpper))

/-- Direct endpoint squaring retains the original nested maximum of four generic rational powers. -/
public theorem coordinateSqBound_eq_original (B : Box) :
    B.coordinateSqBound = max (max (B.xLower ^ 2) (B.xUpper ^ 2))
      (max (B.yLower ^ 2) (B.yUpper ^ 2)) := by
  unfold coordinateSqBound
  rewrite [Fraction.square_eq_mul, Fraction.square_eq_mul, Fraction.square_eq_mul, Fraction.square_eq_mul,
    pow_two, pow_two, pow_two, pow_two]
  rfl

/-- The maximum of the squared endpoint coordinates is nonnegative.

The lower real endpoint square is nonnegative and lies below both retained
maxima. Their comparisons give a nonnegative floor for the same coordinate bound. -/
public theorem coordinateSqBound_nonneg (B : Box) : 0 ≤ B.coordinateSqBound := by
  rewrite [coordinateSqBound_eq_original]
  exact (Arithmetic.sq_nonneg_direct B.xLower).trans
    ((Basic.le_max_left _ _).trans (Basic.le_max_left _ _))

/-- The sum of the squared width and height of the box.

The original horizontal and vertical endpoint differences determine the
squared diagonal. Their reduced fraction certificates give the same two
squares without repeated gcd normalization. -/
@[expose] public def diagonalSq (B : Box) : Fraction.Rational :=
  Fraction.square (B.xUpper - B.xLower) + Fraction.square (B.yUpper - B.yLower)

/-- Direct side-length squaring retains the original diagonal for every box. -/
public theorem diagonalSq_eq_original (B : Box) :
    B.diagonalSq = (B.xUpper - B.xLower) ^ 2 + (B.yUpper - B.yLower) ^ 2 := by
  unfold diagonalSq
  rewrite [Fraction.square_eq_mul, Fraction.square_eq_mul, pow_two, pow_two]
  rfl

/-- The squared box diagonal is nonnegative.

Both squared endpoint differences are nonnegative. Their sum is therefore
nonnegative for every box with the original retained endpoints. -/
public theorem diagonalSq_nonneg (B : Box) : 0 ≤ B.diagonalSq := by
  rewrite [diagonalSq_eq_original]
  exact add_nonneg
    (Arithmetic.sq_nonneg_direct _)
    (Arithmetic.sq_nonneg_direct _)

/-- Coarse squared Gaussian norm bound for every member of the box.

Twice the largest retained endpoint square bounds the sum of the two
coordinate squares. The same box supplies all four endpoint observations. -/
@[expose] public def normSqBound (B : Box) : Fraction.Rational := 2 * B.coordinateSqBound

/-- The endpoint-based bound on Gaussian squared norm is nonnegative.

The retained maximum of endpoint squares is nonnegative. Doubling that
original scalar bound preserves its nonnegative floor. -/
public theorem normSqBound_nonneg (B : Box) : 0 ≤ B.normSqBound :=
  calc
    0 = 0 + 0 := by ring1
    _ ≤ B.coordinateSqBound + B.coordinateSqBound :=
      add_le_add B.coordinateSqBound_nonneg B.coordinateSqBound_nonneg
    _ = B.normSqBound := by
      dsimp only [normSqBound]
      ring1

/-- Every point in the closed box satisfies its endpoint-based squared-norm bound.

The retained containment comparisons place both Gaussian coordinates
between their respective box endpoints. Their endpoint-square bounds add
to at most twice the same maximum. -/
public theorem normSq_le_normSqBound {B : Box} {z : Data.Gaussian.Basic.Canonical}
    (inside : B.Contains z) : Basic.normSq z ≤ B.normSqBound := by
  rcases inside with ⟨hxLower, hxUpper, hyLower, hyUpper⟩
  have hre : z.re ^ 2 ≤ B.coordinateSqBound := by
    rewrite [coordinateSqBound_eq_original]
    exact (sq_le_endpoint_max hxLower hxUpper).trans (Basic.le_max_left _ _)
  have him : z.im ^ 2 ≤ B.coordinateSqBound := by
    rewrite [coordinateSqBound_eq_original]
    exact (sq_le_endpoint_max hyLower hyUpper).trans (Basic.le_max_right _ _)
  calc
    Basic.normSq z = z.re ^ 2 + z.im ^ 2 := rfl
    _ ≤ B.coordinateSqBound + B.coordinateSqBound := add_le_add hre him
    _ = B.normSqBound := by
      dsimp only [normSqBound]
      ring1

/-- Every point of a box is within its squared diagonal of the fixed anchor.

Containment makes each displacement from the lower-endpoint anchor
nonnegative and no larger than its original side length. Direct rational
multiplication comparisons bound the sum of their squares. -/
public theorem normSq_sub_anchor_le {B : Box} {z : Data.Gaussian.Basic.Canonical}
    (inside : B.Contains z) : Basic.normSq (z - B.anchor) ≤ B.diagonalSq := by
  rewrite [diagonalSq_eq_original]
  have xNonnegative : 0 ≤ z.re - B.xLower := Arithmetic.sub_nonneg_direct inside.1
  have yNonnegative : 0 ≤ z.im - B.yLower := Arithmetic.sub_nonneg_direct inside.2.2.1
  have xBound : z.re - B.xLower ≤ B.xUpper - B.xLower :=
    Arithmetic.sub_le_sub_right_direct inside.2.1 B.xLower
  have yBound : z.im - B.yLower ≤ B.yUpper - B.yLower :=
    Arithmetic.sub_le_sub_right_direct inside.2.2.2 B.yLower
  have xSquare : (z.re - B.xLower) ^ 2 ≤
      (B.xUpper - B.xLower) ^ 2 := by
    rw [pow_two, pow_two]
    exact Arithmetic.mul_le_mul_direct xBound xBound
      xNonnegative B.widthX_nonneg
  have ySquare : (z.im - B.yLower) ^ 2 ≤
      (B.yUpper - B.yLower) ^ 2 := by
    rw [pow_two, pow_two]
    exact Arithmetic.mul_le_mul_direct yBound yBound
      yNonnegative B.widthY_nonneg
  exact add_le_add xSquare ySquare

/-- Any two points of a box are at squared distance at most its squared diagonal.

The two retained points lie in the same box. Each coordinate difference
lies between the negative and positive original side length, so their
squared differences add to at most the squared diagonal. -/
public theorem normSq_sub_le_diagonalSq {B : Box} {u v : Data.Gaussian.Basic.Canonical}
    (uInside : B.Contains u) (vInside : B.Contains v) :
    Basic.normSq (u - v) ≤ B.diagonalSq := by
  rewrite [diagonalSq_eq_original]
  have xLower : -B.widthX ≤ u.re - v.re := by
    calc
      -B.widthX = B.xLower - B.xUpper := by
        dsimp only [widthX]
        ring1
      _ ≤ u.re - v.re := Arithmetic.sub_le_sub_direct uInside.1 vInside.2.1
  have xUpper : u.re - v.re ≤ B.widthX := by
    exact Arithmetic.sub_le_sub_direct uInside.2.1 vInside.1
  have yLower : -B.widthY ≤ u.im - v.im := by
    calc
      -B.widthY = B.yLower - B.yUpper := by
        dsimp only [widthY]
        ring1
      _ ≤ u.im - v.im := Arithmetic.sub_le_sub_direct uInside.2.2.1 vInside.2.2.2
  have yUpper : u.im - v.im ≤ B.widthY := by
    exact Arithmetic.sub_le_sub_direct uInside.2.2.2 vInside.2.2.1
  have xSquare := sq_le_endpoint_max xLower xUpper
  have ySquare := sq_le_endpoint_max yLower yUpper
  have negXSquare : (-B.widthX) ^ 2 = B.widthX ^ 2 := by ring1
  have negYSquare : (-B.widthY) ^ 2 = B.widthY ^ 2 := by ring1
  rw [negXSquare, Basic.max_self] at xSquare
  rw [negYSquare, Basic.max_self] at ySquare
  exact add_le_add xSquare ySquare

/-- Box refinement cannot increase horizontal width.

The retained refinement comparisons move the lower real endpoint upward
and the upper real endpoint downward. Subtracting the original endpoints
therefore decreases the horizontal side length. -/
public theorem widthX_le_of_refines {inner outer : Box}
    (refines : inner.Refines outer) : inner.widthX ≤ outer.widthX :=
  Arithmetic.sub_le_sub_direct refines.2.1 refines.1

/-- Box refinement cannot increase vertical width.

The retained refinement comparisons move the lower imaginary endpoint
upward and the upper imaginary endpoint downward. The original vertical
side length therefore cannot increase. -/
public theorem widthY_le_of_refines {inner outer : Box}
    (refines : inner.Refines outer) : inner.widthY ≤ outer.widthY :=
  Arithmetic.sub_le_sub_direct refines.2.2.2 refines.2.2.1

/-- Shrinking a rational box cannot increase its squared diagonal.

Refinement decreases each original side length, and both side lengths
remain nonnegative. Direct multiplication comparisons bound their squares
and hence the sum defining the diagonal. -/
public theorem diagonalSq_le_of_refines {inner outer : Box}
    (refines : inner.Refines outer) :
    inner.diagonalSq ≤ outer.diagonalSq := by
  rewrite [diagonalSq_eq_original, diagonalSq_eq_original]
  have xWidth := widthX_le_of_refines refines
  have yWidth := widthY_le_of_refines refines
  have xSquare : inner.widthX ^ 2 ≤ outer.widthX ^ 2 := by
    rw [pow_two, pow_two]
    exact Arithmetic.mul_le_mul_direct xWidth xWidth
      inner.widthX_nonneg outer.widthX_nonneg
  have ySquare : inner.widthY ^ 2 ≤ outer.widthY ^ 2 := by
    rw [pow_two, pow_two]
    exact Arithmetic.mul_le_mul_direct yWidth yWidth
      inner.widthY_nonneg outer.widthY_nonneg
  exact add_le_add xSquare ySquare

end Purelib.Geometry.Rational.Box

namespace Purelib.Geometry.Rational.Box.Bounds

/-- The displayed corner opposite the fixed lower-left box anchor.

The original upper real and imaginary endpoints determine this Gaussian
corner. The lower endpoints still determine the unchanged box anchor. -/
@[expose] public def oppositeCorner (box : Box) : Data.Gaussian.Basic.Canonical :=
  ⟨box.xUpper, box.yUpper⟩

/-- The quadrance between opposite box corners equals the squared box diagonal.

The original lower-endpoint anchor and upper-endpoint corner differ by
the two signed side lengths. Squaring those coordinates gives precisely
the retained squared diagonal. -/
public theorem normSq_anchor_sub_oppositeCorner
    (box : Box) :
    Basic.normSq (box.anchor - oppositeCorner box) =
      box.diagonalSq := by
  simp only [anchor, oppositeCorner,
    Basic.normSq,
    Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, diagonalSq_eq_original]
  ring1

end Purelib.Geometry.Rational.Box.Bounds

namespace Purelib.Geometry.Rational.Box

/-- Refining a box cannot increase the maximum squared endpoint coordinate.

Both inner endpoints lie between the original outer endpoints in each
coordinate. Their four square bounds combine under the same nested
maximum operations. -/
public theorem coordinateSqBound_le_of_refines {inner outer : Box}
    (refines : inner.Refines outer) :
    inner.coordinateSqBound ≤ outer.coordinateSqBound := by
  rewrite [coordinateSqBound_eq_original, coordinateSqBound_eq_original]
  apply Basic.max_le
  · apply Basic.max_le
    · exact (sq_le_endpoint_max refines.1
        (inner.x_valid.trans refines.2.1)).trans (Basic.le_max_left _ _)
    · exact (sq_le_endpoint_max (refines.1.trans inner.x_valid)
        refines.2.1).trans (Basic.le_max_left _ _)
  · apply Basic.max_le
    · exact (sq_le_endpoint_max refines.2.2.1
        (inner.y_valid.trans refines.2.2.2)).trans (Basic.le_max_right _ _)
    · exact (sq_le_endpoint_max (refines.2.2.1.trans inner.y_valid)
        refines.2.2.2).trans (Basic.le_max_right _ _)

/-- Refining a box cannot increase its endpoint-based Gaussian squared-norm bound.

Refinement decreases the original maximum of endpoint squares.
Multiplication by the same nonnegative factor two preserves the comparison. -/
public theorem normSqBound_le_of_refines {inner outer : Box}
    (refines : inner.Refines outer) : inner.normSqBound ≤ outer.normSqBound :=
  Arithmetic.mul_le_mul_of_nonneg_left_direct
    (coordinateSqBound_le_of_refines refines) (by decide)

end Purelib.Geometry.Rational.Box
