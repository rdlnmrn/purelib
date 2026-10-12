module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
public import Purelib.Approximation.Gaussian.SignedDigit.Cell
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Dyadic
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.SignedDigit

open Purelib.Approximation.Gaussian.SignedDigit.Cell

open Purelib.Approximation.Rational

open Purelib.Data.Rat

section
public section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

namespace Purelib.Approximation.Gaussian.SignedDigit.Cell

/-- Any two readings of a signed-digit cell have the explicit squared distance bound `8 * tail²`. -/
theorem normSq_sub_le_eight_tailSq {cell : Cell}
    {left right : Data.Gaussian.Basic.Canonical} (leftInside : cell.Contains left)
    (rightInside : cell.Contains right) :
    Data.Gaussian.Norm.Basic.normSq (left - right) ≤ 8 * cell.tail ^ 2 := by
  have leftRealSquare := Bounds.Square.sq_le_sq_of_bounds
    (by
      calc
        -cell.tail = (cell.center.re - cell.tail) - cell.center.re := by ring1
        _ ≤ left.re - cell.center.re :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct leftInside.1 _)
    (by
      calc
        left.re - cell.center.re ≤
            (cell.center.re + cell.tail) - cell.center.re :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct
            leftInside.2.1 _
        _ = cell.tail := by ring1)
  have leftImagSquare := Bounds.Square.sq_le_sq_of_bounds
    (by
      calc
        -cell.tail = (cell.center.im - cell.tail) - cell.center.im := by ring1
        _ ≤ left.im - cell.center.im :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct
            leftInside.2.2.1 _)
    (by
      calc
        left.im - cell.center.im ≤
            (cell.center.im + cell.tail) - cell.center.im :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct
            leftInside.2.2.2 _
        _ = cell.tail := by ring1)
  have leftBound : Data.Gaussian.Norm.Basic.normSq (left - cell.center) ≤ 2 * cell.tail ^ 2 := by
    change (left.re - cell.center.re) ^ 2 +
      (left.im - cell.center.im) ^ 2 ≤ _
    exact
      (Fraction.Order.Arithmetic.add_le_add_direct
        leftRealSquare leftImagSquare).trans_eq (by ring1)
  have rightRealSquare := Bounds.Square.sq_le_sq_of_bounds
    (by
      calc
        -cell.tail = (cell.center.re - cell.tail) - cell.center.re := by ring1
        _ ≤ right.re - cell.center.re :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct rightInside.1 _)
    (by
      calc
        right.re - cell.center.re ≤
            (cell.center.re + cell.tail) - cell.center.re :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct
            rightInside.2.1 _
        _ = cell.tail := by ring1)
  have rightImagSquare := Bounds.Square.sq_le_sq_of_bounds
    (by
      calc
        -cell.tail = (cell.center.im - cell.tail) - cell.center.im := by ring1
        _ ≤ right.im - cell.center.im :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct
            rightInside.2.2.1 _)
    (by
      calc
        right.im - cell.center.im ≤
            (cell.center.im + cell.tail) - cell.center.im :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct
            rightInside.2.2.2 _
        _ = cell.tail := by ring1)
  have rightForward : Data.Gaussian.Norm.Basic.normSq (right - cell.center) ≤
      2 * cell.tail ^ 2 := by
    change (right.re - cell.center.re) ^ 2 +
      (right.im - cell.center.im) ^ 2 ≤ _
    exact
      (Fraction.Order.Arithmetic.add_le_add_direct
        rightRealSquare rightImagSquare).trans_eq (by ring1)
  have rightBound : Data.Gaussian.Norm.Basic.normSq (cell.center - right) ≤
      2 * cell.tail ^ 2 := by
    have identity : cell.center - right = -(right - cell.center) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.neg_re,
          Data.Gaussian.Basic.neg_im] <;> ring1
    rw [identity, Data.Gaussian.Norm.Basic.normSq_neg]
    exact rightForward
  calc
    Data.Gaussian.Norm.Basic.normSq (left - right) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq (left - cell.center) +
          Data.Gaussian.Norm.Basic.normSq (cell.center - right)) :=
      Data.Gaussian.Norm.Bounds.normSq_sub_le_via left cell.center right
    _ ≤ 2 * ((2 * cell.tail ^ 2) + (2 * cell.tail ^ 2)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct leftBound rightBound)
        (by decide)
    _ = 8 * cell.tail ^ 2 := by ring1

/-- The signed-digit precision allowance equals twice the square of its retained coordinate tail radius. -/
theorem precisionSq_eq_two_tailSq (cell : Cell) :
    cell.precisionSq = 2 * cell.tail ^ 2 := by
  rw [Cell.precisionSq, Geometric.Basic.quarterRadius_eq_mul_pow]
  unfold Cell.tail Cell.factor
  calc
    2 * cell.scale ^ 2 * (1 / 4 : Fraction.Rational) ^ cell.depth =
        2 * cell.scale ^ 2 *
          (((1 / 2 : Fraction.Rational) ^ cell.depth) ^ 2) := by
      rw [Dyadic.half_pow_sq]
    _ = 2 * (cell.scale * (1 / 2 : Fraction.Rational) ^ cell.depth) ^ 2 := by
      ring1

/-- Enclose a signed-digit cell by the ball with the same centre and twice its squared tail radius. -/
@[expose] def toBall (cell : Cell) : Enclosure.Ball :=
  { center := cell.center
    radiusSq := 2 * cell.tail ^ 2
    radiusSq_nonneg :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.sq_nonneg_direct cell.tail) }

/-- Every reading admitted by a signed-digit cell is admitted by its enclosing rational ball. -/
theorem toBall_contains {cell : Cell} {value : Data.Gaussian.Basic.Canonical}
    (inside : cell.Contains value) : cell.toBall.Contains value := by
  change (value.re - cell.center.re) ^ 2 +
    (value.im - cell.center.im) ^ 2 ≤ 2 * cell.tail ^ 2
  have realSquare := Bounds.Square.sq_le_sq_of_bounds
    (by
      calc
        -cell.tail = (cell.center.re - cell.tail) - cell.center.re := by ring1
        _ ≤ value.re - cell.center.re := Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.1 _)
    (by
      calc
        value.re - cell.center.re ≤
            (cell.center.re + cell.tail) - cell.center.re :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2.1 _
        _ = cell.tail := by ring1)
  have imagSquare := Bounds.Square.sq_le_sq_of_bounds
    (by
      calc
        -cell.tail = (cell.center.im - cell.tail) - cell.center.im := by ring1
        _ ≤ value.im - cell.center.im :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2.2.1 _)
    (by
      calc
        value.im - cell.center.im ≤
            (cell.center.im + cell.tail) - cell.center.im :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2.2.2 _
        _ = cell.tail := by ring1)
  exact
    (Fraction.Order.Arithmetic.add_le_add_direct realSquare imagSquare).trans_eq
      (by ring1)
end Purelib.Approximation.Gaussian.SignedDigit.Cell

end
