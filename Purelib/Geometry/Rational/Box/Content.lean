module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Dimensions
public import Purelib.Geometry.Rational.Box.Point
public import Purelib.Geometry.Rational.Box.Subdivision
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

@[expose] public section

/-!
# Finite rational content of RFAP boxes

Axis-aligned rational boxes have an exact executable area.  Finite covers and
effective nullity are request protocols returning only displayed box lists;
no outer-measure infimum or collection of all covers is formed.
-/

namespace Purelib.Geometry.Rational.Box.Content

/-- Exact rational area of a displayed RFAP box. -/
def boxContent (box : Rational.Box) : Fraction.Rational :=
  box.widthX * box.widthY

/-- The exact rational area of an ordered box is nonnegative. -/
theorem boxContent_nonneg (box : Rational.Box) : 0 ≤
  boxContent box :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    box.widthX_nonneg box.widthY_nonneg

/-- Every proper displayed rational box has strictly positive exact area. -/
theorem boxContent_pos_of_proper {box : Rational.Box}
  (proper : box.Proper) :
    0 < boxContent box := by
  unfold boxContent Rational.Box.widthX Rational.Box.widthY
  exact Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Arithmetic.sub_pos_direct proper.1)
    (Fraction.Order.Arithmetic.sub_pos_direct proper.2)

/-- Rational box refinement cannot increase exact box content. -/
theorem boxContent_le_of_refines {inner outer :
  Rational.Box}
    (refines : inner.Refines outer) :
    boxContent inner ≤ boxContent outer :=
  Fraction.Order.Arithmetic.mul_le_mul_direct
    (Rational.Box.widthX_le_of_refines refines)
    (Rational.Box.widthY_le_of_refines refines)
    inner.widthY_nonneg outer.widthX_nonneg

/-- Box area is at most half its displayed squared diagonal. -/
theorem boxContent_le_half_diagonalSq (box : Rational.Box)
  :
    boxContent box ≤ box.diagonalSq / 2 := by
  apply (Fraction.Order.Field.le_div_iff_pos
    (by decide : (0 : Fraction.Rational) < 2)).2
  calc
    boxContent box * 2 = 2 * (box.widthX * box.widthY) := by
      dsimp only [boxContent]
      ring1
    _ ≤ 2 * (box.widthX * box.widthY) +
          (box.widthX - box.widthY) ^ 2 :=
      le_add_of_nonneg_right
        (Fraction.Order.Arithmetic.sq_nonneg_direct
          (box.widthX - box.widthY))
    _ = box.diagonalSq := by
      dsimp only [Rational.Box.diagonalSq, Rational.Box.widthX,
        Rational.Box.widthY]
      ring1

/-- Half the squared box diagonal is bounded by the full squared diagonal. -/
theorem half_diagonalSq_le_diagonalSq (box : Rational.Box)
  :
    box.diagonalSq / 2 ≤ box.diagonalSq := by
  apply (Fraction.Order.Field.div_le_iff_pos
    (by decide : (0 : Fraction.Rational) < 2)).2
  calc
    box.diagonalSq ≤ box.diagonalSq + box.diagonalSq :=
      le_add_of_nonneg_right box.diagonalSq_nonneg
    _ = box.diagonalSq * 2 := by ring1

/-- The exact box area is bounded by its squared diagonal. -/
theorem boxContent_le_diagonalSq (box : Rational.Box) :
    boxContent box ≤ box.diagonalSq :=
  (boxContent_le_half_diagonalSq box).trans
    (half_diagonalSq_le_diagonalSq box)

/-- A squared-diagonal request is also a strict area request. -/
theorem boxContent_lt_of_diagonalSq_lt {box : Rational.Box}
  {target : Fraction.Rational}
    (small : box.diagonalSq < target) : boxContent box < target :=
  (boxContent_le_diagonalSq box).trans_lt small

/-- Exact finite additivity across a displayed vertical cut. -/
theorem vertical_content_add (box : Rational.Box) (cut :
  Fraction.Rational)
    (inside : box.xLower ≤ cut ∧ cut ≤ box.xUpper) :
    boxContent (box.verticalLeft cut inside) +
      boxContent (box.verticalRight cut inside) = boxContent
        box := by
  dsimp only [boxContent, Rational.Box.widthX,
    Rational.Box.widthY, Rational.Box.verticalLeft,
    Rational.Box.verticalRight]
  ring1

/-- Exact finite additivity across a displayed horizontal cut. -/
theorem horizontal_content_add (box : Rational.Box) (cut :
  Fraction.Rational)
    (inside : box.yLower ≤ cut ∧ cut ≤ box.yUpper) :
    boxContent (box.horizontalLower cut inside) +
      boxContent (box.horizontalUpper cut inside) =
        boxContent box := by
  dsimp only [boxContent, Rational.Box.widthX,
    Rational.Box.widthY, Rational.Box.horizontalLower,
    Rational.Box.horizontalUpper]
  ring1

/-- The degenerate box at a single point has zero area. -/
@[simp] theorem pointBox_content (point : Data.Gaussian.Basic.Canonical) :
    boxContent (Rational.Box.Point.pointBox point) = 0 := by
  dsimp only [boxContent, Rational.Box.Point.pointBox,
    Rational.Box.widthX,
    Rational.Box.widthY]
  ring1
end Purelib.Geometry.Rational.Box.Content

end
