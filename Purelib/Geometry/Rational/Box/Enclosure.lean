module

public import Purelib.Geometry.Rational.Box.Bounds
public import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic

/-! # An exact finite ball enclosing a rational box -/

public section

namespace Purelib.Geometry.Rational.Box

open Purelib.Approximation.Gaussian
open Purelib.Data.Rat

/-- Enclose the original box by the ball at its lower corner with its exact squared diagonal. -/
@[expose] def enclosure (box : Box) : Enclosure.Ball :=
  ⟨box.anchor, box.diagonalSq, box.diagonalSq_nonneg⟩

/-- Every point in the original box belongs to that same finite enclosing ball. -/
theorem inside_enclosure {box : Box} {point : Purelib.Data.Gaussian.Basic.Canonical} (inside : box.Contains point) :
    box.enclosure.Contains point := box.normSq_sub_anchor_le inside

/-- The nonnegative endpoint radius of a centered square enclosing the original box. -/
@[expose] def enclosingRadius (box : Box) : Fraction.Rational :=
  max 0 (max (max (-box.xLower) box.xUpper) (max (-box.yLower) box.yUpper))

/-- The original endpoint enclosure retains its explicit nonnegative zero floor. -/
theorem enclosingRadius_nonneg (box : Box) : 0 ≤ box.enclosingRadius :=
  Fraction.Order.Basic.le_max_left _ _

/-- The original box refines every centered square whose radius exceeds its computed endpoint enclosure. -/
theorem refines_symmetric_of_enclosingRadius_le (box : Box) {radius : Fraction.Rational}
    (nonnegative : 0 ≤ radius) (enclosed : box.enclosingRadius ≤ radius) :
    box.Refines (Box.symmetric radius nonnegative) := by
  have core : max (max (-box.xLower) box.xUpper) (max (-box.yLower) box.yUpper) ≤ radius :=
    (Fraction.Order.Basic.le_max_right _ _).trans enclosed
  have horizontal : max (-box.xLower) box.xUpper ≤ radius :=
    (Fraction.Order.Basic.le_max_left _ _).trans core
  have vertical : max (-box.yLower) box.yUpper ≤ radius :=
    (Fraction.Order.Basic.le_max_right _ _).trans core
  have left := Fraction.Order.Arithmetic.neg_le_neg_direct
    ((Fraction.Order.Basic.le_max_left _ _).trans horizontal)
  have bottom := Fraction.Order.Arithmetic.neg_le_neg_direct
    ((Fraction.Order.Basic.le_max_left _ _).trans vertical)
  have doubleLeft : -(-box.xLower) = box.xLower := by ring1
  have doubleBottom : -(-box.yLower) = box.yLower := by ring1
  rewrite [doubleLeft] at left
  rewrite [doubleBottom] at bottom
  exact ⟨left, (Fraction.Order.Basic.le_max_right _ _).trans horizontal,
    bottom, (Fraction.Order.Basic.le_max_right _ _).trans vertical⟩

/-- The nonnegative maximum of the original endpoint enclosure radii of a finite ordered box list. -/
@[expose] def enclosureRadius : List Box → Fraction.Rational
  | [] => 0
  | box :: rest => max box.enclosingRadius (enclosureRadius rest)

/-- Every computed finite-family enclosure radius is nonnegative. -/
theorem enclosureRadius_nonneg : (boxes : List Box) → 0 ≤ enclosureRadius boxes
  | [] => Fraction.Order.Basic.le_refl 0
  | box :: _ => box.enclosingRadius_nonneg.trans (Fraction.Order.Basic.le_max_left _ _)

/-- Each retained occurrence's endpoint radius lies below the same original finite family's enclosure radius. -/
theorem enclosingRadius_le_of_mem {box : Box} {boxes : List Box} (member : box ∈ boxes) :
    box.enclosingRadius ≤ enclosureRadius boxes := by
  induction member with
  | head => exact Fraction.Order.Basic.le_max_left _ _
  | tail _ _ inductionHypothesis => exact inductionHypothesis.trans (Fraction.Order.Basic.le_max_right _ _)

end Purelib.Geometry.Rational.Box

end
