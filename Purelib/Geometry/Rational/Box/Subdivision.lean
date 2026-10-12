module
public import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
public import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Symmetric boxes and certified coordinate cuts

A nonnegative radius determines a box centered at zero. A displayed cut inside
one coordinate interval retains the other interval and supplies both child
order certificates directly from the same parent and cut witnesses.
-/

namespace Purelib.Geometry.Rational.Box

-- Retain the established Box declaration names.
open Purelib.Data.Rat
open Purelib.Geometry.Rational (Box)

/-- The square centered at zero with the given nonnegative coordinate radius.

The four endpoints are negative and positive copies of the supplied radius. Direct rational negation order certifies
both closed coordinate intervals. -/
@[expose] public def symmetric (radius : Fraction.Rational) (nonnegative : 0 ≤ radius) : Box where
  xLower := -radius
  xUpper := radius
  yLower := -radius
  yUpper := radius
  x_valid := by
    have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct nonnegative
    change -radius ≤ (0 : Fraction.Rational) at reversed
    exact reversed.trans nonnegative
  y_valid := by
    have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct nonnegative
    change -radius ≤ (0 : Fraction.Rational) at reversed
    exact reversed.trans nonnegative

/-- Left child produced by a certified vertical cut.

The lower real endpoint and both imaginary endpoints remain those of the parent. The supplied lower cut bound certifies
the shortened real interval. -/
@[expose] public def verticalLeft (B : Box) (cut : Fraction.Rational)
    (inside : B.xLower ≤ cut ∧ cut ≤ B.xUpper) : Box where
  xLower := B.xLower
  xUpper := cut
  yLower := B.yLower
  yUpper := B.yUpper
  x_valid := inside.1
  y_valid := B.y_valid

/-- Right child produced by a certified vertical cut.

The upper real endpoint and both imaginary endpoints remain those of the parent. The supplied upper cut bound certifies
the shortened real interval. -/
@[expose] public def verticalRight (B : Box) (cut : Fraction.Rational)
    (inside : B.xLower ≤ cut ∧ cut ≤ B.xUpper) : Box where
  xLower := cut
  xUpper := B.xUpper
  yLower := B.yLower
  yUpper := B.yUpper
  x_valid := inside.2
  y_valid := B.y_valid

/-- The left child of a certified vertical cut refines its parent box.

The unchanged endpoints satisfy reflexive bounds; the retained upper cut bound supplies containment of the new real
endpoint. -/
public theorem verticalLeft_refines (B : Box) (cut : Fraction.Rational)
    (inside : B.xLower ≤ cut ∧ cut ≤ B.xUpper) :
    (B.verticalLeft cut inside).Refines B :=
  ⟨le_rfl, inside.2, le_rfl, le_rfl⟩

/-- The right child of a certified vertical cut refines its parent box.

The unchanged endpoints satisfy reflexive bounds; the retained lower cut bound supplies containment of the new real
endpoint. -/
public theorem verticalRight_refines (B : Box) (cut : Fraction.Rational)
    (inside : B.xLower ≤ cut ∧ cut ≤ B.xUpper) :
    (B.verticalRight cut inside).Refines B :=
  ⟨inside.1, le_rfl, le_rfl, le_rfl⟩

/-- Lower child produced by a certified horizontal cut.

Both real endpoints and the lower imaginary endpoint remain those of the parent. The supplied lower cut bound certifies
the shortened imaginary interval. -/
@[expose] public def horizontalLower (B : Box) (cut : Fraction.Rational)
    (inside : B.yLower ≤ cut ∧ cut ≤ B.yUpper) : Box where
  xLower := B.xLower
  xUpper := B.xUpper
  yLower := B.yLower
  yUpper := cut
  x_valid := B.x_valid
  y_valid := inside.1

/-- Upper child produced by a certified horizontal cut.

Both real endpoints and the upper imaginary endpoint remain those of the parent. The supplied upper cut bound certifies
the shortened imaginary interval. -/
@[expose] public def horizontalUpper (B : Box) (cut : Fraction.Rational)
    (inside : B.yLower ≤ cut ∧ cut ≤ B.yUpper) : Box where
  xLower := B.xLower
  xUpper := B.xUpper
  yLower := cut
  yUpper := B.yUpper
  x_valid := B.x_valid
  y_valid := inside.2

/-- The lower child of a certified horizontal cut refines its parent box.

The unchanged endpoints satisfy reflexive bounds; the retained upper cut bound supplies containment of the new imaginary
endpoint. -/
public theorem horizontalLower_refines (B : Box) (cut : Fraction.Rational)
    (inside : B.yLower ≤ cut ∧ cut ≤ B.yUpper) :
    (B.horizontalLower cut inside).Refines B :=
  ⟨le_rfl, le_rfl, le_rfl, inside.2⟩

/-- The upper child of a certified horizontal cut refines its parent box.

The unchanged endpoints satisfy reflexive bounds; the retained lower cut bound supplies containment of the new imaginary
endpoint. -/
public theorem horizontalUpper_refines (B : Box) (cut : Fraction.Rational)
    (inside : B.yLower ≤ cut ∧ cut ≤ B.yUpper) :
    (B.horizontalUpper cut inside).Refines B :=
  ⟨le_rfl, le_rfl, inside.1, le_rfl⟩

end Purelib.Geometry.Rational.Box
