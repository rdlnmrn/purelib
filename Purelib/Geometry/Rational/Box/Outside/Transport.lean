module

public import Purelib.Geometry.Rational.Box.Outside
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Transport of retained outside sides

A selected coordinate side has an exact positive gap. Moving the original
point by less than that gap preserves the same side constructor and leaves
an explicit lower bound for its original squared clearance margin.
-/

public section

namespace Purelib.Geometry.Rational.Box.OutsideSide

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Fraction.Order

/-- The unsquared coordinate gap of the original selected outside side. -/
@[expose] def gap {box : Box} {point : Canonical} : OutsideSide box point → Fraction.Rational
  | .left _ => box.xLower - point.re
  | .right _ => point.re - box.xUpper
  | .bottom _ => box.yLower - point.im
  | .top _ => point.im - box.yUpper

/-- Every original outside side has a strictly positive coordinate gap. -/
theorem gap_positive {box : Box} {point : Canonical} (side : OutsideSide box point) : 0 < side.gap := by
  cases side <;> exact Arithmetic.sub_pos_direct (by assumption)

/-- The original squared outside-side margin is exactly the square of its retained coordinate gap. -/
theorem margin_eq_gap_sq {box : Box} {point : Canonical} (side : OutsideSide box point) :
    side.margin = side.gap ^ 2 := by
  cases side <;> rfl

/-- Transport the same original side to a point with sufficiently small coordinate displacement.

The original side constructor is retained. Both coordinate displacements
lie between the displayed signed radius bounds, and that radius is below
the original selected gap. No new outside-side selection is performed. -/
@[expose] def rebase {box : Box} {point : Canonical} (side : OutsideSide box point)
    (target : Canonical) (radius : Fraction.Rational) (small : radius < side.gap)
    (near : -radius ≤ target.re - point.re ∧ target.re - point.re ≤ radius ∧
      -radius ≤ target.im - point.im ∧ target.im - point.im ≤ radius) : OutsideSide box target := by
  cases side with
  | left less =>
      apply OutsideSide.left
      calc
        target.re = point.re + (target.re - point.re) := by ring1
        _ ≤ point.re + radius := Arithmetic.add_le_add_direct le_rfl near.2.1
        _ < point.re + (box.xLower - point.re) := Arithmetic.add_lt_add_left_direct small point.re
        _ = box.xLower := by ring1
  | right less =>
      apply OutsideSide.right
      calc
        box.xUpper = point.re - (point.re - box.xUpper) := by ring1
        _ < point.re - radius := Arithmetic.sub_lt_sub_left_direct small point.re
        _ = point.re + (-radius) := by ring1
        _ ≤ point.re + (target.re - point.re) := Arithmetic.add_le_add_direct le_rfl near.1
        _ = target.re := by ring1
  | bottom less =>
      apply OutsideSide.bottom
      calc
        target.im = point.im + (target.im - point.im) := by ring1
        _ ≤ point.im + radius := Arithmetic.add_le_add_direct le_rfl near.2.2.2
        _ < point.im + (box.yLower - point.im) := Arithmetic.add_lt_add_left_direct small point.im
        _ = box.yLower := by ring1
  | top less =>
      apply OutsideSide.top
      calc
        box.yUpper = point.im - (point.im - box.yUpper) := by ring1
        _ < point.im - radius := Arithmetic.sub_lt_sub_left_direct small point.im
        _ = point.im + (-radius) := by ring1
        _ ≤ point.im + (target.im - point.im) := Arithmetic.add_le_add_direct le_rfl near.2.2.1
        _ = target.im := by ring1

/-- Rebasing an original outside side loses at most the displayed coordinate radius from its same gap. -/
theorem rebase_gap_lower {box : Box} {point : Canonical} (side : OutsideSide box point)
    (target : Canonical) (radius : Fraction.Rational) (small : radius < side.gap)
    (near : -radius ≤ target.re - point.re ∧ target.re - point.re ≤ radius ∧
      -radius ≤ target.im - point.im ∧ target.im - point.im ≤ radius) :
    side.gap - radius ≤ (side.rebase target radius small near).gap := by
  cases side with
  | left less =>
      change (box.xLower - point.re) - radius ≤ box.xLower - target.re
      calc
        _ ≤ (box.xLower - point.re) - (target.re - point.re) :=
          Arithmetic.sub_le_sub_left_direct near.2.1 _
        _ = box.xLower - target.re := by ring1
  | right less =>
      change (point.re - box.xUpper) - radius ≤ target.re - box.xUpper
      calc
        _ = (point.re - box.xUpper) + (-radius) := by ring1
        _ ≤ (point.re - box.xUpper) + (target.re - point.re) :=
          Arithmetic.add_le_add_direct le_rfl near.1
        _ = target.re - box.xUpper := by ring1
  | bottom less =>
      change (box.yLower - point.im) - radius ≤ box.yLower - target.im
      calc
        _ ≤ (box.yLower - point.im) - (target.im - point.im) :=
          Arithmetic.sub_le_sub_left_direct near.2.2.2 _
        _ = box.yLower - target.im := by ring1
  | top less =>
      change (point.im - box.yUpper) - radius ≤ target.im - box.yUpper
      calc
        _ = (point.im - box.yUpper) + (-radius) := by ring1
        _ ≤ (point.im - box.yUpper) + (target.im - point.im) :=
          Arithmetic.add_le_add_direct le_rfl near.2.2.1
        _ = target.im - box.yUpper := by ring1

/-- The same rebased outside-side margin bounds the square of its remaining original gap. -/
theorem rebase_margin_lower {box : Box} {point : Canonical} (side : OutsideSide box point)
    (target : Canonical) (radius : Fraction.Rational) (small : radius < side.gap)
    (near : -radius ≤ target.re - point.re ∧ target.re - point.re ≤ radius ∧
      -radius ≤ target.im - point.im ∧ target.im - point.im ≤ radius) :
    (side.gap - radius) ^ 2 ≤ (side.rebase target radius small near).margin := by
  rewrite [margin_eq_gap_sq]
  exact Arithmetic.pow_le_pow_direct (Arithmetic.sub_nonneg_direct small.le)
    (side.rebase_gap_lower target radius small near) 2

end Purelib.Geometry.Rational.Box.OutsideSide
