module
meta import Mathlib.Tactic.Linter.Lint
public import Purelib.Geometry.Rational.Box.Refinement

import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
public import Mathlib.Order.Basic

public section

/-!
# Intersections of finitely cleared boxes

A supplied common subbox certifies nonemptiness.  The four intersection sides
are selected from the original sides, so their boundary clearance is at least
the smaller original clearance; no new boundary scan is needed.
-/

namespace Purelib.Geometry.Rational.Box.Intersection

open Purelib
open Purelib.Geometry
open Purelib.Data.Rat

section Boxes.Box

/-- Intersect box coordinates using a retained common subbox.

Each lower endpoint is the maximum of the two original lower endpoints; each
upper endpoint is their minimum. The supplied refinement witnesses and original
common-box ordering certify the selected endpoint order. -/
@[expose] def intersection (first second common : Rational.Box)
    (inFirst : common.Refines first) (inSecond : common.Refines second) : Rational.Box where
  xLower := max first.xLower second.xLower
  xUpper := min first.xUpper second.xUpper
  yLower := max first.yLower second.yLower
  yUpper := min first.yUpper second.yUpper
  x_valid := (Fraction.Order.Basic.max_le inFirst.1 inSecond.1).trans
    (common.x_valid.trans (Fraction.Order.Basic.le_min inFirst.2.1 inSecond.2.1))
  y_valid := (Fraction.Order.Basic.max_le inFirst.2.2.1 inSecond.2.2.1).trans
    (common.y_valid.trans (Fraction.Order.Basic.le_min inFirst.2.2.2 inSecond.2.2.2))

variable {first second common : Purelib.Geometry.Rational.Box} {inFirst : common.Refines first}
  {inSecond : common.Refines second}

/-- The certified coordinate intersection refines its first input box. -/
theorem intersection_refines_first : (intersection first second common inFirst inSecond).Refines first :=
  ⟨Fraction.Order.Basic.le_max_left _ _, Fraction.Order.Basic.min_le_left _ _,
    Fraction.Order.Basic.le_max_left _ _, Fraction.Order.Basic.min_le_left _ _⟩

/-- The certified coordinate intersection refines its second input box. -/
theorem intersection_refines_second : (intersection first second common inFirst inSecond).Refines second :=
  ⟨Fraction.Order.Basic.le_max_right _ _, Fraction.Order.Basic.min_le_right _ _,
    Fraction.Order.Basic.le_max_right _ _, Fraction.Order.Basic.min_le_right _ _⟩

/-- A box strictly inside both inputs is strictly inside their certified intersection.

Each selected lower endpoint retains one original strict lower bound. Both
original strict upper bounds bound the selected minimum, preserving the exact
common box and its two refinement witnesses. -/
theorem strictInterior_intersection (strictFirst : common.StrictInterior first)
    (strictSecond : common.StrictInterior second) :
    common.StrictInterior (intersection first second common inFirst inSecond) := by
  have left : max first.xLower second.xLower < common.xLower := by
    change (if first.xLower ≤ second.xLower then second.xLower else first.xLower) < common.xLower
    split
    · exact strictSecond.left
    · exact strictFirst.left
  have bottom : max first.yLower second.yLower < common.yLower := by
    change (if first.yLower ≤ second.yLower then second.yLower else first.yLower) < common.yLower
    split
    · exact strictSecond.bottom
    · exact strictFirst.bottom
  exact ⟨left, Fraction.Order.Basic.lt_min strictFirst.right strictSecond.right,
    bottom, Fraction.Order.Basic.lt_min strictFirst.top strictSecond.top⟩

/-- A common strictly interior box certifies positive intersection width and height.

The common box retains its weak endpoint ordering. Its strict lower and upper
intersection bounds compose through that ordering to prove both strict side
comparisons. -/
theorem intersection_proper (strictFirst : common.StrictInterior first)
    (strictSecond : common.StrictInterior second) :
    (intersection first second common inFirst inSecond).Proper := by
  have strict := strictInterior_intersection (inFirst := inFirst) (inSecond := inSecond) strictFirst strictSecond
  exact ⟨(strict.left.trans_le common.x_valid).trans strict.right,
    (strict.bottom.trans_le common.y_valid).trans strict.top⟩
end Boxes.Box

end Purelib.Geometry.Rational.Box.Intersection

end
