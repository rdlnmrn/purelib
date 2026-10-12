module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Basic
import Init.Prelude
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
public import Mathlib.Order.Basic

open Purelib

open Purelib.Geometry

section
@[expose] public section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

namespace Purelib.Geometry.Rational.Box.Hull

/-! ## Finite coordinatewise hulls -/

section
open Purelib.Data
open Purelib.Data.Rat
/-- Coordinatewise rational hull of two boxes. -/
def hull (left right : Rational.Box) :
  Rational.Box where
  xLower := min left.xLower right.xLower
  xUpper := max left.xUpper right.xUpper
  yLower := min left.yLower right.yLower
  yUpper := max left.yUpper right.yUpper
  x_valid := (Fraction.Order.Basic.min_le_left _ _).trans (left.x_valid.trans (Fraction.Order.Basic.le_max_left _ _))
  y_valid := (Fraction.Order.Basic.min_le_left _ _).trans (left.y_valid.trans (Fraction.Order.Basic.le_max_left _ _))

/-- The coordinatewise hull contains every point of its left box. -/
theorem hull_contains_left {left right : Rational.Box} {value
  : Data.Gaussian.Basic.Canonical}
    (inside : left.Contains value) : (hull left right).Contains value :=
  ⟨(Fraction.Order.Basic.min_le_left _ _).trans inside.1,
    inside.2.1.trans (Fraction.Order.Basic.le_max_left _ _),
    (Fraction.Order.Basic.min_le_left _ _).trans inside.2.2.1,
    inside.2.2.2.trans (Fraction.Order.Basic.le_max_left _ _)⟩

/-- The coordinatewise hull contains every point of its right box. -/
theorem hull_contains_right {left right : Rational.Box} {value
  : Data.Gaussian.Basic.Canonical}
    (inside : right.Contains value) : (hull left right).Contains value :=
  ⟨(Fraction.Order.Basic.min_le_right _ _).trans inside.1,
    inside.2.1.trans (Fraction.Order.Basic.le_max_right _ _),
    (Fraction.Order.Basic.min_le_right _ _).trans inside.2.2.1,
    inside.2.2.2.trans (Fraction.Order.Basic.le_max_right _ _)⟩

end

/-- Hull a finite candidate list, using an explicit fallback for the empty list. In the parser application the fallback
is the previous coarse box. -/
def hullList (fallback : Purelib.Geometry.Rational.Box) : List
  Purelib.Geometry.Rational.Box → Purelib.Geometry.Rational.Box
  | [] => fallback
  | box :: remaining => hull box (hullList
    fallback remaining)

open Purelib.Data in
open Purelib.Data.Rat in
/-- The finite hull contains every point belonging to any listed box. -/
theorem hullList_contains_of_mem
    {fallback candidate : Rational.Box} {candidates : List Rational.Box} {value :
      Data.Gaussian.Basic.Canonical}
    (member : candidate ∈ candidates) (inside : candidate.Contains value) :
    (hullList fallback candidates).Contains value := by
  induction candidates with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      rcases List.Membership.mem_cons.mp member with equal | member
      · subst head
        exact hull_contains_left inside
      · exact hull_contains_right (inductionHypothesis member)

end Purelib.Geometry.Rational.Box.Hull

end
