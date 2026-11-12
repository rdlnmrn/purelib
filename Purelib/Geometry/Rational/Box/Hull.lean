module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Point
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring
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

/-- The coordinatewise hull refines every box containing both original boxes.

The lower coordinates are the original minima and the upper coordinates
are the original maxima. Their four comparison laws retain both supplied
refinement certificates without selecting a new point or box.
-/
theorem refines {left right outer : Rational.Box}
    (leftRefines : left.Refines outer) (rightRefines : right.Refines outer) :
    (hull left right).Refines outer :=
  ⟨Fraction.Order.Basic.le_min leftRefines.1 rightRefines.1,
    Fraction.Order.Basic.max_le leftRefines.2.1 rightRefines.2.1,
    Fraction.Order.Basic.le_min leftRefines.2.2.1 rightRefines.2.2.1,
    Fraction.Order.Basic.max_le leftRefines.2.2.2 rightRefines.2.2.2⟩

/-- The hull of two point boxes has exactly the squared distance of its original points as diagonal.

Coordinate order only chooses the direction of each side. Squaring those
same endpoint differences gives the original Gaussian quadrance, including
coincident endpoints and degenerate horizontal or vertical rectangles.
-/
theorem pointBoxes_diagonalSq (start finish : Gaussian.Basic.Canonical) :
    (hull (Point.pointBox start) (Point.pointBox finish)).diagonalSq =
      Gaussian.Norm.Basic.normSq (finish - start) := by
  rewrite [diagonalSq_eq_original]
  change (max start.re finish.re - min start.re finish.re) ^ 2 +
    (max start.im finish.im - min start.im finish.im) ^ 2 =
      (finish.re - start.re) ^ 2 + (finish.im - start.im) ^ 2
  rcases Fraction.Order.Basic.le_total start.re finish.re with horizontal | horizontal
  · rcases Fraction.Order.Basic.le_total start.im finish.im with vertical | vertical
    · rewrite [Fraction.Order.Basic.min_eq_left horizontal, Fraction.Order.Basic.max_eq_right horizontal,
        Fraction.Order.Basic.min_eq_left vertical, Fraction.Order.Basic.max_eq_right vertical]
      rfl
    · rewrite [Fraction.Order.Basic.min_eq_left horizontal, Fraction.Order.Basic.max_eq_right horizontal,
        Fraction.Order.Basic.min_eq_right vertical, Fraction.Order.Basic.max_eq_left vertical]
      ring1
  · rcases Fraction.Order.Basic.le_total start.im finish.im with vertical | vertical
    · rewrite [Fraction.Order.Basic.min_eq_right horizontal, Fraction.Order.Basic.max_eq_left horizontal,
        Fraction.Order.Basic.min_eq_left vertical, Fraction.Order.Basic.max_eq_right vertical]
      ring1
    · rewrite [Fraction.Order.Basic.min_eq_right horizontal, Fraction.Order.Basic.max_eq_left horizontal,
        Fraction.Order.Basic.min_eq_right vertical, Fraction.Order.Basic.max_eq_left vertical]
      ring1

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

end

public section

namespace Purelib.Geometry.Rational.Box.Hull

open Purelib.Data
open Purelib.Data.Rat

/-- The left original box refines its unchanged coordinatewise hull. -/
theorem left_refines (left right : Rational.Box) : left.Refines (hull left right) :=
  ⟨Fraction.Order.Basic.min_le_left _ _, Fraction.Order.Basic.le_max_left _ _,
    Fraction.Order.Basic.min_le_left _ _, Fraction.Order.Basic.le_max_left _ _⟩

/-- The right original box refines its unchanged coordinatewise hull. -/
theorem right_refines (left right : Rational.Box) : right.Refines (hull left right) :=
  ⟨Fraction.Order.Basic.min_le_right _ _, Fraction.Order.Basic.le_max_right _ _,
    Fraction.Order.Basic.min_le_right _ _, Fraction.Order.Basic.le_max_right _ _⟩

/-- A hull containing a proper original left box is proper.

Its lower endpoints lie below the original lower endpoints and its upper
endpoints lie above the original upper endpoints. Both strict widths are
therefore inherited from the same supplied original box.
-/
theorem proper {left right : Rational.Box} (ordered : left.Proper) : (hull left right).Proper :=
  ⟨(Fraction.Order.Basic.min_le_left _ _).trans_lt
      (ordered.1.trans_le (Fraction.Order.Basic.le_max_left _ _)),
    (Fraction.Order.Basic.min_le_left _ _).trans_lt
      (ordered.2.trans_le (Fraction.Order.Basic.le_max_left _ _))⟩

end Purelib.Geometry.Rational.Box.Hull

end
