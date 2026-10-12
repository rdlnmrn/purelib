module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Point.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint
public import Mathlib.Algebra.GroupWithZero.NeZero
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Curves.Plane.Conic

open Purelib.Geometry

section
@[expose] public section

/-!
# Divine Proportions, Chapter 3: points, lines, and incidence

Lines are finite coefficient records, not sets of points and not quotients.
`Line.Equivalent` records the three cross-product equations expressing equality
of the ordered proportions.  This follows the source's finite algebra while
keeping every construction executable over both finite fields and the
constructive rationals.
-/

namespace Purelib.Geometry.Plane

variable {K : Type*}

section

set_option genInjectivity false in
/-- A line is a displayed coefficient triple with a nonzero direction pair. The proof field prevents the invalid triple
`⟨0 : 0 : c⟩`. -/
structure Line (K : Type*) [Zero K] where
  /-- The coefficient of the first point coordinate. -/ a : K
  /-- The coefficient of the second point coordinate. -/ b : K
  /-- The constant coefficient of the affine line equation. -/ c : K
  /-- At least one direction coefficient is nonzero. -/ direction_nonzero : a ≠ 0 ∨ b ≠ 0

constructive_injectivity Line

end

section

end

namespace Line

variable [CommRing K]

/-- Equality of two displayed ordered proportions, expressed without a quotient or a selected scaling coefficient. -/
def Equivalent (left right : Line K) : Prop :=
  left.a * right.b = right.a * left.b ∧
  left.a * right.c = right.a * left.c ∧
  left.b * right.c = right.b * left.c

/-- Every displayed line is equivalent to itself. -/
theorem equivalent_refl (line : Line K) :
  line.Equivalent line := by
  exact ⟨rfl, rfl, rfl⟩

/-- Equivalence of displayed line coefficient triples is symmetric. -/
theorem equivalent_symm {left right : Line K}
    (equivalent : left.Equivalent right) : right.Equivalent left := by
  rcases equivalent with ⟨first, second, third⟩
  exact ⟨first.symm, second.symm, third.symm⟩

/-- A point lies on a line when it satisfies the displayed linear equation. -/
def Contains (line : Line K) (point :
  Point K) : Prop :=
  line.a * point.x + line.b * point.y + line.c = 0

/-- Two lines are parallel when their direction determinant vanishes. -/
def Parallel (left right : Line K) : Prop :=
  left.a * right.b - right.a * left.b = 0

/-- Two lines are perpendicular when their direction dot product vanishes. -/
def Perpendicular (left right : Line K) : Prop
  :=
  left.a * right.a + left.b * right.b = 0

/-- A line is null when its direction quadrance vanishes. -/
def IsNull (line : Line K) : Prop := line.a ^ 2
  + line.b ^ 2 = 0

/-- Every displayed line is parallel to itself. -/
theorem parallel_refl (line : Line K) :
  line.Parallel line := by
  unfold Parallel
  ring1

/-- Parallelism of displayed lines is symmetric. -/
theorem parallel_symm {left right : Line K}
  (parallel : left.Parallel right) :
    right.Parallel left := by
  unfold Parallel at parallel ⊢
  calc
    right.a * left.b - left.a * right.b =
        -(left.a * right.b - right.a * left.b) := by ring1
    _ = 0 := by rw [parallel]; exact neg_zero

/-- Perpendicularity of displayed lines is symmetric. -/
theorem perpendicular_symm {left right : Line K}
    (perpendicular : left.Perpendicular right) : right.Perpendicular left := by
  unfold Perpendicular at perpendicular ⊢
  calc
    right.a * left.a + right.b * left.b =
        left.a * right.a + left.b * right.b := by ring1
    _ = 0 := perpendicular

end Line

end Purelib.Geometry.Plane

end

end

section
@[expose] public section

/-!
# Divine Proportions, Exercise 16.8: rational polar form

A Cartesian point is used as a finite Gaussian pair.  Multiplication and
scaling are explicit coordinate operations; no completed complex carrier is
introduced.  The unit-circle parameter is recovered by the finite quotient
`y / (1+x)`, and the chord through `-1` has the displayed equation
`lambda*x-y+lambda=0`.

The multiplication theorem uses the same `turnComposition` operation as
Exercise 9.2.  Its premise `1-lambda₁*lambda₂ != 0` is essential: when it
vanishes, the product unit point is the excluded point `[-1,0]`, so the finite
chart has no resulting parameter.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section Conic

/-- The displayed imaginary axis `x=0`. -/
def imaginaryAxis [Nontrivial K] : Geometry.Plane.Line K where
  a := 1
  b := 0
  c := 0
  direction_nonzero := Or.inl one_ne_zero

/-- The point `i*lambda` lies on the imaginary axis. -/
theorem imaginaryAxis_contains_parameter [Nontrivial K]
    (parameter : K) :
    Curves.Plane.Conic.imaginaryAxis.Contains (Conic.imaginaryParameterPoint parameter) := by
  unfold imaginaryAxis Conic.imaginaryParameterPoint Geometry.Plane.Line.Contains
  dsimp only
  ring1
end Conic

end Purelib.Curves.Plane.Conic

end

section
@[expose] public section

/-!
# Divine Proportions, §15.5: grammolas

A grammola is retained through its two explicit non-null diagonal lines and
associated quadrance.  Multiplying by the two line norms clears exactly the
two finite divisions and produces an executable conic.  The intersection of
the diagonals is then an explicit center.
-/

namespace Purelib.Geometry.Plane.Line.Basic

section

variable {K : Type*} [ExplicitField K]

/-- The linear expression represented by a displayed line at a point. -/
def lineValue (line : Line K) (point :
  Point K) : K :=
  line.a * point.x + line.b * point.y + line.c
end

end Purelib.Geometry.Plane.Line.Basic

end

section
@[expose] public section

/-!
# Divine Proportions, Exercise 15.18

The two axes of a grammola are constructed from an explicit square witness
for the product of its diagonal norms.  Reflection in either normalized
vertex bisector swaps the two weighted squared line values, so it preserves
the grammola equation.  Conversely, two finite reflection probes show that
every axis satisfies the equal-spread bisector equation.
-/

namespace Purelib.Geometry.Plane.Line.Basic

variable {K : Type*} [ExplicitField K]

/-- The dot product of the two displayed line direction coefficient pairs. -/
public def lineDot (first second :
  Line K) : K :=
  first.a * second.a + first.b * second.b

end Purelib.Geometry.Plane.Line.Basic

end

section
@[expose] public section

/-!
# Divine Proportions, Exercises 15.8 and 15.9

This module constructs a parabola's axis from its focus and directrix, proves
that equation preservation characterizes that axis up to the project's
quotient-free line equivalence, and constructs the unique vertex as the
midpoint of the focus and its altitude foot on the directrix.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section Conic

/-- Evaluation of a displayed line's affine polynomial. -/
def lineValue (line : Geometry.Plane.Line K) (point :
  Geometry.Plane.Point K) : K :=
  line.a * point.x + line.b * point.y + line.c
end Conic

end Purelib.Curves.Plane.Conic

end

section
@[expose] public section

/-!
# Divine Proportions, §3.4: the foot of an altitude

The construction is the exact rational formula printed in Theorem 8.  Its only
denominator is the direction quadrance `a² + b²`, so the source's non-null-line
hypothesis is exposed as the precise executable cancellation certificate.
-/

namespace Purelib.Geometry.Plane.Line.Basic

variable {K : Type*} [ExplicitField K]

/-- Direction quadrance of a displayed line. -/
def lineNorm (line : Line K) : K := line.a ^ 2 +
  line.b ^ 2

/-- A displayed line is null exactly when its direction norm is zero. -/
theorem line_isNull_iff_norm_eq_zero (line : Line K)
  :
    line.IsNull ↔ lineNorm line = 0 := Iff.rfl

/-- A non-null line has nonzero direction norm. -/
public theorem lineNorm_ne_zero {line :
  Line K} (nonNull : ¬ line.IsNull) :
    lineNorm line ≠ 0 := nonNull

end Purelib.Geometry.Plane.Line.Basic

end

end

section
@[expose] public section

/-!
# Divine Proportions, Theorem 96: regular stars of order five

The five cyclic reflection equations and all ten nonparallel pairs are stored
as finite data.  The executable reflection iterator is then related to these
displayed representatives using quotient-free line congruence.
-/

namespace Purelib.Geometry.Plane.Line.Basic

variable {K : Type*} [ExplicitField K]

section

/-- The horizontal coordinate axis, displayed by the equation y = 0. -/
def xAxis [Nontrivial K] : Line K where
  a := 0
  b := 1
  c := 0
  direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0)

end

end Purelib.Geometry.Plane.Line.Basic

end

section
@[expose] public section

/-!
# Divine Proportions, §6.9: vertex bisectors

An explicit witness `r² = ‖l₁‖‖l₂‖` produces the two normalized
bisectors `r l₁ ± ‖l₁‖ l₂`.  This formulation is equivalent to the
book's longer coefficient display, but is symmetric enough that all finite
field cancellations remain visible.
-/

namespace Purelib.Geometry.Plane.Line.Basic

variable {K : Type*} [ExplicitField K]

/-- Nonparallel displayed lines have a nonzero direction determinant. -/
public theorem
  determinant_ne_zero_of_not_parallel
    {first second : Line K} (notParallel : ¬ first.Parallel second) :
    first.a * second.b - second.a * first.b ≠ 0 := notParallel

end Purelib.Geometry.Plane.Line.Basic

end
