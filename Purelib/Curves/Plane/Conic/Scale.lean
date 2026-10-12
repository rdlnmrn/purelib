module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Plane.Point.Basic
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

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

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Multiply every displayed conic coefficient by one explicit nonzero scale. -/
def scaleConic (scale : K) (scaleNonzero : scale ≠ 0)
    (conic : Conic K) : Conic K where
  d := scale * conic.d
  e := scale * conic.e
  f := scale * conic.f
  a := scale * conic.a
  b := scale * conic.b
  c := scale * conic.c
  quadratic_nonzero := by
    rcases conic.quadratic_nonzero with dNonzero | eNonzero | fNonzero
    · exact Or.inl (Algebra.Field.ExplicitField.mul_ne_zero scaleNonzero dNonzero)
    · exact Or.inr (Or.inl
        (Algebra.Field.ExplicitField.mul_ne_zero scaleNonzero eNonzero))
    · exact Or.inr (Or.inr
        (Algebra.Field.ExplicitField.mul_ne_zero scaleNonzero fNonzero))

/-- Scaling coefficients scales the evaluated polynomial by the same factor. -/
theorem scaleConic_evaluate (scale : K) (scaleNonzero : scale ≠ 0)
    (conic : Conic K) (point : Plane.Point K) :
    (scaleConic scale scaleNonzero conic).evaluate point =
      scale * conic.evaluate point := by
  unfold Conic.scaleConic Conic.evaluate
  ring1

end Purelib.Curves.Plane.Conic

end

section
@[expose] public section

/-!
# Divine Proportions, §15.4 and Exercise 19.3: quadrolas

A quadrola is given by one finite Archimedes polynomial in the two focal
quadrances and its associated quadrance.  The apparent quartic terms cancel
to an explicit conic.  Its gradient tangent satisfies the equal-spread
reflection property by a denominator-cleared polynomial identity.
-/

namespace Purelib.Curves.Plane.Conic.Scale

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- An explicit quotient-free witness that two displayed conic coefficient records represent the same six-proportion. -/
structure CoefficientScale (source target : Conic K) (scale : K) :
  Prop where
  /-- The source x-squared coefficient equals the specified scale times its target coefficient. -/ d : source.d = scale
    * target.d
  /-- The source mixed coefficient equals the specified scale times its target coefficient. -/ e : source.e = scale *
    target.e
  /-- The source y-squared coefficient equals the specified scale times its target coefficient. -/ f : source.f = scale
    * target.f
  /-- The source x coefficient equals the specified scale times its target coefficient. -/ a : source.a = scale *
    target.a
  /-- The source y coefficient equals the specified scale times its target coefficient. -/ b : source.b = scale *
    target.b
  /-- The source constant coefficient equals the specified scale times its target coefficient. -/ c : source.c = scale *
    target.c

/-- A retained coefficient-scale witness scales conic evaluation by that same factor. -/
theorem CoefficientScale.evaluate
    {source target : Conic K} {scale : K}
    (scaled : CoefficientScale source target scale) (point : Plane.Point K) :
    source.evaluate point = scale * target.evaluate point := by
  unfold Conic.evaluate
  rw [scaled.d, scaled.e, scaled.f, scaled.a, scaled.b, scaled.c]
  ring1

end Purelib.Curves.Plane.Conic.Scale

end
