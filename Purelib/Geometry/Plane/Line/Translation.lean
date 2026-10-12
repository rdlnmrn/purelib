module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Point

section
@[expose] public section

/-!
# Divine Proportions, Chapter 19: tangent lines and conics

Translations, Taylor conics, and tangent lines are retained as explicit
finite coefficient records.  A non-singular point carries the disjunction
that one of the two displayed linear coefficients is nonzero, so every line
construction remains executable and choice-free.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

/-- Translation of a displayed line by `B`: its equation is obtained by replacing `x,y` by `x-u,y-v`. -/
def translateLine (line : Plane.Line K) (offset :
  Plane.Point K) : Plane.Line K where
  a := line.a
  b := line.b
  c := line.c - line.a * offset.x - line.b * offset.y
  direction_nonzero := line.direction_nonzero

/-- Point incidence is transported by the displayed line translation. -/
theorem translateLine_contains_translationPoint
    (line : Plane.Line K) (offset point : Plane.Point K) :
    (translateLine line offset).Contains
        (Affine.translationPoint offset.x offset.y point) ↔
      line.Contains point := by
  unfold translateLine Plane.Line.Contains Affine.translationPoint
  constructor <;> intro equation
  · calc
      line.a * point.x + line.b * point.y + line.c =
          line.a * (point.x + offset.x) +
            line.b * (point.y + offset.y) +
            (line.c - line.a * offset.x - line.b * offset.y) := by ring1
      _ = 0 := equation
  · calc
      line.a * (point.x + offset.x) +
          line.b * (point.y + offset.y) +
          (line.c - line.a * offset.x - line.b * offset.y) =
        line.a * point.x + line.b * point.y + line.c := by ring1
      _ = 0 := equation
end

end Purelib.Curves.Plane.Conic

end
