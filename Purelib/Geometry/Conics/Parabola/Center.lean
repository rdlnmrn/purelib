module
public import Purelib.Curves.Plane.Conic.Center
public import Purelib.Geometry.Conics.Parabola.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane

section
@[expose] public section

/-!
# Divine Proportions, §15.3: parabolas

The six coefficient equations below are the denominator-cleared expansion of
`Q(X,F) = Q(X,l)`.  An explicit nonzero scale retains the source's proportional
conic notation without a quotient or a selected representative.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- Exercise 15.7: a parabola has no center. The two putative center equations combine to say that the focus lies on the
directrix. -/
theorem parabola_has_no_center (conic : Conic K)
    (focus : Plane.Point K) (directrix : Plane.Line K)
    (twoNonzero : (2 : K) ≠ 0)
    (presentation : conic.IsParabolaPresentation focus directrix) :
    ¬ ∃ center : Plane.Point K, conic.IsCenter center := by
  rcases presentation with ⟨presentation⟩
  rintro ⟨center, firstCenterEquation, secondCenterEquation⟩
  have scaleTwoNonzero : presentation.scale * 2 ≠ 0 :=
    ExplicitField.mul_ne_zero presentation.scaleNonzero twoNonzero
  have firstInnerZero :
      directrix.b ^ 2 * center.x -
          directrix.a * directrix.b * center.y -
          directrix.a * directrix.c -
          Line.Basic.lineNorm directrix * focus.x = 0 := by
    apply ExplicitField.eq_zero_of_mul_eq_zero_left scaleTwoNonzero
    calc
      presentation.scale * 2 *
          (directrix.b ^ 2 * center.x -
            directrix.a * directrix.b * center.y -
            directrix.a * directrix.c -
            Line.Basic.lineNorm directrix * focus.x) =
        2 * conic.d * center.x + conic.e * center.y + conic.a := by
          rw [presentation.dEquation, presentation.eEquation,
            presentation.aEquation]
          ring1
      _ = 0 := firstCenterEquation
  have secondInnerZero :
      -directrix.a * directrix.b * center.x +
          directrix.a ^ 2 * center.y -
          directrix.b * directrix.c -
          Line.Basic.lineNorm directrix * focus.y = 0 := by
    apply ExplicitField.eq_zero_of_mul_eq_zero_left scaleTwoNonzero
    calc
      presentation.scale * 2 *
          (-directrix.a * directrix.b * center.x +
            directrix.a ^ 2 * center.y -
            directrix.b * directrix.c -
            Line.Basic.lineNorm directrix * focus.y) =
        conic.e * center.x + 2 * conic.f * center.y + conic.b := by
          rw [presentation.eEquation, presentation.fEquation,
            presentation.bEquation]
          ring1
      _ = 0 := secondCenterEquation
  have incidenceScaledZero :
      Line.Basic.lineNorm directrix *
        (directrix.a * focus.x + directrix.b * focus.y + directrix.c) = 0 := by
    calc
      Line.Basic.lineNorm directrix *
          (directrix.a * focus.x + directrix.b * focus.y + directrix.c) =
        -(directrix.a *
            (directrix.b ^ 2 * center.x -
              directrix.a * directrix.b * center.y -
              directrix.a * directrix.c -
              Line.Basic.lineNorm directrix * focus.x) +
          directrix.b *
            (-directrix.a * directrix.b * center.x +
              directrix.a ^ 2 * center.y -
              directrix.b * directrix.c -
              Line.Basic.lineNorm directrix * focus.y)) := by
                unfold Line.Basic.lineNorm
                ring1
      _ = 0 := by rw [firstInnerZero, secondInnerZero]; ring1
  have focusOnDirectrix : directrix.Contains focus := by
    exact ExplicitField.eq_zero_of_mul_eq_zero_left presentation.directrixNonNull
      incidenceScaledZero
  exact presentation.focusNotOnDirectrix focusOnDirectrix

/-- A presented parabola has no center when two is nonzero.

The conclusion rules out every point satisfying the conic center equations, independently of the chosen focus and
directrix presentation (Exercise 15.7). -/
theorem exercise_15_7 (conic : Conic K) (twoNonzero : (2 : K)
  ≠ 0)
    (isParabola : conic.IsParabola) :
    ¬ ∃ center : Plane.Point K, conic.IsCenter center := by
  rcases isParabola with ⟨focus, directrix, presentation⟩
  exact parabola_has_no_center conic focus directrix twoNonzero presentation
end

end Purelib.Curves.Plane.Conic

end
