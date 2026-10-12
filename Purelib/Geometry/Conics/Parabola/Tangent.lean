module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Geometry.Conics.Parabola.Basic
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Algebra.Field (ExplicitField)

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Point

section
public section

/-!
# Divine Proportions, Chapter 19: tangent lines and conics

Translations, Taylor conics, and tangent lines are retained as explicit
finite coefficient records.  A non-singular point carries the disjunction
that one of the two displayed linear coefficients is nonzero, so every line
construction remains executable and choice-free.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- Evaluation through an arbitrary scaled focus/directrix presentation. -/
theorem evaluate_eq_scale_mul_parabola_residual
    (conic : Conic K) (focus point : Plane.Point K) (directrix : Plane.Line K)
    (presentation :
      Conic.ParabolaPresentationData conic focus directrix) :
    conic.evaluate point = presentation.scale *
      (Line.Basic.lineNorm directrix * Quadrance.quadrance point focus -
        (directrix.a * point.x + directrix.b * point.y +
          directrix.c) ^ 2) := by
  unfold Conic.evaluate Line.Basic.lineNorm Quadrance.quadrance
  rw [presentation.dEquation, presentation.eEquation,
    presentation.fEquation, presentation.aEquation,
    presentation.bEquation, presentation.cEquation]
  unfold Line.Basic.lineNorm
  ring1

/-- Incidence with a presented parabola is the denominator-cleared equality between focus quadrance and squared
directrix evaluation. -/
theorem parabola_incidence_residual
    (conic : Conic K) (focus point : Plane.Point K) (directrix : Plane.Line K)
    (presentation :
      Conic.ParabolaPresentationData conic focus directrix)
    (onParabola : conic.Contains point) :
    Line.Basic.lineNorm directrix * Quadrance.quadrance point focus =
      (directrix.a * point.x + directrix.b * point.y +
        directrix.c) ^ 2 := by
  have scaledResidualZero : presentation.scale *
      (Line.Basic.lineNorm directrix * Quadrance.quadrance point focus -
        (directrix.a * point.x + directrix.b * point.y +
          directrix.c) ^ 2) = 0 := by
    calc
      presentation.scale *
          (Line.Basic.lineNorm directrix * Quadrance.quadrance point focus -
            (directrix.a * point.x + directrix.b * point.y +
              directrix.c) ^ 2) = conic.evaluate point :=
        (evaluate_eq_scale_mul_parabola_residual conic focus point
          directrix presentation).symm
      _ = 0 := onParabola
  have residualZero := ExplicitField.eq_zero_of_mul_eq_zero_left
    presentation.scaleNonzero scaledResidualZero
  exact Group.eq_of_sub_eq_zero residualZero

/-- A point of a valid focus/directrix parabola cannot be its focus. -/
theorem parabola_point_ne_focus
    [DecidableEq K]
    (conic : Conic K) (focus point : Plane.Point K) (directrix : Plane.Line K)
    (presentation : conic.IsParabolaPresentation focus directrix)
    (onParabola : conic.Contains point) : point ≠ focus := by
  rcases presentation with ⟨presentation⟩
  intro pointEqualsFocus
  have residual := parabola_incidence_residual conic focus point directrix
    presentation onParabola
  have focusEvaluationSquaredZero :
      (directrix.a * focus.x + directrix.b * focus.y +
        directrix.c) ^ 2 = 0 := by
    rw [pointEqualsFocus] at residual
    calc
      (directrix.a * focus.x + directrix.b * focus.y +
          directrix.c) ^ 2 =
        Line.Basic.lineNorm directrix * Quadrance.quadrance focus focus := residual.symm
      _ = 0 := by rw [Quadrance.quadrance_self]; ring1
  have focusEvaluationZero :
      directrix.a * focus.x + directrix.b * focus.y +
        directrix.c = 0 := by
    by_cases evaluationZero :
        directrix.a * focus.x + directrix.b * focus.y +
          directrix.c = 0
    · exact evaluationZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero evaluationZero evaluationZero)
          (by simpa only [pow_two] using focusEvaluationSquaredZero))
  apply presentation.focusNotOnDirectrix
  exact focusEvaluationZero

/-- The gradient of a presented parabola is nonzero at every point.

When two is nonzero, the non-null directrix and its separation from the focus prevent simultaneous vanishing of the
gradient coordinates; point incidence is not required. -/
theorem parabola_nonSingularAt
    [DecidableEq K]
    (conic : Conic K) (focus point : Plane.Point K) (directrix : Plane.Line K)
    (twoNonzero : (2 : K) ≠ 0)
    (presentation : conic.IsParabolaPresentation focus directrix) :
    conic.IsNonSingularAt point := by
  rcases presentation with ⟨presentation⟩
  let gradientX :=
    conic.a + 2 * conic.d * point.x + conic.e * point.y
  let gradientY :=
    conic.b + conic.e * point.x + 2 * conic.f * point.y
  let focusEvaluation :=
    directrix.a * focus.x + directrix.b * focus.y + directrix.c
  have normNonzero : Line.Basic.lineNorm directrix ≠ 0 :=
    presentation.directrixNonNull
  have focusEvaluationNonzero : focusEvaluation ≠ 0 := by
    intro evaluationZero
    apply presentation.focusNotOnDirectrix
    exact evaluationZero
  have combinedGradient :
      directrix.a * gradientX + directrix.b * gradientY =
        -(presentation.scale * 2 * Line.Basic.lineNorm directrix *
          focusEvaluation) := by
    unfold gradientX gradientY focusEvaluation Line.Basic.lineNorm
    rw [presentation.dEquation, presentation.eEquation,
      presentation.fEquation, presentation.aEquation,
      presentation.bEquation]
    unfold Line.Basic.lineNorm
    ring1
  have combinedGradientNonzero :
      directrix.a * gradientX + directrix.b * gradientY ≠ 0 := by
    rw [combinedGradient]
    intro negativeProductZero
    have productZero :
        presentation.scale * 2 * Line.Basic.lineNorm directrix *
          focusEvaluation = 0 := by
      calc
        presentation.scale * 2 * Line.Basic.lineNorm directrix * focusEvaluation =
            -(-(presentation.scale * 2 * Line.Basic.lineNorm directrix *
              focusEvaluation)) := by ring1
        _ = 0 := by rw [negativeProductZero]; ring1
    exact (ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero
        (ExplicitField.mul_ne_zero presentation.scaleNonzero
          twoNonzero) normNonzero) focusEvaluationNonzero) productZero
  unfold Conic.IsNonSingularAt
  change gradientX ≠ 0 ∨ gradientY ≠ 0
  by_cases firstNonzero : gradientX ≠ 0
  · exact Or.inl firstNonzero
  · right
    intro secondZero
    have firstZero : gradientX = 0 := by
      by_cases zero : gradientX = 0
      · exact zero
      · exact False.elim (firstNonzero zero)
    apply combinedGradientNonzero
    rw [firstZero, secondZero]
    ring1
end

end Purelib.Curves.Plane.Conic

end

end
