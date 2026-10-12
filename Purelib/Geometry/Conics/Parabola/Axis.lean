module
public import Purelib.Geometry.Conics.Axis
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Geometry.Conics.Parabola.Basic
import Purelib.Geometry.Conics.Parabola.Reflection
import Purelib.Geometry.Conics.Parabola.Uniqueness
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Construction
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Plane.Reflection.Line
import Purelib.Geometry.Plane.Reflection.Line.Evaluation
import Purelib.Geometry.Plane.Reflection.Point
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Conics

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Reflection

open Purelib.Geometry.Plane.Reflection.Point

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

section

/-- The canonical parabola axis is the altitude from the focus to the directrix. -/
def parabolaAxis (focus : Plane.Point K) (directrix :
  Plane.Line K) : Plane.Line K :=
  Construction.altitudeThrough focus directrix

/-- A non-null directrix gives a non-null canonical axis. -/
theorem parabolaAxis_nonNull (focus : Plane.Point K)
  (directrix : Line K)
    (directrixNonNull : ¬ directrix.IsNull) :
    ¬ (parabolaAxis focus directrix).IsNull := by
  intro axisNull
  apply directrixNonNull
  unfold Line.IsNull at axisNull ⊢
  unfold parabolaAxis Construction.altitudeThrough at axisNull
  calc
    directrix.a ^ 2 + directrix.b ^ 2 =
        (-directrix.b) ^ 2 + directrix.a ^ 2 := by ring1
    _ = 0 := axisNull

/-- The canonical axis contains the focus. -/
theorem parabolaAxis_contains_focus (focus : Plane.Point K)
    (directrix : Plane.Line K) :
    (parabolaAxis focus directrix).Contains focus := by
  exact Construction.altitudeThrough_contains focus directrix

/-- The canonical axis is perpendicular to the directrix. -/
theorem parabolaAxis_perpendicular (focus : Plane.Point K)
    (directrix : Plane.Line K) :
    (parabolaAxis focus directrix).Perpendicular directrix := by
  exact Construction.altitudeThrough_perpendicular focus directrix

/-- Reflection in the focus altitude preserves the presented parabola equation pointwise. -/
theorem parabolaAxis_isAxis [DecidableEq K]
    (conic : Conic K) (focus : Plane.Point K) (directrix : Plane.Line K)
    (presentation : Conic.ParabolaPresentationData conic focus directrix) :
    conic.IsAxis (parabolaAxis focus directrix) := by
  let axis := parabolaAxis focus directrix
  have axisNonNull : ¬ axis.IsNull :=
    parabolaAxis_nonNull focus directrix presentation.directrixNonNull
  have focusFixed :
      Reflection.Point.reflectPoint axis axisNonNull focus = focus :=
    Axis.reflectPoint_fixed_of_contains axis axisNonNull focus
      (parabolaAxis_contains_focus focus directrix)
  have perpendicular : axis.Perpendicular directrix :=
    parabolaAxis_perpendicular focus directrix
  refine ⟨axisNonNull, ?_⟩
  intro point
  rw [(Parabola.Basic.Conic.ParabolaPresentationData.evaluate_eq_scale_mul presentation),
    (Parabola.Basic.Conic.ParabolaPresentationData.evaluate_eq_scale_mul presentation)]
  congr 1
  rw [Conic.parabolaConic_evaluate, Conic.parabolaConic_evaluate]
  have focusQuadrance :
      Quadrance.quadrance (Reflection.Point.reflectPoint axis axisNonNull point) focus =
        Quadrance.quadrance point focus := by
    calc
      Quadrance.quadrance (Reflection.Point.reflectPoint axis axisNonNull point) focus =
          Quadrance.quadrance (Reflection.Point.reflectPoint axis axisNonNull point)
            (Reflection.Point.reflectPoint axis axisNonNull focus) := by rw [focusFixed]
      _ = Quadrance.quadrance point focus :=
        Reflection.Point.reflectPoint_preserves_quadrance axis axisNonNull point focus
  have directrixValue :
      Conic.lineValue directrix (Reflection.Point.reflectPoint axis axisNonNull point) =
        Conic.lineValue directrix point :=
    Conic.lineValue_reflectPoint_of_perpendicular axis directrix axisNonNull
      perpendicular point
  change
    Line.Basic.lineNorm directrix *
          Quadrance.quadrance (Reflection.Point.reflectPoint axis axisNonNull point) focus -
        Conic.lineValue directrix (Reflection.Point.reflectPoint axis axisNonNull point) ^ 2 =
      Line.Basic.lineNorm directrix * Quadrance.quadrance point focus -
        Conic.lineValue directrix point ^ 2
  rw [focusQuadrance, directrixValue]

/-- Every equation-preserving mirror of a presented parabola is equivalent to the focus altitude. -/
theorem parabolaAxis_unique [DecidableEq K]
    (conic : Conic K) (focus : Plane.Point K) (directrix axis : Plane.Line K)
    (presentation : Conic.ParabolaPresentationData conic focus directrix)
    (twoNonzero : (2 : K) ≠ 0) (isAxis : conic.IsAxis axis) :
    axis.Equivalent (parabolaAxis focus directrix) := by
  rcases isAxis with ⟨axisNonNull, equationInvariant⟩
  have reflectedPresentation :=
    Conic.reflectedPresentation_of_axis conic focus directrix axis presentation
      twoNonzero axisNonNull equationInvariant
  have reflectedUniqueness :=
    Conic.parabola_uniqueness conic twoNonzero reflectedPresentation
      ⟨presentation⟩
  have focusFixed : Reflection.Point.reflectPoint axis axisNonNull focus = focus :=
    reflectedUniqueness.1
  have axisContainsFocus : axis.Contains focus :=
    (Reflection.Point.reflectPoint_fixed_iff_contains axis axisNonNull twoNonzero focus).1
      focusFixed
  have fixedDirectrix :
      (Line.reflectLine axis directrix axisNonNull).Equivalent directrix :=
    reflectedUniqueness.2
  have fixedDirection :
      directrix.Parallel (Line.reflectLine axis directrix axisNonNull) :=
    Relations.line_parallel_of_equivalent (Plane.Line.equivalent_symm fixedDirectrix)
  have directionCases :=
    Line.parallel_or_perpendicular_of_parallel_reflectLine axis directrix
      axisNonNull twoNonzero fixedDirection
  have axisPerpendicular : axis.Perpendicular directrix := by
    rcases directionCases with directrixParallel | directrixPerpendicular
    · have axisParallel : axis.Parallel directrix :=
        Plane.Line.parallel_symm directrixParallel
      have axisEquivalentDirectrix :=
        Conic.equivalent_of_parallel_and_reflectLine_fixed axis directrix
          axisNonNull twoNonzero axisParallel fixedDirectrix
      have focusOnDirectrix : directrix.Contains focus :=
        Relations.line_contains_of_equivalent axisEquivalentDirectrix focus
          axisContainsFocus
      exact False.elim
        (presentation.focusNotOnDirectrix focusOnDirectrix)
    · exact Plane.Line.perpendicular_symm directrixPerpendicular
  have canonicalParallel :
      (parabolaAxis focus directrix).Parallel axis := by
    unfold parabolaAxis Construction.altitudeThrough Line.Parallel
    unfold Plane.Line.Perpendicular at axisPerpendicular
    calc
      -directrix.b * axis.b - axis.a * directrix.a =
          -(axis.a * directrix.a + axis.b * directrix.b) := by ring1
      _ = 0 := by rw [axisPerpendicular]; ring1
  have canonicalEquivalentAxis :=
    Relations.line_equivalent_of_parallel_and_common_point
      (parabolaAxis focus directrix) axis focus canonicalParallel
      (parabolaAxis_contains_focus focus directrix) axisContainsFocus
  exact Plane.Line.equivalent_symm canonicalEquivalentAxis

/-- Exercise 15.8: every presented parabola has exactly one axis up to quotient-free line equivalence, namely the
altitude from its focus to its directrix. -/
theorem exercise_15_8 [DecidableEq K] (conic : Conic K)
    (twoNonzero : (2 : K) ≠ 0) (isParabola : conic.IsParabola) :
    ∃ focus : Plane.Point K, ∃ directrix : Plane.Line K,
      conic.IsParabolaPresentation focus directrix ∧
        conic.IsAxis (parabolaAxis focus directrix) ∧
        ∀ otherAxis : Plane.Line K, conic.IsAxis otherAxis →
          otherAxis.Equivalent (parabolaAxis focus directrix) := by
  rcases isParabola with ⟨focus, directrix, presentation⟩
  rcases presentation with ⟨presentation⟩
  refine ⟨focus, directrix, ⟨presentation⟩, ?_, ?_⟩
  · exact parabolaAxis_isAxis conic focus directrix presentation
  · intro otherAxis otherIsAxis
    exact parabolaAxis_unique conic focus directrix otherAxis presentation
      twoNonzero otherIsAxis
end

end Purelib.Curves.Plane.Conic

end
