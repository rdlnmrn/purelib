module
import Purelib.Curves.Plane.Conic.Extensionality
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Curves.Plane.Conic.Scale
public import Purelib.Curves.Plane.Conic.Tangent
import Purelib.Geometry.Conics.Parabola.Basic
public import Purelib.Geometry.Conics.Parabola.Tangent
import Purelib.Geometry.Plane.Line.Altitude
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Construction
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Plane.Reflection.Line
import Purelib.Geometry.Plane.Reflection.Line.Evaluation
import Purelib.Geometry.Plane.Reflection.Point
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra.Field

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Reflection

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

section

/-- Simultaneously reflecting the focus and directrix multiplies the canonical parabola polynomial by the square of the
mirror norm. -/
theorem parabolaConic_reflected_evaluate [DecidableEq K]
    (focus point : Plane.Point K) (directrix mirror : Plane.Line K)
    (mirrorNonNull : ¬ mirror.IsNull) :
    (Conic.parabolaConic (Reflection.Point.reflectPoint mirror mirrorNonNull focus)
        (Line.reflectLine mirror directrix mirrorNonNull)).evaluate point =
      Line.Basic.lineNorm mirror ^ 2 *
        (Conic.parabolaConic focus directrix).evaluate
          (Reflection.Point.reflectPoint mirror mirrorNonNull point) := by
  have quadranceReflected :
      Quadrance.quadrance point (Reflection.Point.reflectPoint mirror mirrorNonNull focus) =
        Quadrance.quadrance (Reflection.Point.reflectPoint mirror mirrorNonNull point) focus := by
    calc
      Quadrance.quadrance point (Reflection.Point.reflectPoint mirror mirrorNonNull focus) =
          Quadrance.quadrance (Reflection.Point.reflectPoint mirror mirrorNonNull point)
            (Reflection.Point.reflectPoint mirror mirrorNonNull
              (Reflection.Point.reflectPoint mirror mirrorNonNull focus)) :=
        (Reflection.Point.reflectPoint_preserves_quadrance mirror mirrorNonNull point
          (Reflection.Point.reflectPoint mirror mirrorNonNull focus)).symm
      _ = Quadrance.quadrance (Reflection.Point.reflectPoint mirror mirrorNonNull point) focus := by
        rw [Reflection.Point.reflectPoint_involutive]
  have reflectedValue :
      Conic.lineValue (Line.reflectLine mirror directrix mirrorNonNull) point =
        -Line.Basic.lineNorm mirror *
          Conic.lineValue directrix (Reflection.Point.reflectPoint mirror mirrorNonNull point) := by
    calc
      Conic.lineValue (Line.reflectLine mirror directrix mirrorNonNull) point =
          Conic.lineValue (Line.reflectLine mirror directrix mirrorNonNull)
            (Reflection.Point.reflectPoint mirror mirrorNonNull
              (Reflection.Point.reflectPoint mirror mirrorNonNull point)) := by
                rw [Reflection.Point.reflectPoint_involutive]
      _ = -Line.Basic.lineNorm mirror *
          Conic.lineValue directrix (Reflection.Point.reflectPoint mirror mirrorNonNull point) :=
        Conic.reflectLine_lineValue_reflectPoint mirror directrix mirrorNonNull
          (Reflection.Point.reflectPoint mirror mirrorNonNull point)
  rw [Conic.parabolaConic_evaluate, Conic.parabolaConic_evaluate,
    Line.reflectLine_norm, quadranceReflected]
  change
    Line.Basic.lineNorm mirror ^ 2 * Line.Basic.lineNorm directrix *
          Quadrance.quadrance (Reflection.Point.reflectPoint mirror mirrorNonNull point) focus -
        Conic.lineValue (Line.reflectLine mirror directrix mirrorNonNull) point ^ 2 =
      Line.Basic.lineNorm mirror ^ 2 *
        (Line.Basic.lineNorm directrix *
            Quadrance.quadrance (Reflection.Point.reflectPoint mirror mirrorNonNull point) focus -
          Conic.lineValue directrix
            (Reflection.Point.reflectPoint mirror mirrorNonNull point) ^ 2)
  rw [reflectedValue]
  ring1

/-- An equation-preserving reflection turns a displayed focus/directrix pair into another valid presentation of the same
conic. The new coefficient scale is the old scale divided by the square of the mirror norm. -/
theorem reflectedPresentation_of_axis [DecidableEq K]
    (conic : Conic K) (focus : Plane.Point K) (directrix axis : Line K)
    (presentation : Conic.ParabolaPresentationData conic focus directrix)
    (twoNonzero : (2 : K) ≠ 0) (axisNonNull : ¬ axis.IsNull)
    (equationInvariant : ∀ point : Plane.Point K,
      conic.evaluate (Reflection.Point.reflectPoint axis axisNonNull point) =
        conic.evaluate point) :
    conic.IsParabolaPresentation
      (Reflection.Point.reflectPoint axis axisNonNull focus)
      (Line.reflectLine axis directrix axisNonNull) := by
  let reflectedFocus := Reflection.Point.reflectPoint axis axisNonNull focus
  let reflectedDirectrix := Line.reflectLine axis directrix axisNonNull
  have normNonzero : Line.Basic.lineNorm axis ≠ 0 := axisNonNull
  have normSquareNonzero : Line.Basic.lineNorm axis ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      ExplicitField.mul_ne_zero normNonzero normNonzero
  let reflectedScale := presentation.scale / Line.Basic.lineNorm axis ^ 2
  have reflectedScaleNonzero : reflectedScale ≠ 0 := by
    exact ExplicitField.div_ne_zero presentation.scaleNonzero
      normSquareNonzero
  have canonicalInvariant (point : Plane.Point K) :
      (Conic.parabolaConic focus directrix).evaluate
          (Reflection.Point.reflectPoint axis axisNonNull point) =
        (Conic.parabolaConic focus directrix).evaluate point := by
    apply ExplicitField.eq_of_mul_eq_mul_left presentation.scaleNonzero
    calc
      presentation.scale *
          (Conic.parabolaConic focus directrix).evaluate
            (Reflection.Point.reflectPoint axis axisNonNull point) =
        conic.evaluate (Reflection.Point.reflectPoint axis axisNonNull point) :=
          ((Conics.Parabola.Basic.Conic.ParabolaPresentationData.evaluate_eq_scale_mul presentation)
            (Reflection.Point.reflectPoint axis axisNonNull point)).symm
      _ = conic.evaluate point := equationInvariant point
      _ = presentation.scale *
          (Conic.parabolaConic focus directrix).evaluate point :=
        (Conics.Parabola.Basic.Conic.ParabolaPresentationData.evaluate_eq_scale_mul presentation) point
  have reflectedDirectrixNonNull : ¬ reflectedDirectrix.IsNull := by
    exact Line.reflectLine_nonNull axis directrix axisNonNull
      presentation.directrixNonNull
  have reflectedFocusNotOnDirectrix :
      ¬ reflectedDirectrix.Contains reflectedFocus := by
    intro reflectedContains
    have scaledOriginalZero :
        -Line.Basic.lineNorm axis * Conic.lineValue directrix focus = 0 := by
      calc
        -Line.Basic.lineNorm axis * Conic.lineValue directrix focus =
            Conic.lineValue reflectedDirectrix reflectedFocus := by
              exact (Conic.reflectLine_lineValue_reflectPoint axis directrix
                axisNonNull focus).symm
        _ = 0 := reflectedContains
    have negativeNormNonzero : -Line.Basic.lineNorm axis ≠ 0 := by
      intro negativeNormZero
      apply normNonzero
      calc
        Line.Basic.lineNorm axis = -(-Line.Basic.lineNorm axis) := by ring1
        _ = 0 := by rw [negativeNormZero]; ring1
    have originalZero : Conic.lineValue directrix focus = 0 :=
      ExplicitField.eq_zero_of_mul_eq_zero_left negativeNormNonzero scaledOriginalZero
    apply presentation.focusNotOnDirectrix
    exact originalZero
  let scaledReflectedConic :=
    Conic.scaleConic reflectedScale reflectedScaleNonzero
      (Conic.parabolaConic reflectedFocus reflectedDirectrix)
  have scaleCancel :
      reflectedScale * Line.Basic.lineNorm axis ^ 2 = presentation.scale := by
    unfold reflectedScale
    exact ExplicitField.div_mul_cancel presentation.scale
      normSquareNonzero
  have evaluationsEqual (point : Plane.Point K) :
      conic.evaluate point = scaledReflectedConic.evaluate point := by
    calc
      conic.evaluate point = presentation.scale *
          (Conic.parabolaConic focus directrix).evaluate point :=
        (Conics.Parabola.Basic.Conic.ParabolaPresentationData.evaluate_eq_scale_mul presentation) point
      _ = presentation.scale *
          (Conic.parabolaConic focus directrix).evaluate
            (Reflection.Point.reflectPoint axis axisNonNull point) := by
              rw [canonicalInvariant]
      _ = reflectedScale *
          (Line.Basic.lineNorm axis ^ 2 *
            (Conic.parabolaConic focus directrix).evaluate
              (Reflection.Point.reflectPoint axis axisNonNull point)) := by
                rw [← scaleCancel]
                ring1
      _ = reflectedScale *
          (Conic.parabolaConic reflectedFocus reflectedDirectrix).evaluate point := by
            unfold reflectedFocus reflectedDirectrix
            rw [parabolaConic_reflected_evaluate]
      _ = scaledReflectedConic.evaluate point := by
        exact (Conic.scaleConic_evaluate reflectedScale reflectedScaleNonzero
          (Conic.parabolaConic reflectedFocus reflectedDirectrix) point).symm
  rcases Conic.coefficients_eq_of_evaluate_eq conic scaledReflectedConic
      twoNonzero evaluationsEqual with
    ⟨dEqual, eEqual, fEqual, aEqual, bEqual, cEqual⟩
  refine ⟨
    { directrixNonNull := reflectedDirectrixNonNull
      focusNotOnDirectrix := reflectedFocusNotOnDirectrix
      scale := reflectedScale
      scaleNonzero := reflectedScaleNonzero
      dEquation := ?_
      eEquation := ?_
      fEquation := ?_
      aEquation := ?_
      bEquation := ?_
      cEquation := ?_ }⟩
  · simpa only [scaledReflectedConic, Conic.scaleConic, Conic.parabolaConic] using dEqual
  · simpa only [scaledReflectedConic, Conic.scaleConic, Conic.parabolaConic] using eEqual
  · simpa only [scaledReflectedConic, Conic.scaleConic, Conic.parabolaConic] using fEqual
  · simpa only [scaledReflectedConic, Conic.scaleConic, Conic.parabolaConic] using aEqual
  · simpa only [scaledReflectedConic, Conic.scaleConic, Conic.parabolaConic] using bEqual
  · simpa only [scaledReflectedConic, Conic.scaleConic, Conic.parabolaConic] using cEqual
end

end Purelib.Curves.Plane.Conic

end

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

variable {K : Type*} [ExplicitField K]

section

/-- Theorem 121 (Parabola reflection): the tangent at a point of a presented parabola makes equal spreads with the focus
line and the altitude to the directrix. The source's implicit requirement that `AF` be non-null is exposed because
otherwise its displayed spread is undefined. -/
theorem parabola_reflection
    [DecidableEq K]
    (conic : Conic K) (focus point : Plane.Point K) (directrix : Plane.Line K)
    (twoNonzero : (2 : K) ≠ 0)
    (presentation : conic.IsParabolaPresentation focus directrix)
    (onParabola : conic.Contains point)
    (focusLineNonNull :
      ¬ (Incidence.lineThrough point focus
        (Conic.parabola_point_ne_focus conic focus point directrix presentation
          onParabola)).IsNull) :
    let pointFocusDistinct :=
      Conic.parabola_point_ne_focus conic focus point directrix presentation
        onParabola
    let nonSingular :=
      Conic.parabola_nonSingularAt conic focus point directrix twoNonzero
        presentation
    let tangent := Conic.tangentLine conic point nonSingular
    let focusLine := Incidence.lineThrough point focus pointFocusDistinct
    let normalLine := Construction.altitudeThrough point directrix
    ∃ tangentNonNull : ¬ tangent.IsNull,
      ∃ normalLineNonNull : ¬ normalLine.IsNull,
        Spread.spread tangent focusLine tangentNonNull focusLineNonNull =
          Spread.spread tangent normalLine tangentNonNull normalLineNonNull := by
  dsimp only
  let pointFocusDistinct :=
    Conic.parabola_point_ne_focus conic focus point directrix presentation
      onParabola
  let nonSingular :=
    Conic.parabola_nonSingularAt conic focus point directrix twoNonzero
      presentation
  let tangent := Conic.tangentLine conic point nonSingular
  let focusLine := Incidence.lineThrough point focus pointFocusDistinct
  let normalLine := Construction.altitudeThrough point directrix
  rcases presentation with ⟨presentation⟩
  let norm := Basic.lineNorm directrix
  let evaluation :=
    directrix.a * point.x + directrix.b * point.y + directrix.c
  let focusEvaluation :=
    directrix.a * focus.x + directrix.b * focus.y + directrix.c
  let scaleTwo := presentation.scale * 2
  have normNonzero : norm ≠ 0 := presentation.directrixNonNull
  have focusEvaluationNonzero : focusEvaluation ≠ 0 := by
    intro evaluationZero
    apply presentation.focusNotOnDirectrix
    exact evaluationZero
  have parabolaEquation :
      norm * Quadrance.quadrance point focus = evaluation ^ 2 := by
    exact Conic.parabola_incidence_residual conic focus point directrix
      presentation onParabola
  have focusLineNorm : Basic.lineNorm focusLine = Quadrance.quadrance point focus := by
    unfold focusLine Basic.lineNorm Incidence.lineThrough Quadrance.quadrance
    ring1
  have focusQuadranceNonzero : Quadrance.quadrance point focus ≠ 0 := by
    intro quadranceZero
    apply focusLineNonNull
    change Basic.lineNorm focusLine = 0
    rw [focusLineNorm, quadranceZero]
  have evaluationNonzero : evaluation ≠ 0 := by
    intro evaluationZero
    have productZero : norm * Quadrance.quadrance point focus = 0 := by
      rw [parabolaEquation, evaluationZero]
      ring1
    exact (ExplicitField.mul_ne_zero normNonzero
      focusQuadranceNonzero) productZero
  have scaleTwoNonzero : scaleTwo ≠ 0 :=
    ExplicitField.mul_ne_zero presentation.scaleNonzero twoNonzero
  have tangentA : tangent.a = scaleTwo *
      (norm * (point.x - focus.x) - directrix.a * evaluation) := by
    change conic.a + 2 * conic.d * point.x + conic.e * point.y = _
    rw [presentation.aEquation, presentation.dEquation,
      presentation.eEquation]
    unfold scaleTwo norm evaluation Basic.lineNorm
    ring1
  have tangentB : tangent.b = scaleTwo *
      (norm * (point.y - focus.y) - directrix.b * evaluation) := by
    change conic.b + conic.e * point.x + 2 * conic.f * point.y = _
    rw [presentation.bEquation, presentation.eEquation,
      presentation.fEquation]
    unfold scaleTwo norm evaluation Basic.lineNorm
    ring1
  have baseTangentNorm :
      (norm * (point.x - focus.x) - directrix.a * evaluation) ^ 2 +
          (norm * (point.y - focus.y) - directrix.b * evaluation) ^ 2 =
        2 * norm * evaluation * focusEvaluation := by
    calc
      (norm * (point.x - focus.x) - directrix.a * evaluation) ^ 2 +
            (norm * (point.y - focus.y) - directrix.b * evaluation) ^ 2 =
          norm * (norm * Quadrance.quadrance point focus -
            2 * evaluation *
              (directrix.a * (point.x - focus.x) +
                directrix.b * (point.y - focus.y)) +
            evaluation ^ 2) := by
        unfold norm Basic.lineNorm Quadrance.quadrance
        ring1
      _ = norm * (evaluation ^ 2 -
            2 * evaluation *
              (directrix.a * (point.x - focus.x) +
                directrix.b * (point.y - focus.y)) +
            evaluation ^ 2) := by
        rw [parabolaEquation]
      _ = 2 * norm * evaluation * focusEvaluation := by
        unfold evaluation focusEvaluation
        ring1
  have tangentNorm :
      Basic.lineNorm tangent =
        (scaleTwo * scaleTwo) *
          (2 * norm * evaluation * focusEvaluation) := by
    unfold Basic.lineNorm
    rw [tangentA, tangentB]
    calc
      (scaleTwo *
              (norm * (point.x - focus.x) -
                directrix.a * evaluation)) ^ 2 +
          (scaleTwo *
              (norm * (point.y - focus.y) -
                directrix.b * evaluation)) ^ 2 =
        (scaleTwo * scaleTwo) *
          ((norm * (point.x - focus.x) -
              directrix.a * evaluation) ^ 2 +
            (norm * (point.y - focus.y) -
              directrix.b * evaluation) ^ 2) := by ring1
      _ = (scaleTwo * scaleTwo) *
          (2 * norm * evaluation * focusEvaluation) := by
        rw [baseTangentNorm]
  have baseNormNonzero :
      2 * norm * evaluation * focusEvaluation ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero
        (ExplicitField.mul_ne_zero twoNonzero normNonzero)
        evaluationNonzero) focusEvaluationNonzero
  have tangentNonNull : ¬ tangent.IsNull := by
    intro tangentNull
    have tangentNormZero : Basic.lineNorm tangent = 0 := tangentNull
    have displayedProductZero :
        (scaleTwo * scaleTwo) *
          (2 * norm * evaluation * focusEvaluation) = 0 := by
      rw [← tangentNorm]
      exact tangentNormZero
    exact (ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero scaleTwoNonzero scaleTwoNonzero)
      baseNormNonzero) displayedProductZero
  have normalLineNonNull : ¬ normalLine.IsNull :=
    Conic.altitudeThrough_nonNull point directrix presentation.directrixNonNull
  have normalLineNorm : Basic.lineNorm normalLine = norm := by
    unfold normalLine Construction.altitudeThrough norm
    unfold Basic.lineNorm
    ring1
  have focusDeterminant :
      tangent.a * focusLine.b - focusLine.a * tangent.b =
        -(scaleTwo * evaluation * focusEvaluation) := by
    rw [tangentA, tangentB]
    unfold focusLine Incidence.lineThrough
    calc
      scaleTwo *
              (norm * (point.x - focus.x) - directrix.a * evaluation) *
            (focus.x - point.x) -
          (point.y - focus.y) *
            (scaleTwo *
              (norm * (point.y - focus.y) - directrix.b * evaluation)) =
        -(scaleTwo *
          (norm * Quadrance.quadrance point focus - evaluation *
            (directrix.a * (point.x - focus.x) +
              directrix.b * (point.y - focus.y)))) := by
        unfold Quadrance.quadrance
        ring1
      _ = -(scaleTwo *
          (evaluation ^ 2 - evaluation *
            (directrix.a * (point.x - focus.x) +
              directrix.b * (point.y - focus.y)))) := by
        rw [parabolaEquation]
      _ = -(scaleTwo * evaluation * focusEvaluation) := by
        unfold evaluation focusEvaluation
        ring1
  have normalDeterminant :
      tangent.a * normalLine.b - normalLine.a * tangent.b =
        -(scaleTwo * norm * focusEvaluation) := by
    rw [tangentA, tangentB]
    unfold normalLine Construction.altitudeThrough
    unfold norm evaluation focusEvaluation
    unfold Basic.lineNorm
    ring1
  have focusLineNormExpanded :
      focusLine.a ^ 2 + focusLine.b ^ 2 = Quadrance.quadrance point focus :=
    focusLineNorm
  have normalLineNormExpanded :
      normalLine.a ^ 2 + normalLine.b ^ 2 = norm :=
    normalLineNorm
  refine ⟨tangentNonNull, normalLineNonNull, ?_⟩
  change
    (tangent.a * focusLine.b - focusLine.a * tangent.b) ^ 2 /
        (Basic.lineNorm tangent * Basic.lineNorm focusLine) =
      (tangent.a * normalLine.b - normalLine.a * tangent.b) ^ 2 /
        (Basic.lineNorm tangent * Basic.lineNorm normalLine)
  apply Ratio.ratio_eq_of_cross_product
    (ExplicitField.mul_ne_zero tangentNonNull focusLineNonNull)
    (ExplicitField.mul_ne_zero tangentNonNull normalLineNonNull)
  rw [focusDeterminant, normalDeterminant, focusLineNormExpanded,
    normalLineNormExpanded]
  calc
    (-(scaleTwo * evaluation * focusEvaluation)) ^ 2 *
          ((tangent.a ^ 2 + tangent.b ^ 2) * norm) =
        scaleTwo ^ 2 * focusEvaluation ^ 2 *
          (tangent.a ^ 2 + tangent.b ^ 2) * norm * evaluation ^ 2 := by
      ring1
    _ = scaleTwo ^ 2 * focusEvaluation ^ 2 *
          (tangent.a ^ 2 + tangent.b ^ 2) * norm *
            (norm * Quadrance.quadrance point focus) := by
      rw [← parabolaEquation]
    _ = (-(scaleTwo * norm * focusEvaluation)) ^ 2 *
          ((tangent.a ^ 2 + tangent.b ^ 2) *
            Quadrance.quadrance point focus) := by
      ring1

end

end Purelib.Curves.Plane.Conic

end
