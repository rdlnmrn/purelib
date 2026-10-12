module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Geometry.Conics.Parabola.Axis
import Purelib.Geometry.Conics.Parabola.Basic
import Purelib.Geometry.Plane.Line.Altitude
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Construction
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Affine.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
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

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Point.Affine

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

/-- The vertex candidate is the midpoint of the focus and its altitude foot on the directrix. -/
def parabolaVertex (focus : Plane.Point K) (directrix :
  Plane.Line K)
    (directrixNonNull : ¬ directrix.IsNull) : Plane.Point K :=
  Affine.midpoint focus (Altitude.altitudeFoot focus directrix directrixNonNull)

/-- The focus does not coincide with its directrix foot in a valid parabola presentation. -/
theorem focus_ne_directrixFoot
    {conic : Conic K} {focus : Plane.Point K} {directrix : Plane.Line K}
    (presentation : Conic.ParabolaPresentationData conic focus directrix) :
    focus ≠ Altitude.altitudeFoot focus directrix presentation.directrixNonNull := by
  intro focusEqualsFoot
  apply presentation.focusNotOnDirectrix
  rw [focusEqualsFoot]
  exact Altitude.altitudeFoot_on_line focus directrix presentation.directrixNonNull

/-- Every point on the focus altitude has the same directrix foot as the focus itself. -/
theorem altitudeFoot_eq_focusFoot_of_on_parabolaAxis
    (focus point : Plane.Point K) (directrix : Plane.Line K)
    (directrixNonNull : ¬ directrix.IsNull)
    (onAxis : (Conic.parabolaAxis focus directrix).Contains point) :
    Altitude.altitudeFoot point directrix directrixNonNull =
      Altitude.altitudeFoot focus directrix directrixNonNull := by
  let focusFoot := Altitude.altitudeFoot focus directrix directrixNonNull
  have focusFootOnDirectrix : directrix.Contains focusFoot :=
    Altitude.altitudeFoot_on_line focus directrix directrixNonNull
  have focusFootOnAxis :
      (Conic.parabolaAxis focus directrix).Contains focusFoot := by
    exact Altitude.altitudeFoot_on_altitude focus directrix directrixNonNull
  have constantEqual :
      (Conic.parabolaAxis focus directrix).c =
        (Construction.altitudeThrough point directrix).c := by
    apply Construction.altitudeThrough_unique point directrix (Conic.parabolaAxis focus directrix)
    · rfl
    · rfl
    · exact onAxis
  have focusFootOnPointAltitude :
      (Construction.altitudeThrough point directrix).Contains focusFoot := by
    unfold Plane.Line.Contains at focusFootOnAxis ⊢
    change
      -directrix.b * focusFoot.x + directrix.a * focusFoot.y +
          (Construction.altitudeThrough point directrix).c = 0
    rw [← constantEqual]
    exact focusFootOnAxis
  exact (Altitude.altitudeFoot_unique point directrix directrixNonNull focusFoot
    focusFootOnDirectrix focusFootOnPointAltitude).symm

/-- The vertex candidate lies on the canonical axis. -/
theorem parabolaVertex_on_axis
    (focus : Plane.Point K) (directrix : Plane.Line K)
    (directrixNonNull : ¬ directrix.IsNull)
    (twoNonzero : (2 : K) ≠ 0) :
    (Conic.parabolaAxis focus directrix).Contains
      (parabolaVertex focus directrix directrixNonNull) := by
  have focusContains := Conic.parabolaAxis_contains_focus focus directrix
  have footContains :
      (Conic.parabolaAxis focus directrix).Contains
        (Altitude.altitudeFoot focus directrix directrixNonNull) :=
    Altitude.altitudeFoot_on_altitude focus directrix directrixNonNull
  unfold Plane.Line.Contains at focusContains footContains ⊢
  unfold parabolaVertex Affine.midpoint
  have firstCoordinateCancel :
      (focus.x + (Altitude.altitudeFoot focus directrix directrixNonNull).x) / 2 * 2 =
        focus.x + (Altitude.altitudeFoot focus directrix directrixNonNull).x :=
    ExplicitField.div_mul_cancel _ twoNonzero
  have secondCoordinateCancel :
      (focus.y + (Altitude.altitudeFoot focus directrix directrixNonNull).y) / 2 * 2 =
        focus.y + (Altitude.altitudeFoot focus directrix directrixNonNull).y :=
    ExplicitField.div_mul_cancel _ twoNonzero
  apply ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero
  calc
    2 *
        ((Conic.parabolaAxis focus directrix).a *
            ((focus.x +
              (Altitude.altitudeFoot focus directrix directrixNonNull).x) / 2) +
          (Conic.parabolaAxis focus directrix).b *
            ((focus.y +
              (Altitude.altitudeFoot focus directrix directrixNonNull).y) / 2) +
          (Conic.parabolaAxis focus directrix).c) =
      ((Conic.parabolaAxis focus directrix).a * focus.x +
          (Conic.parabolaAxis focus directrix).b * focus.y +
          (Conic.parabolaAxis focus directrix).c) +
        ((Conic.parabolaAxis focus directrix).a *
            (Altitude.altitudeFoot focus directrix directrixNonNull).x +
          (Conic.parabolaAxis focus directrix).b *
            (Altitude.altitudeFoot focus directrix directrixNonNull).y +
          (Conic.parabolaAxis focus directrix).c) := by
            calc
              2 *
                  ((Conic.parabolaAxis focus directrix).a *
                      ((focus.x +
                        (Altitude.altitudeFoot focus directrix
                          directrixNonNull).x) / 2) +
                    (Conic.parabolaAxis focus directrix).b *
                      ((focus.y +
                        (Altitude.altitudeFoot focus directrix
                          directrixNonNull).y) / 2) +
                    (Conic.parabolaAxis focus directrix).c) =
                (Conic.parabolaAxis focus directrix).a *
                    (((focus.x +
                      (Altitude.altitudeFoot focus directrix
                        directrixNonNull).x) / 2) * 2) +
                  (Conic.parabolaAxis focus directrix).b *
                    (((focus.y +
                      (Altitude.altitudeFoot focus directrix
                        directrixNonNull).y) / 2) * 2) +
                  2 * (Conic.parabolaAxis focus directrix).c := by ring1
              _ = _ := by
                rw [firstCoordinateCancel, secondCoordinateCancel]
                ring1
    _ = 0 := by rw [focusContains, footContains]; ring1

/-- The vertex candidate lies on the presented parabola. -/
theorem parabolaVertex_contains [DecidableEq K]
    (conic : Conic K) (focus : Plane.Point K) (directrix : Plane.Line K)
    (presentation : Conic.ParabolaPresentationData conic focus directrix)
    (twoNonzero : (2 : K) ≠ 0) :
    conic.Contains
      (parabolaVertex focus directrix presentation.directrixNonNull) := by
  let vertex :=
    parabolaVertex focus directrix presentation.directrixNonNull
  have vertexOnAxis : (Conic.parabolaAxis focus directrix).Contains vertex :=
    parabolaVertex_on_axis focus directrix presentation.directrixNonNull
      twoNonzero
  have vertexFoot :=
    altitudeFoot_eq_focusFoot_of_on_parabolaAxis focus vertex directrix
      presentation.directrixNonNull vertexOnAxis
  apply (Conic.contains_iff_equal_quadrances_of_presentation presentation).2
  unfold Quadrance.pointLineQuadrance
  rw [vertexFoot]
  exact Quadrance.midpoint_equal_quadrance focus
    (Altitude.altitudeFoot focus directrix presentation.directrixNonNull) twoNonzero

/-- The focus-to-foot side is non-null; its quadrance is the nonzero quadrance from the focus to the directrix. -/
theorem focus_directrixFoot_line_nonNull [DecidableEq K]
    {conic : Conic K} {focus : Plane.Point K} {directrix : Plane.Line K}
    (presentation : Conic.ParabolaPresentationData conic focus directrix) :
    let focusFoot :=
      Altitude.altitudeFoot focus directrix presentation.directrixNonNull
    let distinct := focus_ne_directrixFoot presentation
    ¬ (Incidence.lineThrough focus focusFoot distinct).IsNull := by
  dsimp only
  let focusFoot :=
    Altitude.altitudeFoot focus directrix presentation.directrixNonNull
  have lineValueNonzero : Conic.lineValue directrix focus ≠ 0 := by
    intro valueZero
    apply presentation.focusNotOnDirectrix
    exact valueZero
  have valueSquareNonzero : Conic.lineValue directrix focus ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      ExplicitField.mul_ne_zero lineValueNonzero lineValueNonzero
  have focusLineQuadranceNonzero :
      Quadrance.pointLineQuadrance focus directrix presentation.directrixNonNull ≠ 0 := by
    rw [Quadrance.pointLineQuadrance_formula]
    exact ExplicitField.div_ne_zero valueSquareNonzero
      presentation.directrixNonNull
  have focusFootQuadranceNonzero : Quadrance.quadrance focus focusFoot ≠ 0 := by
    exact focusLineQuadranceNonzero
  intro sideNull
  exact focusFootQuadranceNonzero
    ((Quadrance.null_line_iff_quadrance_zero focus focusFoot
      (focus_ne_directrixFoot presentation)).1 sideNull)

/-- Any point lying both on a presented parabola and its canonical axis is the displayed vertex. -/
theorem parabolaVertex_unique [DecidableEq K]
    (conic : Conic K) (focus point : Plane.Point K) (directrix : Plane.Line K)
    (presentation : Conic.ParabolaPresentationData conic focus directrix)
    (twoNonzero : (2 : K) ≠ 0)
    (onParabola : conic.Contains point)
    (onAxis : (Conic.parabolaAxis focus directrix).Contains point) :
    point = parabolaVertex focus directrix presentation.directrixNonNull := by
  let focusFoot :=
    Altitude.altitudeFoot focus directrix presentation.directrixNonNull
  have distinct : focus ≠ focusFoot := focus_ne_directrixFoot presentation
  have throughEquivalentAxis :
      (Incidence.lineThrough focus focusFoot distinct).Equivalent
        (Conic.parabolaAxis focus directrix) := by
    apply Incidence.lineThrough_unique focus focusFoot distinct
    · exact Conic.parabolaAxis_contains_focus focus directrix
    · exact Altitude.altitudeFoot_on_altitude focus directrix
        presentation.directrixNonNull
  have pointOnThrough :
      (Incidence.lineThrough focus focusFoot distinct).Contains point := by
    exact Relations.line_contains_of_equivalent
      (Plane.Line.equivalent_symm throughEquivalentAxis) point onAxis
  have pointFoot :=
    altitudeFoot_eq_focusFoot_of_on_parabolaAxis focus point directrix
      presentation.directrixNonNull onAxis
  have equalQuadrances :
      Quadrance.quadrance point focus = Quadrance.quadrance point focusFoot := by
    have metricEquality :=
      (Conic.contains_iff_equal_quadrances_of_presentation presentation).1
        onParabola
    calc
      Quadrance.quadrance point focus =
          Quadrance.pointLineQuadrance point directrix
            presentation.directrixNonNull := metricEquality
      _ = Quadrance.quadrance point
          (Altitude.altitudeFoot point directrix presentation.directrixNonNull) := rfl
      _ = Quadrance.quadrance point focusFoot := by rw [pointFoot]
  have sideNonNull :
      ¬ (Incidence.lineThrough focus focusFoot distinct).IsNull :=
    focus_directrixFoot_line_nonNull presentation
  have midpointUnique := Quadrance.midpoint_unique_of_equal_quadrance focus focusFoot
    point distinct twoNonzero sideNonNull pointOnThrough equalQuadrances
  exact midpointUnique

/-- Exercise 15.9: a presented parabola and its unique axis have exactly one common point, the explicit focus/directrix
midpoint vertex. -/
theorem exercise_15_9 [DecidableEq K]
    (conic : Conic K) (twoNonzero : (2 : K) ≠ 0)
    (isParabola : conic.IsParabola) :
    ∃ focus : Plane.Point K, ∃ directrix : Plane.Line K,
      ∃ presentation : Conic.ParabolaPresentationData conic focus directrix,
        let vertex := parabolaVertex focus directrix
          presentation.directrixNonNull
        conic.Contains vertex ∧
          (Conic.parabolaAxis focus directrix).Contains vertex ∧
          ∀ point : Plane.Point K, conic.Contains point →
            (Conic.parabolaAxis focus directrix).Contains point → point = vertex := by
  rcases isParabola with ⟨focus, directrix, presentation⟩
  rcases presentation with ⟨presentation⟩
  let vertex :=
    parabolaVertex focus directrix presentation.directrixNonNull
  refine ⟨focus, directrix, presentation, ?_, ?_, ?_⟩
  · exact parabolaVertex_contains conic focus directrix presentation
      twoNonzero
  · exact parabolaVertex_on_axis focus directrix
      presentation.directrixNonNull twoNonzero
  · intro point onParabola onAxis
    exact parabolaVertex_unique conic focus point directrix presentation
      twoNonzero onParabola onAxis

end

end Purelib.Curves.Plane.Conic

end
