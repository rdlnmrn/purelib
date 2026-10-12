module
public import Purelib.Geometry.Conics.Axis
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Conics.Quadrola.Basic
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Line.PerpendicularBisector
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Plane.Reflection.PerpendicularBisector
import Purelib.Geometry.Plane.Reflection.Point
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Conics.Quadrola

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Reflection

open Purelib.Geometry.Plane.Reflection.Point

section
@[expose] public section

/-!
# Divine Proportions, §15.4 and Exercise 19.3: quadrolas

A quadrola is given by one finite Archimedes polynomial in the two focal
quadrances and its associated quadrance.  The apparent quartic terms cancel
to an explicit conic.  Its gradient tangent satisfies the equal-spread
reflection property by a denominator-cleared polynomial identity.
-/

section Purelib.Geometry

section Quadrola

variable {K : Type*} [ExplicitField K]

end Quadrola
end Purelib.Geometry

section
variable {K : Type*} [ExplicitField K]

namespace Purelib.Geometry.Conics.Quadrola

/-- A non-null mirror fixing both foci is an axis of the quadrola conic.

Reflection preserves each focal quadrance and therefore preserves the complete Archimedes polynomial. -/
private theorem conic_isAxis_of_fixed_foci
  [DecidableEq K]
    (firstFocus secondFocus : Plane.Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (axis : Plane.Line K)
    (axisNonNull : ¬ axis.IsNull)
    (firstFixed : Reflection.Point.reflectPoint axis axisNonNull firstFocus = firstFocus)
    (secondFixed : Reflection.Point.reflectPoint axis axisNonNull secondFocus = secondFocus) :
    (Quadrola.conic firstFocus secondFocus associatedQuadrance associatedNonzero
      eightNonzero).IsAxis axis := by
  refine ⟨axisNonNull, ?_⟩
  intro point
  have firstQuadrance :
      Quadrance.quadrance (Reflection.Point.reflectPoint axis axisNonNull point) firstFocus =
        Quadrance.quadrance point firstFocus := by
    calc
      Quadrance.quadrance (Reflection.Point.reflectPoint axis axisNonNull point) firstFocus =
          Quadrance.quadrance (Reflection.Point.reflectPoint axis axisNonNull point)
            (Reflection.Point.reflectPoint axis axisNonNull firstFocus) := by rw [firstFixed]
      _ = Quadrance.quadrance point firstFocus :=
        Reflection.Point.reflectPoint_preserves_quadrance axis axisNonNull point firstFocus
  have secondQuadrance :
      Quadrance.quadrance (Reflection.Point.reflectPoint axis axisNonNull point) secondFocus =
        Quadrance.quadrance point secondFocus := by
    calc
      Quadrance.quadrance (Reflection.Point.reflectPoint axis axisNonNull point) secondFocus =
          Quadrance.quadrance (Reflection.Point.reflectPoint axis axisNonNull point)
            (Reflection.Point.reflectPoint axis axisNonNull secondFocus) := by rw [secondFixed]
      _ = Quadrance.quadrance point secondFocus :=
        Reflection.Point.reflectPoint_preserves_quadrance axis axisNonNull point secondFocus
  calc
    (Quadrola.conic firstFocus secondFocus associatedQuadrance associatedNonzero
          eightNonzero).evaluate (Reflection.Point.reflectPoint axis axisNonNull point) =
        Quadrola.evaluate firstFocus secondFocus associatedQuadrance
          (Reflection.Point.reflectPoint axis axisNonNull point) :=
      Quadrola.conic_evaluate firstFocus secondFocus associatedQuadrance associatedNonzero
        eightNonzero (Reflection.Point.reflectPoint axis axisNonNull point)
    _ = Quadrola.evaluate firstFocus secondFocus associatedQuadrance point := by
      unfold Quadrola.evaluate
      rw [firstQuadrance, secondQuadrance]
    _ = (Quadrola.conic firstFocus secondFocus associatedQuadrance associatedNonzero
          eightNonzero).evaluate point :=
      (Quadrola.conic_evaluate firstFocus secondFocus associatedQuadrance
        associatedNonzero eightNonzero point).symm
/-- A non-null mirror swapping the foci is an axis of the quadrola conic.

The reflected focal quadrances are exchanged, and symmetry of the Archimedes polynomial preserves the displayed
equation. -/
private theorem conic_isAxis_of_swapped_foci
  [DecidableEq K]
    (firstFocus secondFocus : Plane.Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (axis : Plane.Line K)
    (axisNonNull : ¬ axis.IsNull)
    (firstToSecond : Reflection.Point.reflectPoint axis axisNonNull firstFocus = secondFocus)
    (secondToFirst : Reflection.Point.reflectPoint axis axisNonNull secondFocus = firstFocus) :
    (Quadrola.conic firstFocus secondFocus associatedQuadrance associatedNonzero
      eightNonzero).IsAxis axis := by
  refine ⟨axisNonNull, ?_⟩
  intro point
  have firstQuadrance :
      Quadrance.quadrance (Reflection.Point.reflectPoint axis axisNonNull point) firstFocus =
        Quadrance.quadrance point secondFocus := by
    calc
      Quadrance.quadrance (Reflection.Point.reflectPoint axis axisNonNull point) firstFocus =
          Quadrance.quadrance (Reflection.Point.reflectPoint axis axisNonNull point)
            (Reflection.Point.reflectPoint axis axisNonNull secondFocus) := by rw [secondToFirst]
      _ = Quadrance.quadrance point secondFocus :=
        Reflection.Point.reflectPoint_preserves_quadrance axis axisNonNull point secondFocus
  have secondQuadrance :
      Quadrance.quadrance (Reflection.Point.reflectPoint axis axisNonNull point) secondFocus =
        Quadrance.quadrance point firstFocus := by
    calc
      Quadrance.quadrance (Reflection.Point.reflectPoint axis axisNonNull point) secondFocus =
          Quadrance.quadrance (Reflection.Point.reflectPoint axis axisNonNull point)
            (Reflection.Point.reflectPoint axis axisNonNull firstFocus) := by rw [firstToSecond]
      _ = Quadrance.quadrance point firstFocus :=
        Reflection.Point.reflectPoint_preserves_quadrance axis axisNonNull point firstFocus
  calc
    (Quadrola.conic firstFocus secondFocus associatedQuadrance associatedNonzero
          eightNonzero).evaluate (Reflection.Point.reflectPoint axis axisNonNull point) =
        Quadrola.evaluate firstFocus secondFocus associatedQuadrance
          (Reflection.Point.reflectPoint axis axisNonNull point) :=
      Quadrola.conic_evaluate firstFocus secondFocus associatedQuadrance associatedNonzero
        eightNonzero (Reflection.Point.reflectPoint axis axisNonNull point)
    _ = Quadrola.evaluate firstFocus secondFocus associatedQuadrance point := by
      unfold Quadrola.evaluate
      rw [firstQuadrance, secondQuadrance]
      unfold Trigonometry.QuadTriple.Basic.archimedesFunction
      ring1
    _ = (Quadrola.conic firstFocus secondFocus associatedQuadrance associatedNonzero
          eightNonzero).evaluate point :=
      (Quadrola.conic_evaluate firstFocus secondFocus associatedQuadrance
        associatedNonzero eightNonzero point).symm
end Purelib.Geometry.Conics.Quadrola
end

namespace Purelib.Geometry.Conics.Quadrola.Axis

section

variable {K : Type*} [ExplicitField K]

/-- Exercise 15.13: the focal line and the perpendicular bisector of the foci are two inequivalent axes of every
quadrola. Both mirrors are proved non-null from the definition's explicit nonzero focal quadrance. -/
theorem exercise_15_13 [DecidableEq K]
    (firstFocus secondFocus : Plane.Point K) (associatedQuadrance : K)
    (presentation : Quadrola.Presentation firstFocus secondFocus associatedQuadrance)
    (eightNonzero : (8 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    let focalAxis :=
      Incidence.lineThrough firstFocus secondFocus presentation.fociDistinct
    let transverseAxis :=
      PerpendicularBisector.perpendicularBisector firstFocus secondFocus presentation.fociDistinct
    ¬ focalAxis.Equivalent transverseAxis ∧
      (Quadrola.conic firstFocus secondFocus associatedQuadrance
          presentation.associatedNonzero eightNonzero).IsAxis focalAxis ∧
      (Quadrola.conic firstFocus secondFocus associatedQuadrance
          presentation.associatedNonzero eightNonzero).IsAxis transverseAxis := by
  dsimp only
  let focalAxis :=
    Incidence.lineThrough firstFocus secondFocus presentation.fociDistinct
  let transverseAxis :=
    PerpendicularBisector.perpendicularBisector firstFocus secondFocus presentation.fociDistinct
  have focalNonNull : ¬ focalAxis.IsNull := by
    intro focalNull
    apply presentation.focusQuadranceNonzero
    calc
      Quadrance.quadrance firstFocus secondFocus = Basic.lineNorm focalAxis := by
        unfold focalAxis
        exact (Quadrance.lineThrough_norm_eq_quadrance firstFocus secondFocus
          presentation.fociDistinct).symm
      _ = 0 := focalNull
  have transverseNonNull : ¬ transverseAxis.IsNull := by
    intro transverseNull
    apply presentation.focusQuadranceNonzero
    calc
      Quadrance.quadrance firstFocus secondFocus = Basic.lineNorm transverseAxis := by
        unfold transverseAxis PerpendicularBisector.perpendicularBisector Basic.lineNorm Quadrance.quadrance
        ring1
      _ = 0 := transverseNull
  have axesInequivalent : ¬ focalAxis.Equivalent transverseAxis := by
    intro equivalent
    apply presentation.focusQuadranceNonzero
    calc
      Quadrance.quadrance firstFocus secondFocus =
          focalAxis.a * transverseAxis.b -
            transverseAxis.a * focalAxis.b := by
        unfold focalAxis transverseAxis Incidence.lineThrough PerpendicularBisector.perpendicularBisector
          Quadrance.quadrance
        ring1
      _ = 0 := by rw [equivalent.1]; ring1
  have firstFixed :
      Reflection.Point.reflectPoint focalAxis focalNonNull firstFocus = firstFocus := by
    apply Axis.reflectPoint_fixed_of_contains focalAxis focalNonNull firstFocus
    unfold focalAxis
    exact Incidence.lineThrough_contains_first firstFocus secondFocus
      presentation.fociDistinct
  have secondFixed :
      Reflection.Point.reflectPoint focalAxis focalNonNull secondFocus = secondFocus := by
    apply Axis.reflectPoint_fixed_of_contains focalAxis focalNonNull secondFocus
    unfold focalAxis
    exact Incidence.lineThrough_contains_second firstFocus secondFocus
      presentation.fociDistinct
  have firstToSecond :
      Reflection.Point.reflectPoint transverseAxis transverseNonNull firstFocus =
        secondFocus := by
    unfold transverseAxis
    exact PerpendicularBisector.reflectPoint_perpendicularBisector_first firstFocus secondFocus
      presentation.fociDistinct twoNonzero transverseNonNull
  have secondToFirst :
      Reflection.Point.reflectPoint transverseAxis transverseNonNull secondFocus =
        firstFocus := by
    unfold transverseAxis
    exact PerpendicularBisector.reflectPoint_perpendicularBisector_second firstFocus secondFocus
      presentation.fociDistinct twoNonzero transverseNonNull
  exact ⟨axesInequivalent,
    conic_isAxis_of_fixed_foci firstFocus secondFocus
      associatedQuadrance
      presentation.associatedNonzero eightNonzero focalAxis focalNonNull
      firstFixed secondFixed,
    conic_isAxis_of_swapped_foci firstFocus secondFocus
      associatedQuadrance
      presentation.associatedNonzero eightNonzero transverseAxis
      transverseNonNull firstToSecond secondToFirst⟩
end

end Purelib.Geometry.Conics.Quadrola.Axis

end
