module
public import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Affine
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Affine

open Purelib.Geometry.Plane.Line.Basic

section
@[expose] public section

/-!
# Divine Proportions, §15.6: intersections with lines

The restriction of a conic to a displayed line parameter is handled by one
finite interpolation identity.  Thus Theorem 102 needs no completed polynomial
object and no general theorem about a globally collected root set.
-/

namespace Purelib.Curves.Plane.Conic.LineIntersection

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section Conic

/-- A displayed point of intersection of a conic and a line. -/
def IntersectsAt (conic : Conic K) (line :
  Geometry.Plane.Line K) (point : Geometry.Plane.Point K) : Prop :=
  line.Contains point ∧ conic.Contains point

/-- A chord is witnessed by exactly the two distinct intersections needed by the definition. -/
def IsChord (conic : Conic K) (line :
  Geometry.Plane.Line K) : Prop :=
  ∃ first second : Geometry.Plane.Point K,
    first ≠ second ∧ IntersectsAt conic line first ∧
      IntersectsAt conic line second

/-- Three-or-more intersections are represented by three explicit pairwise distinct witnesses. -/
def HasThreeDistinctIntersections (conic : Conic K)
  (line : Geometry.Plane.Line K) : Prop :=
  ∃ first second third : Geometry.Plane.Point K,
    first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      IntersectsAt conic line first ∧
      IntersectsAt conic line second ∧
      IntersectsAt conic line third

/-- The quadratic coefficient obtained by restricting a conic to the direction from `first` to `second`. -/
def lineRestrictionQuadratic (conic : Conic K)
    (first second : Geometry.Plane.Point K) : K :=
  conic.d * (second.x - first.x) ^ 2 +
    conic.e * (second.x - first.x) * (second.y - first.y) +
    conic.f * (second.y - first.y) ^ 2

/-- Exact quadratic interpolation for the conic restricted to a line. -/
theorem evaluate_thalesPoint (conic : Conic K)
    (first second : Geometry.Plane.Point K) (scale : K) :
    conic.evaluate (Purelib.Geometry.Plane.Line.Affine.thalesPoint scale first second) =
      (1 - scale) * conic.evaluate first +
        scale * conic.evaluate second +
        scale * (scale - 1) *
          lineRestrictionQuadratic conic first second := by
  unfold Conic.evaluate Affine.thalesPoint Point.Affine.affineCombination
    lineRestrictionQuadratic
  ring1

/-- Theorem 102 (Conic line intersection): three explicit distinct intersections force the whole line to lie on the
conic. -/
theorem conic_line_intersection [DecidableEq K]
    (conic : Conic K) (line : Geometry.Plane.Line K)
    (threeIntersections : HasThreeDistinctIntersections conic line) :
    ∀ point : Geometry.Plane.Point K, line.Contains point → conic.Contains point := by
  rcases threeIntersections with
    ⟨first, second, third, firstSecondDistinct, firstThirdDistinct,
      secondThirdDistinct, firstIntersection, secondIntersection,
      thirdIntersection⟩
  have throughEquivalentLine :
      (Incidence.lineThrough first second firstSecondDistinct).Equivalent line :=
    Incidence.lineThrough_unique first second firstSecondDistinct line
      firstIntersection.1 secondIntersection.1
  have throughContains :
      ∀ point : Geometry.Plane.Point K, line.Contains point →
        (Incidence.lineThrough first second firstSecondDistinct).Contains point := by
    intro point onLine
    exact Relations.line_contains_of_equivalent
      (Geometry.Plane.Line.equivalent_symm throughEquivalentLine) point onLine
  rcases Conic.thalesPoint_exists_of_on_line first second third
      firstSecondDistinct (throughContains third thirdIntersection.1) with
    ⟨thirdScale, thirdParameter⟩
  have thirdScaleNonzero : thirdScale ≠ 0 := by
    intro scaleZero
    apply firstThirdDistinct
    calc
      first = Affine.thalesPoint 0 first second := (Conic.thalesPoint_zero first second).symm
      _ = Affine.thalesPoint thirdScale first second := by rw [scaleZero]
      _ = third := thirdParameter
  have thirdScaleMinusOneNonzero : thirdScale - 1 ≠ 0 := by
    intro differenceZero
    have scaleOne : thirdScale = 1 := by
      calc
        thirdScale = (thirdScale - 1) + 1 := by ring1
        _ = 1 := by rw [differenceZero]; ring1
    apply secondThirdDistinct
    calc
      second = Affine.thalesPoint 1 first second := (Conic.thalesPoint_one first second).symm
      _ = Affine.thalesPoint thirdScale first second := by rw [scaleOne]
      _ = third := thirdParameter
  have firstZero : conic.evaluate first = 0 := firstIntersection.2
  have secondZero : conic.evaluate second = 0 := secondIntersection.2
  have thirdZero :
      conic.evaluate (Affine.thalesPoint thirdScale first second) = 0 := by
    rw [thirdParameter]
    exact thirdIntersection.2
  have restrictionProductZero :
      (thirdScale * (thirdScale - 1)) *
        lineRestrictionQuadratic conic first second = 0 := by
    calc
      (thirdScale * (thirdScale - 1)) *
          lineRestrictionQuadratic conic first second =
        conic.evaluate (Affine.thalesPoint thirdScale first second) := by
          rw [evaluate_thalesPoint, firstZero, secondZero]
          ring1
      _ = 0 := thirdZero
  have scaleProductNonzero : thirdScale * (thirdScale - 1) ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero thirdScaleNonzero
      thirdScaleMinusOneNonzero
  have restrictionZero :
      lineRestrictionQuadratic conic first second = 0 := by
    have inverseCancel :
        (thirdScale * (thirdScale - 1))⁻¹ *
            (thirdScale * (thirdScale - 1)) = (1 : K) := by
      calc
        (thirdScale * (thirdScale - 1))⁻¹ *
            (thirdScale * (thirdScale - 1)) =
          (thirdScale * (thirdScale - 1)) *
            (thirdScale * (thirdScale - 1))⁻¹ := by ring1
        _ = 1 := Algebra.Field.ExplicitField.mul_inv_cancel _ scaleProductNonzero
    calc
      lineRestrictionQuadratic conic first second =
          1 * lineRestrictionQuadratic conic first second := by ring1
      _ = ((thirdScale * (thirdScale - 1))⁻¹ *
            (thirdScale * (thirdScale - 1))) *
          lineRestrictionQuadratic conic first second := by rw [inverseCancel]
      _ = (thirdScale * (thirdScale - 1))⁻¹ *
          ((thirdScale * (thirdScale - 1)) *
            lineRestrictionQuadratic conic first second) := mul_assoc _ _ _
      _ = 0 := by rw [restrictionProductZero]; ring1
  intro point onLine
  rcases Conic.thalesPoint_exists_of_on_line first second point
      firstSecondDistinct (throughContains point onLine) with
    ⟨scale, parameter⟩
  unfold Conic.Contains
  rw [← parameter, evaluate_thalesPoint, firstZero, secondZero,
    restrictionZero]
  ring1

end Conic

end Purelib.Curves.Plane.Conic.LineIntersection

end
