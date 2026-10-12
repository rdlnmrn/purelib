module
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Cross
import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Line.Intersection
import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Trigonometry.Conversion
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Reflection.Line
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Reflection

section
@[expose] public section

/-!
# Divine Proportions, §12.5: the incenter spread theorem

This module formalizes the source's translated-coordinate proof.  The
incenter is the origin; `firstMirror` and `secondMirror` are the first two
vertex bisectors, and `target` is the side joining their triangle vertices.
Reflecting `target` in those mirrors gives the other two sides.  The displayed
third line joins the origin to their intersection.

The key computation is denominator-free: the third line's spread with the
first reflected side equals the cross of the two initial mirrors.  Fibonacci's
spread-plus-cross identity then gives the printed complementary spread.
-/

namespace Purelib.Geometry.Triangles.Incenter.Spread

variable {K : Type*} [ExplicitField K]

/-- The first coefficient of the third bisector direction formed from the two norm-scaled reflected lines. -/
def incenterThirdDirectionA
    (firstMirror secondMirror target : Plane.Line K) : K :=
  Line.Basic.lineNorm secondMirror * Line.reflectedLineA firstMirror target -
    Line.Basic.lineNorm firstMirror * Line.reflectedLineA secondMirror target

/-- The second coefficient of the third bisector direction formed from the two norm-scaled reflected lines. -/
def incenterThirdDirectionB
    (firstMirror secondMirror target : Plane.Line K) : K :=
  Line.Basic.lineNorm secondMirror * Line.reflectedLineB firstMirror target -
    Line.Basic.lineNorm firstMirror * Line.reflectedLineB secondMirror target

/-- The polynomial norm identity ensuring that the displayed third direction is nonzero. -/
theorem incenterThirdDirection_norm
    (firstMirror secondMirror target : Plane.Line K) :
    incenterThirdDirectionA firstMirror secondMirror target ^ 2 +
        incenterThirdDirectionB firstMirror secondMirror target ^ 2 =
      4 * Line.Basic.lineNorm firstMirror * Line.Basic.lineNorm secondMirror *
        (firstMirror.a * secondMirror.b -
          secondMirror.a * firstMirror.b) ^ 2 * Line.Basic.lineNorm target := by
  unfold incenterThirdDirectionA
    incenterThirdDirectionB Line.reflectedLineA
    Line.reflectedLineB Line.Basic.lineNorm
  ring1

/-- The origin line with the third bisector direction determined by two reflected lines.

The mirrors and reflected line are non-null, the mirror directions are nonparallel and two is nonzero; these
certificates prove that the displayed direction is nonzero. -/
def normalizedIncenterThirdLine [DecidableEq K]
    (firstMirror secondMirror target : Plane.Line K)
    (firstMirrorNonNull : ¬ firstMirror.IsNull)
    (secondMirrorNonNull : ¬ secondMirror.IsNull)
    (targetNonNull : ¬ target.IsNull)
    (mirrorsNonparallel : ¬ firstMirror.Parallel secondMirror)
    (twoNonzero : (2 : K) ≠ 0) : Plane.Line K where
  a := incenterThirdDirectionA firstMirror secondMirror target
  b := incenterThirdDirectionB firstMirror secondMirror target
  c := 0
  direction_nonzero := by
    have fourAsProduct : (4 : K) = 2 * 2 := by ring1
    have fourNonzero : (4 : K) ≠ 0 := by
      rw [fourAsProduct]
      exact ExplicitField.mul_ne_zero twoNonzero twoNonzero
    have mirrorDeterminantNonzero :
        firstMirror.a * secondMirror.b -
          secondMirror.a * firstMirror.b ≠ 0 := mirrorsNonparallel
    have normNonzero :
        4 * Line.Basic.lineNorm firstMirror * Line.Basic.lineNorm secondMirror *
          (firstMirror.a * secondMirror.b -
            secondMirror.a * firstMirror.b) ^ 2 * Line.Basic.lineNorm target ≠ 0 :=
      ExplicitField.mul_ne_zero
        (ExplicitField.mul_ne_zero
          (ExplicitField.mul_ne_zero
            (ExplicitField.mul_ne_zero fourNonzero firstMirrorNonNull)
            secondMirrorNonNull)
          (ExplicitField.square_nonzero_of_nonzero mirrorDeterminantNonzero))
        targetNonNull
    by_cases firstNonzero :
        incenterThirdDirectionA firstMirror secondMirror target ≠ 0
    · exact Or.inl firstNonzero
    · right
      intro secondZero
      apply normNonzero
      rw [← incenterThirdDirection_norm firstMirror secondMirror target]
      have firstZero :
          incenterThirdDirectionA firstMirror secondMirror target = 0 := by
        by_cases equality :
            incenterThirdDirectionA firstMirror secondMirror target = 0
        · exact equality
        · exact False.elim (firstNonzero equality)
      rw [firstZero, secondZero]
      ring1

/-- The displayed third line is non-null. -/
theorem normalizedIncenterThirdLine_nonNull [DecidableEq K]
    (firstMirror secondMirror target : Plane.Line K)
    (firstMirrorNonNull : ¬ firstMirror.IsNull)
    (secondMirrorNonNull : ¬ secondMirror.IsNull)
    (targetNonNull : ¬ target.IsNull)
    (mirrorsNonparallel : ¬ firstMirror.Parallel secondMirror)
    (twoNonzero : (2 : K) ≠ 0) :
    ¬ (normalizedIncenterThirdLine firstMirror secondMirror target
      firstMirrorNonNull secondMirrorNonNull targetNonNull
      mirrorsNonparallel twoNonzero).IsNull := by
  intro nullThird
  have mirrorDeterminantNonzero :
      firstMirror.a * secondMirror.b -
        secondMirror.a * firstMirror.b ≠ 0 := mirrorsNonparallel
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [fourAsProduct]
    exact ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have rightNonzero :
      4 * Line.Basic.lineNorm firstMirror * Line.Basic.lineNorm secondMirror *
        (firstMirror.a * secondMirror.b -
          secondMirror.a * firstMirror.b) ^ 2 * Line.Basic.lineNorm target ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero
        (ExplicitField.mul_ne_zero
          (ExplicitField.mul_ne_zero fourNonzero firstMirrorNonNull)
          secondMirrorNonNull)
        (ExplicitField.square_nonzero_of_nonzero mirrorDeterminantNonzero))
      targetNonNull
  apply rightNonzero
  rw [← incenterThirdDirection_norm firstMirror secondMirror target]
  exact nullThird

/-- The third-line spread computed in the source is the cross of the two initial bisectors. -/
theorem normalized_incenter_third_spread_eq_cross
    [Nontrivial K] [DecidableEq K]
    (firstMirror secondMirror target : Plane.Line K)
    (firstMirrorNonNull : ¬ firstMirror.IsNull)
    (secondMirrorNonNull : ¬ secondMirror.IsNull)
    (targetNonNull : ¬ target.IsNull)
    (mirrorsNonparallel : ¬ firstMirror.Parallel secondMirror)
    (twoNonzero : (2 : K) ≠ 0) :
    let thirdLine := normalizedIncenterThirdLine firstMirror secondMirror target
      firstMirrorNonNull secondMirrorNonNull targetNonNull
      mirrorsNonparallel twoNonzero
    let thirdLineNonNull := normalizedIncenterThirdLine_nonNull
      firstMirror secondMirror target firstMirrorNonNull secondMirrorNonNull
      targetNonNull mirrorsNonparallel twoNonzero
    let reflectedSideNonNull := Line.reflectLine_nonNull firstMirror target
      firstMirrorNonNull targetNonNull
    Spread.spread thirdLine (Line.reflectLine firstMirror target firstMirrorNonNull)
        thirdLineNonNull reflectedSideNonNull =
      Cross.cross firstMirror secondMirror firstMirrorNonNull secondMirrorNonNull := by
  dsimp only
  let thirdLine := normalizedIncenterThirdLine firstMirror secondMirror target
    firstMirrorNonNull secondMirrorNonNull targetNonNull mirrorsNonparallel
    twoNonzero
  let thirdLineNonNull := normalizedIncenterThirdLine_nonNull
    firstMirror secondMirror target firstMirrorNonNull secondMirrorNonNull
    targetNonNull mirrorsNonparallel twoNonzero
  let reflectedSide := Line.reflectLine firstMirror target firstMirrorNonNull
  let reflectedSideNonNull := Line.reflectLine_nonNull firstMirror target
    firstMirrorNonNull targetNonNull
  have leftDenominatorNonzero :
      Line.Basic.lineNorm thirdLine * Line.Basic.lineNorm reflectedSide ≠ 0 :=
    ExplicitField.mul_ne_zero thirdLineNonNull reflectedSideNonNull
  have rightDenominatorNonzero :
      Line.Basic.lineNorm firstMirror * Line.Basic.lineNorm secondMirror ≠ 0 :=
    ExplicitField.mul_ne_zero firstMirrorNonNull secondMirrorNonNull
  unfold Spread.spread Cross.cross
  apply Ratio.ratio_eq_of_cross_product leftDenominatorNonzero
    rightDenominatorNonzero
  unfold thirdLine reflectedSide normalizedIncenterThirdLine
    incenterThirdDirectionA
      incenterThirdDirectionB Line.reflectLine
    Line.reflectedLineA Line.reflectedLineB Line.Basic.lineNorm
  ring1

/-- The third line passes through the translated incenter `[0,0]`. -/
theorem normalizedIncenterThirdLine_contains_origin [DecidableEq K]
    (firstMirror secondMirror target : Plane.Line K)
    (firstMirrorNonNull : ¬ firstMirror.IsNull)
    (secondMirrorNonNull : ¬ secondMirror.IsNull)
    (targetNonNull : ¬ target.IsNull)
    (mirrorsNonparallel : ¬ firstMirror.Parallel secondMirror)
    (twoNonzero : (2 : K) ≠ 0) :
    (normalizedIncenterThirdLine firstMirror secondMirror target
      firstMirrorNonNull secondMirrorNonNull targetNonNull
      mirrorsNonparallel twoNonzero).Contains (⟨0, 0⟩ : Plane.Point K) := by
  unfold normalizedIncenterThirdLine Plane.Line.Contains
  ring1

/-- When the reflected sides meet, the displayed third line also contains their intersection. -/
theorem normalizedIncenterThirdLine_contains_reflected_intersection
    [DecidableEq K]
    (firstMirror secondMirror target : Plane.Line K)
    (firstMirrorNonNull : ¬ firstMirror.IsNull)
    (secondMirrorNonNull : ¬ secondMirror.IsNull)
    (targetNonNull : ¬ target.IsNull)
    (mirrorsNonparallel : ¬ firstMirror.Parallel secondMirror)
    (twoNonzero : (2 : K) ≠ 0)
    (firstMirrorThroughOrigin : firstMirror.c = 0)
    (secondMirrorThroughOrigin : secondMirror.c = 0)
    (reflectedSidesNonparallel :
      ¬ (Line.reflectLine firstMirror target firstMirrorNonNull).Parallel
        (Line.reflectLine secondMirror target secondMirrorNonNull)) :
    let thirdLine := normalizedIncenterThirdLine firstMirror secondMirror target
      firstMirrorNonNull secondMirrorNonNull targetNonNull
      mirrorsNonparallel twoNonzero
    thirdLine.Contains
      (Intersection.lineIntersection
        (Line.reflectLine firstMirror target firstMirrorNonNull)
        (Line.reflectLine secondMirror target secondMirrorNonNull)
        reflectedSidesNonparallel) := by
  dsimp only
  apply Intersection.lineIntersection_on_third_of_determinant_eq_zero
    (Line.reflectLine firstMirror target firstMirrorNonNull)
    (Line.reflectLine secondMirror target secondMirrorNonNull)
    (normalizedIncenterThirdLine firstMirror secondMirror target
      firstMirrorNonNull secondMirrorNonNull targetNonNull
      mirrorsNonparallel twoNonzero)
    reflectedSidesNonparallel
  unfold Incidence.lineDeterminant normalizedIncenterThirdLine
    incenterThirdDirectionA
      incenterThirdDirectionB Line.reflectLine
    Line.reflectedLineA Line.reflectedLineB Line.reflectedLineC Line.Basic.lineNorm
  rw [firstMirrorThroughOrigin, secondMirrorThroughOrigin]
  ring1

/-- Theorem 89 (Incenter spread), in the translated coordinates used by the book's proof. The first two conjuncts
certify that `thirdLine` is exactly the line from the incenter to the third vertex. -/
theorem incenter_spread
    [Nontrivial K] [DecidableEq K]
    (firstMirror secondMirror target : Plane.Line K)
    (firstMirrorNonNull : ¬ firstMirror.IsNull)
    (secondMirrorNonNull : ¬ secondMirror.IsNull)
    (targetNonNull : ¬ target.IsNull)
    (mirrorsNonparallel : ¬ firstMirror.Parallel secondMirror)
    (twoNonzero : (2 : K) ≠ 0)
    (firstMirrorThroughOrigin : firstMirror.c = 0)
    (secondMirrorThroughOrigin : secondMirror.c = 0)
    (reflectedSidesNonparallel :
      ¬ (Line.reflectLine firstMirror target firstMirrorNonNull).Parallel
        (Line.reflectLine secondMirror target secondMirrorNonNull)) :
    let thirdLine := normalizedIncenterThirdLine firstMirror secondMirror target
      firstMirrorNonNull secondMirrorNonNull targetNonNull
      mirrorsNonparallel twoNonzero
    let thirdLineNonNull := normalizedIncenterThirdLine_nonNull
      firstMirror secondMirror target firstMirrorNonNull secondMirrorNonNull
      targetNonNull mirrorsNonparallel twoNonzero
    let reflectedSideNonNull := Line.reflectLine_nonNull firstMirror target
      firstMirrorNonNull targetNonNull
    thirdLine.Contains (⟨0, 0⟩ : Plane.Point K) ∧
      thirdLine.Contains
        (Intersection.lineIntersection
          (Line.reflectLine firstMirror target firstMirrorNonNull)
          (Line.reflectLine secondMirror target secondMirrorNonNull)
          reflectedSidesNonparallel) ∧
      Spread.spread firstMirror secondMirror firstMirrorNonNull secondMirrorNonNull =
        1 - Spread.spread thirdLine
          (Line.reflectLine firstMirror target firstMirrorNonNull)
          thirdLineNonNull reflectedSideNonNull := by
  dsimp only
  have thirdSpread := normalized_incenter_third_spread_eq_cross
    firstMirror secondMirror target firstMirrorNonNull secondMirrorNonNull
    targetNonNull mirrorsNonparallel twoNonzero
  have fibonacci := Trigonometry.Conversion.spread_add_cross firstMirror secondMirror
    firstMirrorNonNull secondMirrorNonNull
  refine ⟨normalizedIncenterThirdLine_contains_origin firstMirror secondMirror
    target firstMirrorNonNull secondMirrorNonNull targetNonNull
    mirrorsNonparallel twoNonzero, ?_, ?_⟩
  · apply normalizedIncenterThirdLine_contains_reflected_intersection
      firstMirror secondMirror target firstMirrorNonNull secondMirrorNonNull
      targetNonNull mirrorsNonparallel twoNonzero firstMirrorThroughOrigin
      secondMirrorThroughOrigin reflectedSidesNonparallel
  · calc
      Spread.spread firstMirror secondMirror firstMirrorNonNull secondMirrorNonNull =
          1 - Cross.cross firstMirror secondMirror firstMirrorNonNull
            secondMirrorNonNull := by
              rw [← fibonacci]
              ring1
      _ = 1 - Spread.spread
          (normalizedIncenterThirdLine firstMirror secondMirror target
            firstMirrorNonNull secondMirrorNonNull targetNonNull
            mirrorsNonparallel twoNonzero)
          (Line.reflectLine firstMirror target firstMirrorNonNull)
          (normalizedIncenterThirdLine_nonNull firstMirror secondMirror target
            firstMirrorNonNull secondMirrorNonNull targetNonNull
            mirrorsNonparallel twoNonzero)
          (Line.reflectLine_nonNull firstMirror target firstMirrorNonNull
            targetNonNull) := by rw [thirdSpread]
end Purelib.Geometry.Triangles.Incenter.Spread

end
