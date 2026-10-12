module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Squares
import Purelib.Geometry.Circles.Projective.Basic
public import Purelib.Geometry.Circles.Projective.Parametrization
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Point.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Curves.Plane.Conic.Basic
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

open Purelib.Curves.Plane (Conic)

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

public section

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- The canonical line through the origin corresponding to parameter `λ`. -/
@[expose] def projectiveCircleLine [Nontrivial K] (parameter : K) :
  Plane.Line K where
  a := -1
  b := parameter
  c := 0
  direction_nonzero := Or.inl ((by intro negZero; have restored := congrArg (fun value : K => -value) negZero; rewrite
    [neg_neg, SubNegZeroMonoid.neg_zero] at restored; exact one_ne_zero restored))

/-- An admissible projective-circle point is not the distinguished origin. -/
theorem projectiveCirclePoint_ne_origin [Nontrivial K]
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    Conic.projectiveCirclePoint parameter ≠ Conic.projectiveCircleOrigin := by
  have denominatorNonzero : 1 + parameter ^ 2 ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter).2
      squareNotNegativeOne
  intro pointEqualsOrigin
  have yEqualsZero := congrArg Plane.Point.y pointEqualsOrigin
  change 1 / (1 + parameter ^ 2) = 0 at yEqualsZero
  apply (one_ne_zero : (1 : K) ≠ 0)
  calc
    (1 : K) = (1 / (1 + parameter ^ 2)) *
        (1 + parameter ^ 2) :=
      (ExplicitField.div_mul_cancel 1 denominatorNonzero).symm
    _ = 0 := by rw [yEqualsZero]; ring1

/-- The canonical ray contains the origin. -/
theorem projectiveCircleLine_contains_origin [Nontrivial K]
    (parameter : K) :
    (projectiveCircleLine parameter).Contains Conic.projectiveCircleOrigin := by
  unfold projectiveCircleLine Conic.projectiveCircleOrigin Plane.Line.Contains
  ring1

/-- The canonical ray contains its parametrized point. -/
theorem projectiveCircleLine_contains_point [Nontrivial K]
    (parameter : K) :
    (projectiveCircleLine parameter).Contains
      (Conic.projectiveCirclePoint parameter) := by
  unfold projectiveCircleLine Conic.projectiveCirclePoint Plane.Line.Contains
  rw [ExplicitField.div_eq_mul_inv,
    ExplicitField.div_eq_mul_inv]
  ring1

/-- The geometric line through the two points is equivalent to the canonical coefficient representative `⟨-1:λ:0⟩`. -/
theorem lineThrough_projectiveCirclePoint_equivalent [Nontrivial K]
    [DecidableEq K]
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    (Incidence.lineThrough Conic.projectiveCircleOrigin (Conic.projectiveCirclePoint parameter)
      (Ne.symm (projectiveCirclePoint_ne_origin parameter
        squareNotNegativeOne))).Equivalent
      (projectiveCircleLine parameter) := by
  apply Incidence.lineThrough_unique Conic.projectiveCircleOrigin
    (Conic.projectiveCirclePoint parameter)
    (Ne.symm (projectiveCirclePoint_ne_origin parameter squareNotNegativeOne))
  · exact projectiveCircleLine_contains_origin parameter
  · exact projectiveCircleLine_contains_point parameter

/-- Canonical projective rays are equivalent exactly when their parameters are equal. -/
theorem projectiveCircleLine_equivalent_iff [Nontrivial K]
    (left right : K) :
    (projectiveCircleLine left).Equivalent
        (projectiveCircleLine right) ↔ left = right := by
  constructor
  · intro equivalent
    have directionEquation := equivalent.1
    change (-1 : K) * right = -1 * left at directionEquation
    calc
      left = -((-1 : K) * left) := by ring1
      _ = -((-1 : K) * right) := by rw [directionEquation]
      _ = right := by ring1
  · intro equal
    rw [equal]
    exact Plane.Line.equivalent_refl _

/-- Two non-origin projective-circle points determine equivalent origin rays exactly when the points are equal. This is
the injective half of Exercise 16.7 without quotienting displayed lines. -/
theorem projectiveCircle_origin_rays_equivalent_iff [Nontrivial K]
    [DecidableEq K]
    (left right : Plane.Point K)
    (leftOnCircle : Conic.projectiveCircle.Contains left)
    (rightOnCircle : Conic.projectiveCircle.Contains right)
    (leftNotOrigin : left ≠ Conic.projectiveCircleOrigin)
    (rightNotOrigin : right ≠ Conic.projectiveCircleOrigin) :
    (Incidence.lineThrough Conic.projectiveCircleOrigin left (Ne.symm leftNotOrigin)).Equivalent
        (Incidence.lineThrough Conic.projectiveCircleOrigin right (Ne.symm rightNotOrigin)) ↔
      left = right := by
  constructor
  · intro raysEquivalent
    rcases Conic.projectiveCirclePoint_exists left leftOnCircle leftNotOrigin with
      ⟨leftParameter, leftAdmissible, leftFormula⟩
    rcases Conic.projectiveCirclePoint_exists right rightOnCircle rightNotOrigin with
      ⟨rightParameter, rightAdmissible, rightFormula⟩
    have leftCanonical :
        (Incidence.lineThrough Conic.projectiveCircleOrigin left
          (Ne.symm leftNotOrigin)).Equivalent
            (projectiveCircleLine leftParameter) := by
      apply Incidence.lineThrough_unique Conic.projectiveCircleOrigin left
        (Ne.symm leftNotOrigin)
      · exact projectiveCircleLine_contains_origin leftParameter
      · rw [leftFormula]
        exact projectiveCircleLine_contains_point leftParameter
    have rightCanonical :
        (Incidence.lineThrough Conic.projectiveCircleOrigin right
          (Ne.symm rightNotOrigin)).Equivalent
            (projectiveCircleLine rightParameter) := by
      apply Incidence.lineThrough_unique Conic.projectiveCircleOrigin right
        (Ne.symm rightNotOrigin)
      · exact projectiveCircleLine_contains_origin rightParameter
      · rw [rightFormula]
        exact projectiveCircleLine_contains_point rightParameter
    have canonicalEquivalent :
        (projectiveCircleLine leftParameter).Equivalent
          (projectiveCircleLine rightParameter) :=
      Relations.line_equivalent_trans (Line.equivalent_symm leftCanonical)
        (Relations.line_equivalent_trans raysEquivalent rightCanonical)
    have parametersEqual :=
      (projectiveCircleLine_equivalent_iff
        leftParameter rightParameter).1 canonicalEquivalent
    calc
      left = Conic.projectiveCirclePoint leftParameter := leftFormula
      _ = Conic.projectiveCirclePoint rightParameter := by rw [parametersEqual]
      _ = right := rightFormula.symm
  · intro pointsEqual
    subst right
    exact Line.equivalent_refl _

/-- Exercise 16.7: non-origin points on the projective circle and displayed lines through the origin with such an
intersection are in one-to-one correspondence, expressed through quotient-free line equivalence. -/
theorem exercise_16_7 [Nontrivial K] [DecidableEq K] :
    (∀ (left right : Plane.Point K)
      (_leftOnCircle : Conic.projectiveCircle.Contains left)
      (_rightOnCircle : Conic.projectiveCircle.Contains right)
      (leftNotOrigin : left ≠ Conic.projectiveCircleOrigin)
      (rightNotOrigin : right ≠ Conic.projectiveCircleOrigin),
      (Incidence.lineThrough Conic.projectiveCircleOrigin left (Ne.symm leftNotOrigin)).Equivalent
          (Incidence.lineThrough Conic.projectiveCircleOrigin right
            (Ne.symm rightNotOrigin)) ↔ left = right) ∧
    (∀ line : Plane.Line K,
      line.Contains Conic.projectiveCircleOrigin →
      (∃ point : Plane.Point K,
        Conic.projectiveCircle.Contains point ∧
          point ≠ Conic.projectiveCircleOrigin ∧ line.Contains point) →
      ∃ point : Plane.Point K,
        ∃ pointNotOrigin : point ≠ Conic.projectiveCircleOrigin,
          Conic.projectiveCircle.Contains point ∧
          (Incidence.lineThrough Conic.projectiveCircleOrigin point
            (Ne.symm pointNotOrigin)).Equivalent line) := by
  constructor
  · exact projectiveCircle_origin_rays_equivalent_iff
  · intro line originOnLine
    rintro ⟨point, pointOnCircle, pointNotOrigin, pointOnLine⟩
    refine ⟨point, pointNotOrigin, pointOnCircle, ?_⟩
    exact Incidence.lineThrough_unique Conic.projectiveCircleOrigin point
      (Ne.symm pointNotOrigin) line originOnLine pointOnLine

end

end Purelib.Curves.Plane.Conic

end

end
