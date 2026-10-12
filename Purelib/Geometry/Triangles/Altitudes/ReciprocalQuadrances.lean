module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Ratio.Cleared
import Purelib.Algebra.Proportions.QuadTriple.Reciprocal
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Parallel.Through
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Line.Twist
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Triangles.Right.Trigonometry
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

open Purelib.Geometry.Trigonometry

section
@[expose] public section

/-!
# Divine Proportions, Chapter 21: two-dimensional problems

The applications are separated into their finite metric identities and the
geometric incidence arguments that supply those identities.  Denominators are
always accompanied by explicit nonzero certificates.
-/

namespace Purelib.Geometry.Triangles.Altitudes.ReciprocalQuadrances

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Problem 4, geometric form. The displayed lines are the three finite line witnesses in the source: the base line and
the two transversal lines through `B₁,B₂,A₃` and `A₁,B₂,B₃`. The non-perpendicular and nonzero premises are exactly the
denominator conditions in the two applications of the Twist ratio theorem and in the final reciprocal statement. -/
theorem problem_4 [Nontrivial K] [DecidableEq K]
    (a₁ a₂ a₃ b₁ b₂ b₃ : Purelib.Geometry.Plane.Point K)
    (base crossAtA₃ crossAtA₁ : Purelib.Geometry.Plane.Line K)
    (twoNonzero : (2 : K) ≠ 0)
    (a₁a₂Distinct : a₁ ≠ a₂) (a₁a₃Distinct : a₁ ≠ a₃)
    (a₂a₃Distinct : a₂ ≠ a₃)
    (a₁b₁Distinct : a₁ ≠ b₁) (a₂b₂Distinct : a₂ ≠ b₂)
    (a₃b₃Distinct : a₃ ≠ b₃)
    (a₃b₁Distinct : a₃ ≠ b₁) (a₃b₂Distinct : a₃ ≠ b₂)
    (a₁b₂Distinct : a₁ ≠ b₂) (a₁b₃Distinct : a₁ ≠ b₃)
    (baseContainsA₁ : base.Contains a₁)
    (baseContainsA₂ : base.Contains a₂)
    (baseContainsA₃ : base.Contains a₃)
    (crossAtA₃ContainsA₃ : crossAtA₃.Contains a₃)
    (crossAtA₃ContainsB₁ : crossAtA₃.Contains b₁)
    (crossAtA₃ContainsB₂ : crossAtA₃.Contains b₂)
    (crossAtA₁ContainsA₁ : crossAtA₁.Contains a₁)
    (crossAtA₁ContainsB₂ : crossAtA₁.Contains b₂)
    (crossAtA₁ContainsB₃ : crossAtA₁.Contains b₃)
    (firstAltitude :
      base.Perpendicular
        (Incidence.lineThrough b₁ a₁ a₁b₁Distinct.symm))
    (secondAltitude :
      base.Perpendicular
        (Incidence.lineThrough b₂ a₂ a₂b₂Distinct.symm))
    (thirdAltitude :
      base.Perpendicular
        (Incidence.lineThrough b₃ a₃ a₃b₃Distinct.symm))
    (firstTwistAtA₃Defined :
      ¬ (Incidence.lineThrough a₃ b₂ a₃b₂Distinct).Perpendicular
          (Incidence.lineThrough a₃ a₂ a₂a₃Distinct.symm))
    (firstTwistAtA₃ComparisonDefined :
      ¬ (Incidence.lineThrough a₃ b₁ a₃b₁Distinct).Perpendicular
          (Incidence.lineThrough a₃ a₁ a₁a₃Distinct.symm))
    (secondTwistAtA₁Defined :
      ¬ (Incidence.lineThrough a₁ b₂ a₁b₂Distinct).Perpendicular
          (Incidence.lineThrough a₁ a₂ a₁a₂Distinct))
    (secondTwistAtA₁ComparisonDefined :
      ¬ (Incidence.lineThrough a₁ b₃ a₁b₃Distinct).Perpendicular
          (Incidence.lineThrough a₁ a₃ a₁a₃Distinct))
    (p₁Nonzero : Quadrance.quadrance a₂ a₃ ≠ 0)
    (p₂Nonzero : Quadrance.quadrance a₁ a₃ ≠ 0)
    (p₃Nonzero : Quadrance.quadrance a₁ a₂ ≠ 0)
    (q₁Nonzero : Quadrance.quadrance a₁ b₁ ≠ 0)
    (q₂Nonzero : Quadrance.quadrance a₂ b₂ ≠ 0)
    (q₃Nonzero : Quadrance.quadrance a₃ b₃ ≠ 0) :
    Purelib.Geometry.Trigonometry.QuadTriple (1 / Quadrance.quadrance a₁ b₁) (1 / Quadrance.quadrance a₂ b₂)
      (1 / Quadrance.quadrance a₃ b₃) := by
  let base₃₂ := Incidence.lineThrough a₃ a₂ a₂a₃Distinct.symm
  let base₃₁ := Incidence.lineThrough a₃ a₁ a₁a₃Distinct.symm
  let base₁₂ := Incidence.lineThrough a₁ a₂ a₁a₂Distinct
  let base₁₃ := Incidence.lineThrough a₁ a₃ a₁a₃Distinct
  let altitude₁ := Incidence.lineThrough b₁ a₁ a₁b₁Distinct.symm
  let altitude₂ := Incidence.lineThrough b₂ a₂ a₂b₂Distinct.symm
  let altitude₃ := Incidence.lineThrough b₃ a₃ a₃b₃Distinct.symm
  let cross₃₂ := Incidence.lineThrough a₃ b₂ a₃b₂Distinct
  let cross₃₁ := Incidence.lineThrough a₃ b₁ a₃b₁Distinct
  let cross₁₂ := Incidence.lineThrough a₁ b₂ a₁b₂Distinct
  let cross₁₃ := Incidence.lineThrough a₁ b₃ a₁b₃Distinct
  have base₃₂Parallel : base₃₂.Parallel base :=
    Relations.line_parallel_of_equivalent
      (Incidence.lineThrough_unique a₃ a₂ a₂a₃Distinct.symm base
        baseContainsA₃ baseContainsA₂)
  have base₃₁Parallel : base₃₁.Parallel base :=
    Relations.line_parallel_of_equivalent
      (Incidence.lineThrough_unique a₃ a₁ a₁a₃Distinct.symm base
        baseContainsA₃ baseContainsA₁)
  have base₁₂Parallel : base₁₂.Parallel base :=
    Relations.line_parallel_of_equivalent
      (Incidence.lineThrough_unique a₁ a₂ a₁a₂Distinct base
        baseContainsA₁ baseContainsA₂)
  have base₁₃Parallel : base₁₃.Parallel base :=
    Relations.line_parallel_of_equivalent
      (Incidence.lineThrough_unique a₁ a₃ a₁a₃Distinct base
        baseContainsA₁ baseContainsA₃)
  have rightAtA₂FromA₃ : base₃₂.Perpendicular altitude₂ :=
    Relations.perpendicular_of_parallel_left_direct base base₃₂ altitude₂
      (Line.parallel_symm base₃₂Parallel) secondAltitude
  have rightAtA₁FromA₃ : base₃₁.Perpendicular altitude₁ :=
    Relations.perpendicular_of_parallel_left_direct base base₃₁ altitude₁
      (Line.parallel_symm base₃₁Parallel) firstAltitude
  have rightAtA₂FromA₁ : base₁₂.Perpendicular altitude₂ :=
    Relations.perpendicular_of_parallel_left_direct base base₁₂ altitude₂
      (Line.parallel_symm base₁₂Parallel) secondAltitude
  have rightAtA₃FromA₁ : base₁₃.Perpendicular altitude₃ :=
    Relations.perpendicular_of_parallel_left_direct base base₁₃ altitude₃
      (Line.parallel_symm base₁₃Parallel) thirdAltitude
  have crossAtA₃Parallel : cross₃₂.Parallel cross₃₁ :=
    Parallel.Through.parallel_pair_through_common_line a₃ b₂ b₁ a₃b₂Distinct
      a₃b₁Distinct crossAtA₃ crossAtA₃ContainsA₃
      crossAtA₃ContainsB₂ crossAtA₃ContainsB₁
  have baseAtA₃Parallel : base₃₂.Parallel base₃₁ :=
    Relations.line_parallel_trans base₃₂Parallel (Line.parallel_symm base₃₁Parallel)
  have crossAtA₁Parallel : cross₁₂.Parallel cross₁₃ :=
    Parallel.Through.parallel_pair_through_common_line a₁ b₂ b₃ a₁b₂Distinct
      a₁b₃Distinct crossAtA₁ crossAtA₁ContainsA₁
      crossAtA₁ContainsB₂ crossAtA₁ContainsB₃
  have baseAtA₁Parallel : base₁₂.Parallel base₁₃ :=
    Relations.line_parallel_trans base₁₂Parallel (Line.parallel_symm base₁₃Parallel)
  have firstTwistRatio := Right.Trigonometry.twist_ratio a₃ b₂ a₂ a₃b₂Distinct
    a₂a₃Distinct.symm a₂b₂Distinct.symm
    (by
      intro zero
      exact p₁Nonzero ((Quadrance.quadrance_symm a₂ a₃).trans zero))
    rightAtA₂FromA₃ firstTwistAtA₃Defined
  have firstComparisonRatio := Right.Trigonometry.twist_ratio a₃ b₁ a₁ a₃b₁Distinct
    a₁a₃Distinct.symm a₁b₁Distinct.symm
    (by
      intro zero
      exact p₂Nonzero ((Quadrance.quadrance_symm a₁ a₃).trans zero))
    rightAtA₁FromA₃ firstTwistAtA₃ComparisonDefined
  have firstTwistsEqual := Twist.twist_eq_of_parallel_pairs
    cross₃₂ base₃₂ cross₃₁ base₃₁ firstTwistAtA₃Defined
      firstTwistAtA₃ComparisonDefined crossAtA₃Parallel baseAtA₃Parallel
  have firstRatiosEqual :
      Quadrance.quadrance a₂ b₂ / Quadrance.quadrance a₂ a₃ =
        Quadrance.quadrance a₁ b₁ / Quadrance.quadrance a₁ a₃ := by
    calc
      Quadrance.quadrance a₂ b₂ / Quadrance.quadrance a₂ a₃ =
          Twist.twist cross₃₂ base₃₂ firstTwistAtA₃Defined := by
            rw [firstTwistRatio]
            simp only [Quadrance.quadrance_symm, -eq_self, -iff_self]
            rfl
      _ = Twist.twist cross₃₁ base₃₁ firstTwistAtA₃ComparisonDefined :=
        firstTwistsEqual
      _ = Quadrance.quadrance a₁ b₁ / Quadrance.quadrance a₁ a₃ := by
        rw [firstComparisonRatio]
        simp only [Quadrance.quadrance_symm, -eq_self, -iff_self]
        rfl
  have secondTwistRatio := Right.Trigonometry.twist_ratio a₁ b₂ a₂ a₁b₂Distinct
    a₁a₂Distinct a₂b₂Distinct.symm p₃Nonzero
    rightAtA₂FromA₁ secondTwistAtA₁Defined
  have secondComparisonRatio := Right.Trigonometry.twist_ratio a₁ b₃ a₃ a₁b₃Distinct
    a₁a₃Distinct a₃b₃Distinct.symm p₂Nonzero
    rightAtA₃FromA₁ secondTwistAtA₁ComparisonDefined
  have secondTwistsEqual := Twist.twist_eq_of_parallel_pairs
    cross₁₂ base₁₂ cross₁₃ base₁₃ secondTwistAtA₁Defined
      secondTwistAtA₁ComparisonDefined crossAtA₁Parallel baseAtA₁Parallel
  have secondRatiosEqual :
      Quadrance.quadrance a₂ b₂ / Quadrance.quadrance a₁ a₂ =
        Quadrance.quadrance a₃ b₃ / Quadrance.quadrance a₁ a₃ := by
    calc
      Quadrance.quadrance a₂ b₂ / Quadrance.quadrance a₁ a₂ =
          Twist.twist cross₁₂ base₁₂ secondTwistAtA₁Defined := by
            rw [secondTwistRatio]
            simp only [Quadrance.quadrance_symm, -eq_self, -iff_self]
            rfl
      _ = Twist.twist cross₁₃ base₁₃ secondTwistAtA₁ComparisonDefined :=
        secondTwistsEqual
      _ = Quadrance.quadrance a₃ b₃ / Quadrance.quadrance a₁ a₃ := by
        rw [secondComparisonRatio]
        simp only [Quadrance.quadrance_symm, -eq_self, -iff_self]
        rfl
  have firstCrossRelation := Ratio.Cleared.cross_mul_of_div_eq_div
    p₁Nonzero p₂Nonzero firstRatiosEqual
  have secondCrossRelation := Ratio.Cleared.cross_mul_of_div_eq_div p₃Nonzero p₂Nonzero
    secondRatiosEqual
  have baseQuadTriple :
      Purelib.Geometry.Trigonometry.QuadTriple (Quadrance.quadrance a₂ a₃) (Quadrance.quadrance a₁ a₃)
        (Quadrance.quadrance a₁ a₂) := by
    unfold Purelib.Geometry.Trigonometry.QuadTriple
    apply (Quadrea.Basic.triple_quad_formula a₁ a₂ a₃ twoNonzero).2
    exact ⟨base, baseContainsA₁, baseContainsA₂, baseContainsA₃⟩
  apply Proportions.QuadTriple.Reciprocal.problem_4_from_twist_relations
    (Quadrance.quadrance a₂ a₃) (Quadrance.quadrance a₁ a₃) (Quadrance.quadrance a₁ a₂)
    (Quadrance.quadrance a₁ b₁) (Quadrance.quadrance a₂ b₂) (Quadrance.quadrance a₃ b₃)
    p₂Nonzero q₁Nonzero q₂Nonzero q₃Nonzero baseQuadTriple
  · calc
      Quadrance.quadrance a₂ a₃ * Quadrance.quadrance a₁ b₁ =
          Quadrance.quadrance a₁ b₁ * Quadrance.quadrance a₂ a₃ := by ring1
      _ = Quadrance.quadrance a₂ b₂ * Quadrance.quadrance a₁ a₃ := firstCrossRelation.symm
      _ = Quadrance.quadrance a₁ a₃ * Quadrance.quadrance a₂ b₂ := by ring1
  · calc
      Quadrance.quadrance a₁ a₂ * Quadrance.quadrance a₃ b₃ =
          Quadrance.quadrance a₃ b₃ * Quadrance.quadrance a₁ a₂ := by ring1
      _ = Quadrance.quadrance a₂ b₂ * Quadrance.quadrance a₁ a₃ := secondCrossRelation.symm
      _ = Quadrance.quadrance a₁ a₃ * Quadrance.quadrance a₂ b₂ := by ring1
end
end Purelib.Geometry.Triangles.Altitudes.ReciprocalQuadrances

end
