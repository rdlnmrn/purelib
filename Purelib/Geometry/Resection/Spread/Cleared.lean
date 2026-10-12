module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Point.Quadrance.FourPoint
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Geometry.Quadrilaterals.Basic

open Purelib.Geometry.Trigonometry

open Purelib.Geometry.Trigonometry.Spread.Triple

section
public section

/-!
# Divine Proportions, Chapter 25: resection and Hansen's problem

The large rational calculations are represented by common-denominator
integer certificates.  The general resection theorem is proved from the
denominator-free Four-point polynomial, so neither a root search nor a
completed coordinate field is used.
-/

namespace Purelib.Geometry.Resection.Spread.Cleared

section

variable {K : Type*} [ExplicitField K]

/-! ## Problem 24: Snellius--Pothenot resection -/

/-- The scalar center numerator in the cleared resection quadratic.

It is the product of the two three-term sums minus twice their coordinatewise product sum. -/
@[expose] def resectionCenterNumerator
    (q₁ q₂ q₃ r₁ r₂ r₃ : K) : K :=
  (q₁ + q₂ + q₃) * (r₁ + r₂ + r₃) -
    2 * (q₁ * r₁ + q₂ * r₂ + q₃ * r₃)

/-- The centered resection root `2 * r₃ * R₃ - centerNumerator`. -/
@[expose] def resectionCenteredRoot
    (q₁ q₂ q₃ r₁ r₂ r₃ R₃ : K) : K :=
  2 * r₃ * R₃ - resectionCenterNumerator q₁ q₂ q₃ r₁ r₂ r₃

/-- The general centered resection quadratic with every denominator cleared: `(R₃-C)²=D` becomes `(2r₃R₃-Cnum)²=4r₃r₁r₂
A(Q₁,Q₂,Q₃)`. -/
theorem problem_24_cleared [DecidableEq K]
    (q₁ q₂ q₃ r₁ r₂ r₃ R₁ R₂ R₃ : K)
    (q₃Nonzero : q₃ ≠ 0) (r₃Nonzero : r₃ ≠ 0)
    (spreadTriple : TripleSpread.SpreadTriple r₁ r₂ r₃)
    (firstSpreadLaw : r₃ * R₁ = r₂ * q₃)
    (secondSpreadLaw : r₃ * R₂ = r₁ * q₃)
    (fourPointRelation :
      Quadrilateral.eulerFunction q₁ q₂ q₃ R₁ R₂ R₃ = 0) :
    resectionCenteredRoot q₁ q₂ q₃ r₁ r₂ r₃ R₃ ^ 2 =
      4 * r₃ * r₁ * r₂ * QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ := by
  let fourPointNumerator :=
    Quadrilateral.fourPointQuadraticNumerator q₁ q₂ q₃ R₁ R₂ R₃
  let centerNumerator := resectionCenterNumerator q₁ q₂ q₃ r₁ r₂ r₃
  let centeredRoot := 2 * r₃ * R₃ - centerNumerator
  have numeratorEquation :
      fourPointNumerator ^ 2 =
        QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ *
          QuadTriple.Basic.archimedesFunction R₁ R₂ q₃ := by
    have identity := Quadrilateral.fourPoint_quadratic_identity
      q₁ q₂ q₃ R₁ R₂ R₃
    unfold fourPointNumerator
    apply Group.eq_of_sub_eq_zero
    calc
      Quadrilateral.fourPointQuadraticNumerator q₁ q₂ q₃ R₁ R₂ R₃ ^ 2 -
          QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ *
            QuadTriple.Basic.archimedesFunction R₁ R₂ q₃ =
        -2 * q₃ *
          Quadrilateral.eulerFunction q₁ q₂ q₃ R₁ R₂ R₃ :=
            identity
      _ = 0 := by rw [fourPointRelation]; ring1
  have numeratorCenterRelation :
      r₃ * fourPointNumerator = q₃ * centeredRoot := by
    unfold fourPointNumerator centeredRoot centerNumerator
      Quadrilateral.fourPointQuadraticNumerator resectionCenterNumerator
    calc
      r₃ *
          (q₃ * (2 * R₃ - R₁ - R₂ + q₃ - q₁ - q₂) +
            (q₁ - q₂) * (R₂ - R₁)) =
        q₃ *
            (2 * r₃ * R₃ - r₃ * R₁ - r₃ * R₂ +
              r₃ * q₃ - r₃ * q₁ - r₃ * q₂) +
          (q₁ - q₂) * (r₃ * R₂ - r₃ * R₁) := by ring1
      _ = q₃ *
            (2 * r₃ * R₃ - r₂ * q₃ - r₁ * q₃ +
              r₃ * q₃ - r₃ * q₁ - r₃ * q₂) +
          (q₁ - q₂) * (r₁ * q₃ - r₂ * q₃) := by
            rw [firstSpreadLaw, secondSpreadLaw]
      _ = q₃ *
          (2 * r₃ * R₃ -
            ((q₁ + q₂ + q₃) * (r₁ + r₂ + r₃) -
              2 * (q₁ * r₁ + q₂ * r₂ + q₃ * r₃))) := by ring1
  have scaledArchimedes :
      r₃ ^ 2 * QuadTriple.Basic.archimedesFunction R₁ R₂ q₃ =
        q₃ ^ 2 * QuadTriple.Basic.archimedesFunction r₂ r₁ r₃ := by
    calc
      r₃ ^ 2 * QuadTriple.Basic.archimedesFunction R₁ R₂ q₃ =
          QuadTriple.Basic.archimedesFunction (r₃ * R₁) (r₃ * R₂) (r₃ * q₃) := by
            unfold QuadTriple.Basic.archimedesFunction
            ring1
      _ = QuadTriple.Basic.archimedesFunction (r₂ * q₃) (r₁ * q₃) (r₃ * q₃) := by
            rw [firstSpreadLaw, secondSpreadLaw]
      _ = q₃ ^ 2 * QuadTriple.Basic.archimedesFunction r₂ r₁ r₃ := by
            unfold QuadTriple.Basic.archimedesFunction
            ring1
  have spreadArchimedes :
      QuadTriple.Basic.archimedesFunction r₂ r₁ r₃ = 4 * r₁ * r₂ * r₃ := by
    unfold TripleSpread.SpreadTriple TripleSpread.tripleSpreadFunction at spreadTriple
    unfold QuadTriple.Basic.archimedesFunction
    calc
      (r₂ + r₁ + r₃) ^ 2 -
          2 * (r₂ ^ 2 + r₁ ^ 2 + r₃ ^ 2) =
        ((r₁ + r₂ + r₃) ^ 2 -
          2 * (r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2) -
          4 * r₁ * r₂ * r₃) +
            4 * r₁ * r₂ * r₃ := by ring1
      _ = 4 * r₁ * r₂ * r₃ := by rw [spreadTriple]; ring1
  have r₃Archimedes :
      r₃ * QuadTriple.Basic.archimedesFunction R₁ R₂ q₃ =
        4 * q₃ ^ 2 * r₁ * r₂ := by
    apply ExplicitField.eq_of_mul_eq_mul_right r₃Nonzero
    calc
      (r₃ * QuadTriple.Basic.archimedesFunction R₁ R₂ q₃) * r₃ =
          r₃ ^ 2 * QuadTriple.Basic.archimedesFunction R₁ R₂ q₃ := by ring1
      _ = q₃ ^ 2 * QuadTriple.Basic.archimedesFunction r₂ r₁ r₃ := scaledArchimedes
      _ = (4 * q₃ ^ 2 * r₁ * r₂) * r₃ := by
        rw [spreadArchimedes]
        ring1
  have q₃SquareNonzero : q₃ ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      ExplicitField.mul_ne_zero q₃Nonzero q₃Nonzero
  have scaledCenteredEquation :
      q₃ ^ 2 * centeredRoot ^ 2 =
        q₃ ^ 2 *
          (4 * r₃ * r₁ * r₂ * QuadTriple.Basic.archimedesFunction q₁ q₂ q₃) := by
    calc
      q₃ ^ 2 * centeredRoot ^ 2 =
          (q₃ * centeredRoot) ^ 2 := by ring1
      _ = (r₃ * fourPointNumerator) ^ 2 := by rw [numeratorCenterRelation]
      _ = r₃ ^ 2 * fourPointNumerator ^ 2 := by ring1
      _ = r₃ ^ 2 *
          (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ *
            QuadTriple.Basic.archimedesFunction R₁ R₂ q₃) := by rw [numeratorEquation]
      _ = r₃ * QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ *
          (r₃ * QuadTriple.Basic.archimedesFunction R₁ R₂ q₃) := by ring1
      _ = q₃ ^ 2 *
          (4 * r₃ * r₁ * r₂ *
            QuadTriple.Basic.archimedesFunction q₁ q₂ q₃) := by
              rw [r₃Archimedes]
              ring1
  apply ExplicitField.eq_of_mul_eq_mul_right q₃SquareNonzero
  calc
    centeredRoot ^ 2 * q₃ ^ 2 =
        q₃ ^ 2 * centeredRoot ^ 2 := by ring1
    _ = q₃ ^ 2 *
        (4 * r₃ * r₁ * r₂ *
          QuadTriple.Basic.archimedesFunction q₁ q₂ q₃) := scaledCenteredEquation
    _ = (4 * r₃ * r₁ * r₂ *
          QuadTriple.Basic.archimedesFunction q₁ q₂ q₃) * q₃ ^ 2 := by ring1

/-- The cleared Cross-law numerator `4 * first * third - (first + third - opposite)²`. -/
@[expose] def resectionCrossSpreadNumerator
    (first third opposite : K) : K :=
  4 * first * third - (first + third - opposite) ^ 2

/-- The remainder of Problem 24: the two Cross-law numerators and final Spread-law equations determining `P₁,P₂`. -/
theorem problem_24_finish
    (q₁ q₂ r₁ r₂ R₁ R₂ R₃ v₁ v₂ P₁ P₂ : K)
    (firstCross :
      v₁ * (4 * R₁ * R₃) =
        resectionCrossSpreadNumerator R₁ R₃ q₂)
    (secondCross :
      v₂ * (4 * R₂ * R₃) =
        resectionCrossSpreadNumerator R₂ R₃ q₁)
    (firstSpreadLaw : r₂ * P₁ = v₁ * R₁)
    (secondSpreadLaw : r₁ * P₂ = v₂ * R₂) :
    v₁ * (4 * R₁ * R₃) =
        resectionCrossSpreadNumerator R₁ R₃ q₂ ∧
      v₂ * (4 * R₂ * R₃) =
        resectionCrossSpreadNumerator R₂ R₃ q₁ ∧
      r₂ * P₁ = v₁ * R₁ ∧
      r₁ * P₂ = v₂ * R₂ :=
  ⟨firstCross, secondCross, firstSpreadLaw, secondSpreadLaw⟩
end
end Purelib.Geometry.Resection.Spread.Cleared

end

end
