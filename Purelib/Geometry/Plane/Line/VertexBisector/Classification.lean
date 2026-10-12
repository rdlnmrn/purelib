module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Squares
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Intersection
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Spread.Squares
import Purelib.Geometry.Plane.Line.VertexBisector.Basic
public import Purelib.Geometry.Plane.Line.VertexBisector.Construction
import Purelib.Geometry.Plane.Line.VertexBisector.Existence
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Line.Spread

open Purelib.Geometry.Plane.Line.VertexBisector

section
@[expose] public section

/-!
# Divine Proportions, §6.9: vertex bisectors

An explicit witness `r² = ‖l₁‖‖l₂‖` produces the two normalized
bisectors `r l₁ ± ‖l₁‖ l₂`.  This formulation is equivalent to the
book's longer coefficient display, but is symmetric enough that all finite
field cancellations remain visible.
-/

namespace Purelib.Geometry.Plane.Line.VertexBisector.Classification

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Classification clause of Theorem 45: once a displayed square root is supplied, every bisector is one of the two
normalized candidates, up to the book's equality of ordered proportions. -/
theorem vertex_bisector_classification [DecidableEq K]
    (first second : Plane.Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (rootEquation : root ^ 2 = Line.Basic.lineNorm first * Line.Basic.lineNorm second)
    (bisector : Plane.Line K)
    (isBisector : VertexBisector.Basic.IsVertexBisector first second bisector
      firstNonNull secondNonNull notParallel) :
    bisector.Equivalent
        (Construction.positiveVertexBisector first second root firstNonNull notParallel) ∨
      bisector.Equivalent
        (Construction.negativeVertexBisector first second root firstNonNull notParallel) := by
  rcases isBisector with
    ⟨bisectorNonNull, bisectorContainsVertex, equalSpreads⟩
  have normBalance := Purelib.Geometry.Plane.Line.Spread.Squares.equal_spreads_norm_balance first second bisector
    firstNonNull secondNonNull bisectorNonNull equalSpreads
  have factorProduct :
      (root * (first.a * bisector.b - bisector.a * first.b) -
          Line.Basic.lineNorm first *
            (second.a * bisector.b - bisector.a * second.b)) *
        (root * (first.a * bisector.b - bisector.a * first.b) +
          Line.Basic.lineNorm first *
            (second.a * bisector.b - bisector.a * second.b)) = 0 := by
    calc
      (root * (first.a * bisector.b - bisector.a * first.b) -
            Line.Basic.lineNorm first *
              (second.a * bisector.b - bisector.a * second.b)) *
          (root * (first.a * bisector.b - bisector.a * first.b) +
            Line.Basic.lineNorm first *
              (second.a * bisector.b - bisector.a * second.b)) =
        root ^ 2 *
            (first.a * bisector.b - bisector.a * first.b) ^ 2 -
          Line.Basic.lineNorm first ^ 2 *
            (second.a * bisector.b - bisector.a * second.b) ^ 2 := by ring1
      _ =
        Line.Basic.lineNorm first *
          (Line.Basic.lineNorm second *
              (first.a * bisector.b - bisector.a * first.b) ^ 2 -
            Line.Basic.lineNorm first *
              (second.a * bisector.b - bisector.a * second.b) ^ 2) := by
        rw [rootEquation]
        ring1
      _ = 0 := by rw [normBalance]; ring1
  let vertex := Intersection.lineIntersection first second notParallel
  have firstContainsVertex : first.Contains vertex :=
    Intersection.lineIntersection_on_first first second notParallel
  have secondContainsVertex : second.Contains vertex :=
    Intersection.lineIntersection_on_second first second notParallel
  by_cases negativeFactorZero :
      root * (first.a * bisector.b - bisector.a * first.b) -
          Line.Basic.lineNorm first *
            (second.a * bisector.b - bisector.a * second.b) = 0
  · right
    have candidateParallel :
        (Construction.negativeVertexBisector first second root firstNonNull notParallel).Parallel
          bisector := by
      unfold Line.Parallel Construction.negativeVertexBisector
      calc
        (root * first.a - Line.Basic.lineNorm first * second.a) * bisector.b -
            bisector.a *
              (root * first.b - Line.Basic.lineNorm first * second.b) =
          root * (first.a * bisector.b - bisector.a * first.b) -
            Line.Basic.lineNorm first *
              (second.a * bisector.b - bisector.a * second.b) := by ring1
        _ = 0 := negativeFactorZero
    have candidateContainsVertex :
        (Construction.negativeVertexBisector first second root firstNonNull notParallel).Contains
          vertex :=
      Construction.negativeVertexBisector_contains_common_point first second root
        firstNonNull notParallel vertex firstContainsVertex secondContainsVertex
    exact Plane.Line.equivalent_symm
      (Relations.line_equivalent_of_parallel_and_common_point
        (Construction.negativeVertexBisector first second root firstNonNull notParallel)
        bisector vertex candidateParallel candidateContainsVertex
        bisectorContainsVertex)
  · left
    have positiveFactorZero :
        root * (first.a * bisector.b - bisector.a * first.b) +
            Line.Basic.lineNorm first *
              (second.a * bisector.b - bisector.a * second.b) = 0 := by
      by_cases factorZero :
          root * (first.a * bisector.b - bisector.a * first.b) +
              Line.Basic.lineNorm first *
                (second.a * bisector.b - bisector.a * second.b) = 0
      · exact factorZero
      · exact False.elim
          ((Algebra.Field.ExplicitField.mul_ne_zero negativeFactorZero factorZero)
            factorProduct)
    have candidateParallel :
        (Construction.positiveVertexBisector first second root firstNonNull notParallel).Parallel
          bisector := by
      unfold Line.Parallel Construction.positiveVertexBisector
      calc
        (root * first.a + Line.Basic.lineNorm first * second.a) * bisector.b -
            bisector.a *
              (root * first.b + Line.Basic.lineNorm first * second.b) =
          root * (first.a * bisector.b - bisector.a * first.b) +
            Line.Basic.lineNorm first *
              (second.a * bisector.b - bisector.a * second.b) := by ring1
        _ = 0 := positiveFactorZero
    have candidateContainsVertex :
        (Construction.positiveVertexBisector first second root firstNonNull notParallel).Contains
          vertex :=
      Construction.positiveVertexBisector_contains_common_point first second root
        firstNonNull notParallel vertex firstContainsVertex secondContainsVertex
    exact Plane.Line.equivalent_symm
      (Relations.line_equivalent_of_parallel_and_common_point
        (Construction.positiveVertexBisector first second root firstNonNull notParallel)
        bisector vertex candidateParallel candidateContainsVertex
        bisectorContainsVertex)

/-- Theorem 45 (Vertex bisector), complete constructive form. It combines the square criterion with two explicit,
distinct, perpendicular witnesses and proves that every bisector is equivalent to one of them. -/
theorem vertex_bisector [DecidableEq K]
    (first second : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0) :
    ((∃ bisector : Plane.Line K,
        VertexBisector.Basic.IsVertexBisector first second bisector
          firstNonNull secondNonNull notParallel) ↔
      Squares.IsNonzeroSquare
        (Spread.spread first second firstNonNull secondNonNull)) ∧
      ∀ root : K, root ^ 2 = Line.Basic.lineNorm first * Line.Basic.lineNorm second →
        let positive := Construction.positiveVertexBisector first second root
          firstNonNull notParallel
        let negative := Construction.negativeVertexBisector first second root
          firstNonNull notParallel
        VertexBisector.Basic.IsVertexBisector first second positive
            firstNonNull secondNonNull notParallel ∧
          VertexBisector.Basic.IsVertexBisector first second negative
            firstNonNull secondNonNull notParallel ∧
          ¬ positive.Equivalent negative ∧
          positive.Perpendicular negative ∧
          ∀ bisector : Plane.Line K,
            VertexBisector.Basic.IsVertexBisector first second bisector
                firstNonNull secondNonNull notParallel →
              bisector.Equivalent positive ∨ bisector.Equivalent negative := by
  constructor
  · exact Existence.vertex_bisector_exists_iff_spread_isNonzeroSquare first second
      firstNonNull secondNonNull notParallel twoNonzero
  · intro root rootEquation
    dsimp only
    exact ⟨
      Construction.positiveVertexBisector_isVertexBisector first second root firstNonNull
        secondNonNull notParallel twoNonzero rootEquation,
      Construction.negativeVertexBisector_isVertexBisector first second root firstNonNull
        secondNonNull notParallel twoNonzero rootEquation,
      Construction.vertexBisectors_not_equivalent first second root firstNonNull
        secondNonNull notParallel twoNonzero rootEquation,
      Construction.vertexBisectors_perpendicular first second root firstNonNull notParallel
        rootEquation,
      fun bisector isBisector => vertex_bisector_classification first
        second
        root firstNonNull secondNonNull notParallel rootEquation bisector
        isBisector⟩
end Purelib.Geometry.Plane.Line.VertexBisector.Classification

end
