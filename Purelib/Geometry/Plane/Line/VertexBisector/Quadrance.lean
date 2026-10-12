module

import Purelib.Algebra.Field.Ratio
import Purelib.Geometry.Plane.Line.VertexBisector.Classification
import Purelib.Geometry.Plane.Line.VertexBisector.Existence
import Purelib.Algebra.Field.Cancellation
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Quadrance
public import Purelib.Geometry.Plane.Line.VertexBisector.Construction
import Purelib.Geometry.Plane.Point.Basic

import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Geometry.Plane.Line.VertexBisector.Basic
import Purelib.Tactic.Ring
import Purelib.Geometry.Plane.Line.Relations

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

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

namespace Purelib.Geometry.Plane.Line.VertexBisector.Quadrance

variable {K : Type*} [ExplicitField K]

/-- Theorem 46 (Equal quadrance to two lines), in its constructive factorized form: the equal-quadrance locus is exactly
the union of the two explicit bisector lines. -/
theorem equal_pointLineQuadrance_iff_on_vertexBisector
  [DecidableEq K]
    (first second : Plane.Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (rootEquation : root ^ 2 = Line.Basic.lineNorm first * Line.Basic.lineNorm second)
    (point : Plane.Point K) :
    Quadrance.pointLineQuadrance point first firstNonNull =
        Quadrance.pointLineQuadrance point second secondNonNull ↔
      (Construction.positiveVertexBisector first second root firstNonNull notParallel).Contains point ∨
      (Construction.negativeVertexBisector first second root firstNonNull notParallel).Contains point := by
  let firstValue := first.a * point.x + first.b * point.y + first.c
  let secondValue := second.a * point.x + second.b * point.y + second.c
  have firstNormNonzero : Line.Basic.lineNorm first ≠ 0 := firstNonNull
  have secondNormNonzero : Line.Basic.lineNorm second ≠ 0 := secondNonNull
  have onPositiveIff :
      (Construction.positiveVertexBisector first second root firstNonNull notParallel).Contains point ↔
        root * firstValue + Line.Basic.lineNorm first * secondValue = 0 := by
    constructor
    · intro contains
      unfold Purelib.Geometry.Plane.Line.Contains Construction.positiveVertexBisector at contains
      calc
        root * firstValue + Line.Basic.lineNorm first * secondValue =
          (root * first.a + Line.Basic.lineNorm first * second.a) * point.x +
            (root * first.b + Line.Basic.lineNorm first * second.b) * point.y +
            (root * first.c + Line.Basic.lineNorm first * second.c) := by
              unfold firstValue secondValue
              ring1
        _ = 0 := contains
    · intro factorZero
      unfold Purelib.Geometry.Plane.Line.Contains Construction.positiveVertexBisector
      calc
        (root * first.a + Line.Basic.lineNorm first * second.a) * point.x +
            (root * first.b + Line.Basic.lineNorm first * second.b) * point.y +
            (root * first.c + Line.Basic.lineNorm first * second.c) =
          root * firstValue + Line.Basic.lineNorm first * secondValue := by
            unfold firstValue secondValue
            ring1
        _ = 0 := factorZero
  have onNegativeIff :
      (Construction.negativeVertexBisector first second root firstNonNull notParallel).Contains point ↔
        root * firstValue - Line.Basic.lineNorm first * secondValue = 0 := by
    constructor
    · intro contains
      unfold Purelib.Geometry.Plane.Line.Contains Construction.negativeVertexBisector at contains
      calc
        root * firstValue - Line.Basic.lineNorm first * secondValue =
          (root * first.a - Line.Basic.lineNorm first * second.a) * point.x +
            (root * first.b - Line.Basic.lineNorm first * second.b) * point.y +
            (root * first.c - Line.Basic.lineNorm first * second.c) := by
              unfold firstValue secondValue
              ring1
        _ = 0 := contains
    · intro factorZero
      unfold Purelib.Geometry.Plane.Line.Contains Construction.negativeVertexBisector
      calc
        (root * first.a - Line.Basic.lineNorm first * second.a) * point.x +
            (root * first.b - Line.Basic.lineNorm first * second.b) * point.y +
            (root * first.c - Line.Basic.lineNorm first * second.c) =
          root * firstValue - Line.Basic.lineNorm first * secondValue := by
            unfold firstValue secondValue
            ring1
        _ = 0 := factorZero
  rw [Quadrance.pointLineQuadrance_formula, Quadrance.pointLineQuadrance_formula]
  constructor
  · intro equalRatios
    have crossProduct := (fun {K : Type _} [ExplicitField K] [DecidableEq K] {leftNumerator
      rightNumerator leftDenominator rightDenominator : K} (leftNonzero : leftDenominator ≠ 0) (rightNonzero :
      rightDenominator ≠ 0) (ratiosEqual : leftNumerator / leftDenominator = rightNumerator / rightDenominator) =>
      (Purelib.Algebra.Field.Ratio.cross_product_of_ratio_eq (K := K) (leftNumerator := leftNumerator) (rightNumerator
      := rightNumerator) (leftDenominator := leftDenominator) (rightDenominator := rightDenominator) leftNonzero
      rightNonzero ratiosEqual : leftNumerator * rightDenominator = rightNumerator * leftDenominator))
      firstNormNonzero secondNormNonzero equalRatios
    change firstValue ^ 2 * Line.Basic.lineNorm second =
      secondValue ^ 2 * Line.Basic.lineNorm first at crossProduct
    have factorProduct :
        (root * firstValue - Line.Basic.lineNorm first * secondValue) *
          (root * firstValue + Line.Basic.lineNorm first * secondValue) = 0 := by
      calc
        (root * firstValue - Line.Basic.lineNorm first * secondValue) *
            (root * firstValue + Line.Basic.lineNorm first * secondValue) =
          root ^ 2 * firstValue ^ 2 -
            Line.Basic.lineNorm first ^ 2 * secondValue ^ 2 := by ring1
        _ =
          Line.Basic.lineNorm first *
            (firstValue ^ 2 * Line.Basic.lineNorm second -
              secondValue ^ 2 * Line.Basic.lineNorm first) := by
          rw [rootEquation]
          ring1
        _ = 0 := by rw [crossProduct]; ring1
    by_cases negativeFactorZero :
        root * firstValue - Line.Basic.lineNorm first * secondValue = 0
    · right
      exact onNegativeIff.2 negativeFactorZero
    · left
      have positiveFactorZero :
          root * firstValue + Line.Basic.lineNorm first * secondValue = 0 := by
        by_cases positiveZero :
            root * firstValue + Line.Basic.lineNorm first * secondValue = 0
        · exact positiveZero
        · exact False.elim
            ((ExplicitField.mul_ne_zero negativeFactorZero positiveZero)
              factorProduct)
      exact onPositiveIff.2 positiveFactorZero
  · intro onBisector
    apply (fun {K : Type _} [ExplicitField K] [DecidableEq K] {leftNumerator rightNumerator
      leftDenominator rightDenominator : K} (leftNonzero : leftDenominator ≠ 0) (rightNonzero : rightDenominator ≠ 0)
      (crossProduct : leftNumerator * rightDenominator = rightNumerator * leftDenominator) =>
      (Purelib.Algebra.Field.Ratio.ratio_eq_of_cross_product (K := K) (leftNumerator := leftNumerator) (rightNumerator
      := rightNumerator) (leftDenominator := leftDenominator) (rightDenominator := rightDenominator) leftNonzero
      rightNonzero crossProduct : leftNumerator / leftDenominator = rightNumerator / rightDenominator)) firstNormNonzero
      secondNormNonzero
    change firstValue ^ 2 * Line.Basic.lineNorm second =
      secondValue ^ 2 * Line.Basic.lineNorm first
    have factorProduct :
        (root * firstValue - Line.Basic.lineNorm first * secondValue) *
          (root * firstValue + Line.Basic.lineNorm first * secondValue) = 0 := by
      rcases onBisector with onPositive | onNegative
      · have positiveFactorZero :
            root * firstValue + Line.Basic.lineNorm first * secondValue = 0 := by
          exact onPositiveIff.1 onPositive
        rw [positiveFactorZero]
        ring1
      · have negativeFactorZero :
            root * firstValue - Line.Basic.lineNorm first * secondValue = 0 := by
          exact onNegativeIff.1 onNegative
        rw [negativeFactorZero]
        ring1
    have scaledDifference : Line.Basic.lineNorm first *
        (firstValue ^ 2 * Line.Basic.lineNorm second -
          secondValue ^ 2 * Line.Basic.lineNorm first) = 0 := by
      calc
        Line.Basic.lineNorm first *
            (firstValue ^ 2 * Line.Basic.lineNorm second -
              secondValue ^ 2 * Line.Basic.lineNorm first) =
          root ^ 2 * firstValue ^ 2 -
            Line.Basic.lineNorm first ^ 2 * secondValue ^ 2 := by
              rw [rootEquation]
              ring1
        _ =
          (root * firstValue - Line.Basic.lineNorm first * secondValue) *
            (root * firstValue + Line.Basic.lineNorm first * secondValue) := by
              ring1
        _ = 0 := factorProduct
    have differenceZero :=
      ExplicitField.eq_zero_of_mul_eq_zero_left firstNormNonzero scaledDifference
    calc
      firstValue ^ 2 * Line.Basic.lineNorm second =
          (firstValue ^ 2 * Line.Basic.lineNorm second -
            secondValue ^ 2 * Line.Basic.lineNorm first) +
            secondValue ^ 2 * Line.Basic.lineNorm first := by ring1
      _ = secondValue ^ 2 * Line.Basic.lineNorm first := by rw [differenceZero]; ring1

end Purelib.Geometry.Plane.Line.VertexBisector.Quadrance

end

section
section
@[expose] public section

/-!
# Divine Proportions, §12.5: incenters

The triangle is represented by its three non-null, pairwise nonparallel side
lines.  A chosen bisector at each of the first two vertices is input data,
matching the constructive existence condition from Theorem 45.  Reflection
shows that those bisectors cannot be parallel.  Their intersection has equal
quadrance to all three side lines, and explicit square witnesses then select a
third vertex bisector through the same point.
-/

namespace Purelib.Geometry.Plane.Line.VertexBisector.Quadrance

variable {K : Type*} [ExplicitField K]

/-- Every point on a displayed vertex bisector has equal quadrance to the two vertex lines. -/
theorem
  equal_pointLineQuadrance_of_isVertexBisector_contains
    [Nontrivial K] [DecidableEq K]
    (first second bisector : Plane.Line K)
    (firstNonNull : ¬ first.IsNull)
    (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (isBisector : VertexBisector.Basic.IsVertexBisector first second bisector
      firstNonNull secondNonNull notParallel)
    (point : Plane.Point K) (onBisector : bisector.Contains point) :
    Quadrance.pointLineQuadrance point first firstNonNull =
      Quadrance.pointLineQuadrance point second secondNonNull := by
  rcases Existence.normProduct_isNonzeroSquare_of_isVertexBisector
      first second bisector firstNonNull secondNonNull notParallel
      isBisector with ⟨root, _rootNonzero, rootEquation⟩
  have rootEquationReversed :
      root ^ 2 = Line.Basic.lineNorm first * Line.Basic.lineNorm second := rootEquation.symm
  rcases Classification.vertex_bisector_classification first second root firstNonNull
      secondNonNull notParallel rootEquationReversed bisector isBisector with
    positiveEquivalent | negativeEquivalent
  · apply (equal_pointLineQuadrance_iff_on_vertexBisector first second root
      firstNonNull secondNonNull notParallel rootEquationReversed point).2
    left
    exact Relations.line_contains_of_equivalent positiveEquivalent point onBisector
  · apply (equal_pointLineQuadrance_iff_on_vertexBisector first second root
      firstNonNull secondNonNull notParallel rootEquationReversed point).2
    right
    exact Relations.line_contains_of_equivalent negativeEquivalent point onBisector
end Purelib.Geometry.Plane.Line.VertexBisector.Quadrance

end

end

