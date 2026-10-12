module

import Purelib.Algebra.Field.Ratio

import Purelib.Data.Rat.Fraction.Order.Cast
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Squares
import Purelib.Curves.Plane.Conic.Center
public import Purelib.Geometry.Conics.Axis
public import Purelib.Geometry.Conics.Grammola.Basic
import Purelib.Geometry.Conics.Grammola.Center
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Intersection
import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Spread.Squares
import Purelib.Geometry.Plane.Line.VertexBisector.Basic
import Purelib.Geometry.Plane.Line.VertexBisector.Classification
public import Purelib.Geometry.Plane.Line.VertexBisector.Construction
import Purelib.Geometry.Plane.Line.VertexBisector.Existence
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Reflection.Line.Evaluation
import Purelib.Geometry.Plane.Reflection.Point
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

open Purelib.Curves.Plane (Conic)

open Purelib.Geometry

open Purelib.Geometry.Conics.Axis

open Purelib.Geometry.Conics.Grammola

open Purelib.Geometry.Conics.Grammola

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Spread

open Purelib.Geometry.Plane.Line.VertexBisector

open Purelib.Geometry.Plane.Reflection.Line

open Purelib.Geometry.Plane.Reflection.Point

section
@[expose] public section

/-!
# Divine Proportions, Exercise 15.18

The two axes of a grammola are constructed from an explicit square witness
for the product of its diagonal norms.  Reflection in either normalized
vertex bisector swaps the two weighted squared line values, so it preserves
the grammola equation.  Conversely, two finite reflection probes show that
every axis satisfies the equal-spread bisector equation.
-/

namespace Purelib.Geometry

namespace Conics.Grammola.Axis

variable {K : Type*} [Algebra.Field.ExplicitField K]

/-- The positive normalized vertex bisector is an axis of the grammola. -/
theorem positiveVertexBisector_isAxis [DecidableEq K]
    (firstDiagonal secondDiagonal : Plane.Line K) (associatedQuadrance root : K)
    (presentation :
      Grammola.Presentation firstDiagonal secondDiagonal associatedQuadrance)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation :
      root ^ 2 = Line.Basic.lineNorm firstDiagonal * Line.Basic.lineNorm secondDiagonal) :
    let axis := Construction.positiveVertexBisector firstDiagonal secondDiagonal root
      presentation.firstNonNull presentation.notParallel
    (Grammola.conic firstDiagonal secondDiagonal presentation.firstNonNull
      presentation.secondNonNull associatedQuadrance twoNonzero).IsAxis axis := by
  dsimp only
  let axis := Construction.positiveVertexBisector firstDiagonal secondDiagonal root
    presentation.firstNonNull presentation.notParallel
  let axisNonNull := Construction.positiveVertexBisector_nonNull firstDiagonal
    secondDiagonal root presentation.firstNonNull presentation.secondNonNull
    presentation.notParallel twoNonzero rootEquation
  refine ⟨axisNonNull, ?_⟩
  intro point
  have rootNonzero := (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] (firstDiagonal secondDiagonal :
    Plane.Line K) (root : K) (firstNonNull : ¬ firstDiagonal.IsNull) (secondNonNull : ¬
    secondDiagonal.IsNull) (rootEquation : root ^ 2 = Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal *
    Purelib.Geometry.Plane.Line.Basic.lineNorm secondDiagonal) =>
    (Purelib.Geometry.Plane.Line.VertexBisector.Construction.root_ne_zero firstDiagonal secondDiagonal root firstNonNull
    secondNonNull rootEquation : root ≠ 0)) firstDiagonal
    secondDiagonal root
    presentation.firstNonNull presentation.secondNonNull rootEquation
  have firstSwap := Purelib.Geometry.Plane.Line.VertexBisector.Construction.positive_reflection_swaps_first
    firstDiagonal
    secondDiagonal root presentation.firstNonNull presentation.secondNonNull
    presentation.notParallel twoNonzero rootEquation point
  have secondSwap := Purelib.Geometry.Plane.Line.VertexBisector.Construction.positive_reflection_swaps_second
    firstDiagonal
    secondDiagonal root presentation.firstNonNull presentation.secondNonNull
    presentation.notParallel twoNonzero rootEquation point
  have squares := Purelib.Algebra.Field.Squares.weightedSquares_preserved
    (Line.Basic.lineNorm firstDiagonal) (Line.Basic.lineNorm secondDiagonal) root
    (Line.Basic.lineValue firstDiagonal point) (Line.Basic.lineValue secondDiagonal point)
    (Line.Basic.lineValue firstDiagonal (Reflection.Point.reflectPoint axis axisNonNull point))
    (Line.Basic.lineValue secondDiagonal (Reflection.Point.reflectPoint axis axisNonNull point))
    presentation.firstNonNull rootNonzero rootEquation firstSwap secondSwap
  rw [Grammola.conic_evaluate, Grammola.conic_evaluate]
  unfold Grammola.clearedEvaluate
  rw [squares]

/-- The negative normalized vertex bisector is the second grammola axis. -/
theorem negativeVertexBisector_isAxis [DecidableEq K]
    (firstDiagonal secondDiagonal : Plane.Line K) (associatedQuadrance root : K)
    (presentation :
      Grammola.Presentation firstDiagonal secondDiagonal associatedQuadrance)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation :
      root ^ 2 = Line.Basic.lineNorm firstDiagonal * Line.Basic.lineNorm secondDiagonal) :
    let axis := Construction.negativeVertexBisector firstDiagonal secondDiagonal root
      presentation.firstNonNull presentation.notParallel
    (Grammola.conic firstDiagonal secondDiagonal presentation.firstNonNull
      presentation.secondNonNull associatedQuadrance twoNonzero).IsAxis axis := by
  dsimp only
  let axis := Construction.negativeVertexBisector firstDiagonal secondDiagonal root
    presentation.firstNonNull presentation.notParallel
  let axisNonNull := Construction.negativeVertexBisector_nonNull firstDiagonal
    secondDiagonal root presentation.firstNonNull presentation.secondNonNull
    presentation.notParallel twoNonzero rootEquation
  refine ⟨axisNonNull, ?_⟩
  intro point
  have rootNonzero := (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] (firstDiagonal secondDiagonal :
    Plane.Line K) (root : K) (firstNonNull : ¬ firstDiagonal.IsNull) (secondNonNull : ¬
    secondDiagonal.IsNull) (rootEquation : root ^ 2 = Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal *
    Purelib.Geometry.Plane.Line.Basic.lineNorm secondDiagonal) =>
    (Purelib.Geometry.Plane.Line.VertexBisector.Construction.root_ne_zero firstDiagonal secondDiagonal root firstNonNull
    secondNonNull rootEquation : root ≠ 0)) firstDiagonal
    secondDiagonal root
    presentation.firstNonNull presentation.secondNonNull rootEquation
  have firstSwap := Purelib.Geometry.Plane.Line.VertexBisector.Construction.negative_reflection_swaps_first
    firstDiagonal
    secondDiagonal root presentation.firstNonNull presentation.secondNonNull
    presentation.notParallel twoNonzero rootEquation point
  have secondSwapUnsigned :=
    Purelib.Geometry.Plane.Line.VertexBisector.Construction.negative_reflection_swaps_second firstDiagonal
    secondDiagonal root presentation.firstNonNull presentation.secondNonNull
    presentation.notParallel twoNonzero rootEquation point
  have firstSwapSigned :
      root * Line.Basic.lineValue firstDiagonal (Reflection.Point.reflectPoint axis axisNonNull point) =
        -Line.Basic.lineNorm firstDiagonal * (-Line.Basic.lineValue secondDiagonal point) := by
    rw [firstSwap]
    ring1
  have secondSwapSigned :
      Line.Basic.lineNorm firstDiagonal *
          Line.Basic.lineValue secondDiagonal (Reflection.Point.reflectPoint axis axisNonNull point) =
        -root * (-Line.Basic.lineValue firstDiagonal point) := by
    rw [secondSwapUnsigned]
    ring1
  have squares := Purelib.Algebra.Field.Squares.weightedSquares_preserved
    (Line.Basic.lineNorm firstDiagonal) (Line.Basic.lineNorm secondDiagonal) root
    (-Line.Basic.lineValue firstDiagonal point) (-Line.Basic.lineValue secondDiagonal point)
    (Line.Basic.lineValue firstDiagonal (Reflection.Point.reflectPoint axis axisNonNull point))
    (Line.Basic.lineValue secondDiagonal (Reflection.Point.reflectPoint axis axisNonNull point))
    presentation.firstNonNull rootNonzero rootEquation firstSwapSigned
    secondSwapSigned
  rw [Grammola.conic_evaluate, Grammola.conic_evaluate]
  unfold Grammola.clearedEvaluate
  calc
    Line.Basic.lineNorm secondDiagonal *
          Line.Basic.lineValue firstDiagonal (Reflection.Point.reflectPoint axis axisNonNull point) ^ 2 +
        Line.Basic.lineNorm firstDiagonal *
          Line.Basic.lineValue secondDiagonal (Reflection.Point.reflectPoint axis axisNonNull point) ^ 2 -
        associatedQuadrance * Line.Basic.lineNorm firstDiagonal *
          Line.Basic.lineNorm secondDiagonal =
      Line.Basic.lineNorm secondDiagonal * (-Line.Basic.lineValue firstDiagonal point) ^ 2 +
        Line.Basic.lineNorm firstDiagonal * (-Line.Basic.lineValue secondDiagonal point) ^ 2 -
        associatedQuadrance * Line.Basic.lineNorm firstDiagonal *
          Line.Basic.lineNorm secondDiagonal := by rw [squares]
    _ = Line.Basic.lineNorm secondDiagonal * Line.Basic.lineValue firstDiagonal point ^ 2 +
        Line.Basic.lineNorm firstDiagonal * Line.Basic.lineValue secondDiagonal point ^ 2 -
        associatedQuadrance * Line.Basic.lineNorm firstDiagonal *
          Line.Basic.lineNorm secondDiagonal := by ring1

end Conics.Grammola.Axis
end Purelib.Geometry

section
variable {K : Type*} [Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Conics.Grammola

/-- The grammola axis cross form factors through the diagonal dot product.

Its remaining factor is the symmetric determinant/dot expression for the two diagonals and the proposed mirror. -/
private theorem axisCrossForm_conic_factor
  [DecidableEq K]
    (firstDiagonal secondDiagonal axis : Plane.Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (twoNonzero : (2 : K) ≠ 0) :
    Purelib.Geometry.Conics.Axis.axisCrossForm
          (Grammola.conic firstDiagonal secondDiagonal firstNonNull secondNonNull
            associatedQuadrance twoNonzero) axis =
      2 * Purelib.Geometry.Plane.Line.Basic.lineDot firstDiagonal secondDiagonal *
        Purelib.Geometry.Plane.Line.VertexBisector.Basic.bisectorFactor firstDiagonal secondDiagonal axis :=
          by
  unfold Purelib.Geometry.Conics.Axis.axisCrossForm Purelib.Geometry.Plane.Line.Basic.lineDot
    Purelib.Geometry.Plane.Line.VertexBisector.Basic.bisectorFactor Grammola.conic Grammola.conicD
    Grammola.conicE Grammola.conicF
    Line.Basic.lineNorm
  ring1
end Purelib.Geometry.Conics.Grammola
end

namespace Purelib.Geometry

namespace Conics.Grammola.Axis

variable {K : Type*} [Algebra.Field.ExplicitField K]

/-- Every equation-preserving mirror of a valid grammola is a vertex bisector of its two diagonal lines. -/
theorem axis_isVertexBisector [DecidableEq K]
    (firstDiagonal secondDiagonal axis : Plane.Line K)
    (associatedQuadrance : K)
    (presentation :
      Grammola.Presentation firstDiagonal secondDiagonal associatedQuadrance)
    (twoNonzero : (2 : K) ≠ 0)
    (isAxis :
      (Grammola.conic firstDiagonal secondDiagonal presentation.firstNonNull
        presentation.secondNonNull associatedQuadrance twoNonzero).IsAxis
          axis) :
    VertexBisector.Basic.IsVertexBisector firstDiagonal secondDiagonal axis
      presentation.firstNonNull presentation.secondNonNull
      presentation.notParallel := by
  let displayedConic := Grammola.conic firstDiagonal secondDiagonal
    presentation.firstNonNull presentation.secondNonNull associatedQuadrance
    twoNonzero
  let center := Intersection.lineIntersection firstDiagonal secondDiagonal
    presentation.notParallel
  rcases isAxis with ⟨axisNonNull, equationInvariant⟩
  have centerIsCenter : displayedConic.IsCenter center := by
    unfold displayedConic center
    exact Center.exercise_15_15 firstDiagonal secondDiagonal associatedQuadrance
      presentation twoNonzero
  have discriminantNonzero : displayedConic.centerDiscriminant ≠ 0 := by
    unfold displayedConic
    exact Center.conic_centerDiscriminant_nonzero firstDiagonal secondDiagonal
      associatedQuadrance presentation twoNonzero
  have reflectedCenterIsCenter :
      displayedConic.IsCenter (Reflection.Point.reflectPoint axis axisNonNull center) :=
    Purelib.Geometry.Conics.Axis.reflected_center_isCenter displayedConic axis axisNonNull
      equationInvariant center centerIsCenter twoNonzero
  have reflectedCenterFixed :
      Reflection.Point.reflectPoint axis axisNonNull center = center := by
    have reflectedFormula := Conic.center_eq_centerPoint displayedConic
      (Reflection.Point.reflectPoint axis axisNonNull center) discriminantNonzero
      reflectedCenterIsCenter
    have centerFormula := Conic.center_eq_centerPoint displayedConic center
      discriminantNonzero centerIsCenter
    exact reflectedFormula.trans centerFormula.symm
  have centerOnAxis : axis.Contains center :=
    Purelib.Geometry.Plane.Reflection.Point.contains_of_reflectPoint_fixed axis axisNonNull twoNonzero center
      reflectedCenterFixed
  have crossFormZero : Purelib.Geometry.Conics.Axis.axisCrossForm displayedConic axis = 0 :=
    Purelib.Geometry.Conics.Axis.axisCrossForm_eq_zero_of_axis displayedConic axis axisNonNull
      equationInvariant center centerIsCenter centerOnAxis twoNonzero
  have dotNonzero : Purelib.Geometry.Plane.Line.Basic.lineDot firstDiagonal secondDiagonal ≠ 0 := by
    exact presentation.notPerpendicular
  have factorNonzero : 2 * Purelib.Geometry.Plane.Line.Basic.lineDot firstDiagonal secondDiagonal ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero twoNonzero dotNonzero
  have factorZero : Purelib.Geometry.Plane.Line.VertexBisector.Basic.bisectorFactor firstDiagonal
    secondDiagonal axis = 0 := by
    apply Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left factorNonzero
    calc
      (2 * Purelib.Geometry.Plane.Line.Basic.lineDot firstDiagonal secondDiagonal) *
          Purelib.Geometry.Plane.Line.VertexBisector.Basic.bisectorFactor firstDiagonal secondDiagonal axis =
        Purelib.Geometry.Conics.Axis.axisCrossForm displayedConic axis := by
          unfold displayedConic
          rw [axisCrossForm_conic_factor]
      _ = 0 := by rw [crossFormZero]
  have balance :
      Line.Basic.lineNorm secondDiagonal *
          (firstDiagonal.a * axis.b - axis.a * firstDiagonal.b) ^ 2 =
        Line.Basic.lineNorm firstDiagonal *
          (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2 := by
    have differenceZero :
        Line.Basic.lineNorm secondDiagonal *
              (firstDiagonal.a * axis.b - axis.a * firstDiagonal.b) ^ 2 -
            Line.Basic.lineNorm firstDiagonal *
              (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2 =
          0 := by
      calc
        Line.Basic.lineNorm secondDiagonal *
              (firstDiagonal.a * axis.b - axis.a * firstDiagonal.b) ^ 2 -
            Line.Basic.lineNorm firstDiagonal *
              (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2 =
          (firstDiagonal.a * secondDiagonal.b -
              secondDiagonal.a * firstDiagonal.b) *
            Purelib.Geometry.Plane.Line.VertexBisector.Basic.bisectorFactor firstDiagonal secondDiagonal axis
              :=
              Purelib.Geometry.Plane.Line.VertexBisector.Basic.bisector_balance_factor firstDiagonal
                secondDiagonal axis
        _ = 0 := by rw [factorZero]; ring1
    calc
      Line.Basic.lineNorm secondDiagonal *
          (firstDiagonal.a * axis.b - axis.a * firstDiagonal.b) ^ 2 =
        (Line.Basic.lineNorm secondDiagonal *
              (firstDiagonal.a * axis.b - axis.a * firstDiagonal.b) ^ 2 -
            Line.Basic.lineNorm firstDiagonal *
              (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2) +
          Line.Basic.lineNorm firstDiagonal *
            (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2 := by
              ring1
      _ = Line.Basic.lineNorm firstDiagonal *
          (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2 := by
            rw [differenceZero]
            ring1
  have firstDenominatorNonzero :
      Line.Basic.lineNorm firstDiagonal * Line.Basic.lineNorm axis ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero presentation.firstNonNull axisNonNull
  have secondDenominatorNonzero :
      Line.Basic.lineNorm secondDiagonal * Line.Basic.lineNorm axis ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero presentation.secondNonNull axisNonNull
  refine ⟨axisNonNull, centerOnAxis, ?_⟩
  unfold Spread.spread
  apply (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {leftNumerator rightNumerator leftDenominator
    rightDenominator : K} (leftNonzero : leftDenominator ≠ 0) (rightNonzero : rightDenominator ≠ 0) (crossProduct :
    leftNumerator * rightDenominator = rightNumerator * leftDenominator) =>
    (Purelib.Algebra.Field.Ratio.ratio_eq_of_cross_product (K := K) (leftNumerator := leftNumerator) (rightNumerator :=
    rightNumerator) (leftDenominator := leftDenominator) (rightDenominator := rightDenominator) leftNonzero rightNonzero
    crossProduct : leftNumerator / leftDenominator = rightNumerator / rightDenominator)) firstDenominatorNonzero
    secondDenominatorNonzero
  calc
    (firstDiagonal.a * axis.b - axis.a * firstDiagonal.b) ^ 2 *
        (Line.Basic.lineNorm secondDiagonal * Line.Basic.lineNorm axis) =
      (Line.Basic.lineNorm secondDiagonal *
          (firstDiagonal.a * axis.b - axis.a * firstDiagonal.b) ^ 2) *
        Line.Basic.lineNorm axis := by ring1
    _ = (Line.Basic.lineNorm firstDiagonal *
          (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2) *
        Line.Basic.lineNorm axis := by rw [balance]
    _ = (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2 *
        (Line.Basic.lineNorm firstDiagonal * Line.Basic.lineNorm axis) := by ring1

/-- Exercise 15.18: a grammola has exactly two axes precisely when its diagonal vertex is square. Every axis is,
constructively, a vertex bisector of the two diagonals. -/
theorem exercise_15_18 [DecidableEq K]
    (firstDiagonal secondDiagonal : Plane.Line K) (associatedQuadrance : K)
    (presentation :
      Grammola.Presentation firstDiagonal secondDiagonal associatedQuadrance)
    (twoNonzero : (2 : K) ≠ 0) :
    Purelib.Geometry.Conics.Axis.HasExactlyTwoAxes
        (Grammola.conic firstDiagonal secondDiagonal presentation.firstNonNull
          presentation.secondNonNull associatedQuadrance twoNonzero) ↔
      Squares.IsNonzeroSquare
        (Spread.spread firstDiagonal secondDiagonal presentation.firstNonNull
          presentation.secondNonNull) := by
  constructor
  · rintro ⟨firstAxis, _secondAxis, firstIsAxis, _secondIsAxis,
      _distinct, _exhaustive⟩
    have firstIsBisector := axis_isVertexBisector firstDiagonal
      secondDiagonal firstAxis associatedQuadrance presentation twoNonzero
      firstIsAxis
    exact (Squares.spread_isNonzeroSquare_iff_normProduct_isNonzeroSquare
      firstDiagonal secondDiagonal presentation.firstNonNull
      presentation.secondNonNull presentation.notParallel).2
        (Existence.normProduct_isNonzeroSquare_of_isVertexBisector firstDiagonal
          secondDiagonal firstAxis presentation.firstNonNull
          presentation.secondNonNull presentation.notParallel
          firstIsBisector)
  · intro spreadSquare
    have normProductSquare :=
      (Squares.spread_isNonzeroSquare_iff_normProduct_isNonzeroSquare firstDiagonal
        secondDiagonal presentation.firstNonNull presentation.secondNonNull
        presentation.notParallel).1 spreadSquare
    rcases normProductSquare with ⟨root, _rootNonzero, rootEquationReversed⟩
    have rootEquation :
        root ^ 2 = Line.Basic.lineNorm firstDiagonal * Line.Basic.lineNorm secondDiagonal :=
      rootEquationReversed.symm
    let positive := Construction.positiveVertexBisector firstDiagonal secondDiagonal root
      presentation.firstNonNull presentation.notParallel
    let negative := Construction.negativeVertexBisector firstDiagonal secondDiagonal root
      presentation.firstNonNull presentation.notParallel
    have positiveAxis := positiveVertexBisector_isAxis firstDiagonal
      secondDiagonal associatedQuadrance root presentation twoNonzero
      rootEquation
    have negativeAxis := negativeVertexBisector_isAxis firstDiagonal
      secondDiagonal associatedQuadrance root presentation twoNonzero
      rootEquation
    have axesDistinct := Construction.vertexBisectors_not_equivalent firstDiagonal
      secondDiagonal root presentation.firstNonNull presentation.secondNonNull
      presentation.notParallel twoNonzero rootEquation
    refine ⟨positive, negative, positiveAxis, negativeAxis, axesDistinct, ?_⟩
    intro axis isAxis
    have isBisector := axis_isVertexBisector firstDiagonal secondDiagonal axis
      associatedQuadrance presentation twoNonzero isAxis
    exact Classification.vertex_bisector_classification firstDiagonal secondDiagonal root
      presentation.firstNonNull presentation.secondNonNull
      presentation.notParallel rootEquation axis isBisector

end Conics.Grammola.Axis

end Purelib.Geometry

end
