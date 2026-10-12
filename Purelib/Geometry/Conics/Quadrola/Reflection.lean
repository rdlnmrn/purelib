module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Conics.Quadrola.Basic
public import Purelib.Geometry.Conics.Quadrola.Tangent
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Quadrance
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Conics.Quadrola

open Purelib.Geometry.Conics.Quadrola.Tangent

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Trigonometry

section
public section

/-!
# Divine Proportions, §15.4 and Exercise 19.3: quadrolas

A quadrola is given by one finite Archimedes polynomial in the two focal
quadrances and its associated quadrance.  The apparent quartic terms cancel
to an explicit conic.  Its gradient tangent satisfies the equal-spread
reflection property by a denominator-cleared polynomial identity.
-/

namespace Purelib.Geometry

namespace Conics.Quadrola.Reflection

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Exercise 19.3 (Quadrola reflection). The tangent makes equal spreads with the two focal lines. The three non-null
hypotheses are exactly the conditions required for those spreads to exist over a general field. -/
theorem reflection [DecidableEq K]
    (firstFocus secondFocus point : Plane.Point K) (associatedQuadrance : K)
    (pointFirstDistinct : point ≠ firstFocus)
    (pointSecondDistinct : point ≠ secondFocus)
    (onQuadrola : Quadrola.Contains firstFocus secondFocus associatedQuadrance point)
    (normalNonNull :
      Tangent.tangentNormalX firstFocus secondFocus associatedQuadrance point ^ 2 +
        Tangent.tangentNormalY firstFocus secondFocus associatedQuadrance point ^ 2 ≠
          0)
    (firstFocusLineNonNull :
      ¬ (Incidence.lineThrough point firstFocus pointFirstDistinct).IsNull)
    (secondFocusLineNonNull :
      ¬ (Incidence.lineThrough point secondFocus pointSecondDistinct).IsNull) :
    let tangent := Tangent.tangentLine firstFocus secondFocus associatedQuadrance point
      normalNonNull
    Spread.spread tangent (Incidence.lineThrough point firstFocus pointFirstDistinct)
        (Tangent.tangentLine_nonNull firstFocus secondFocus associatedQuadrance point
          normalNonNull) firstFocusLineNonNull =
      Spread.spread tangent (Incidence.lineThrough point secondFocus pointSecondDistinct)
        (Tangent.tangentLine_nonNull firstFocus secondFocus associatedQuadrance point
          normalNonNull) secondFocusLineNonNull := by
  dsimp only
  let firstQuadrance := Quadrance.quadrance point firstFocus
  let secondQuadrance := Quadrance.quadrance point secondFocus
  let firstCoefficient :=
    Tangent.firstWeight firstQuadrance secondQuadrance associatedQuadrance
  let secondCoefficient :=
    Tangent.secondWeight firstQuadrance secondQuadrance associatedQuadrance
  let firstX := point.x - firstFocus.x
  let firstY := point.y - firstFocus.y
  let secondX := point.x - secondFocus.x
  let secondY := point.y - secondFocus.y
  let mixedProduct := firstX * secondX + firstY * secondY
  let normalX := Tangent.tangentNormalX firstFocus secondFocus associatedQuadrance point
  let normalY := Tangent.tangentNormalY firstFocus secondFocus associatedQuadrance point
  let firstDot := normalX * firstX + normalY * firstY
  let secondDot := normalX * secondX + normalY * secondY
  have firstQuadranceFormula :
      firstQuadrance = firstX ^ 2 + firstY ^ 2 := by
    unfold firstQuadrance firstX firstY Quadrance.quadrance
    ring1
  have secondQuadranceFormula :
      secondQuadrance = secondX ^ 2 + secondY ^ 2 := by
    unfold secondQuadrance secondX secondY Quadrance.quadrance
    ring1
  have firstCoefficientSquare :
      firstCoefficient ^ 2 =
        4 * associatedQuadrance * secondQuadrance := by
    unfold Quadrola.Contains Quadrola.evaluate at onQuadrola
    have differenceZero :
        firstCoefficient ^ 2 -
          4 * associatedQuadrance * secondQuadrance = 0 := by
      calc
        firstCoefficient ^ 2 -
            4 * associatedQuadrance * secondQuadrance =
          -(QuadTriple.Basic.archimedesFunction firstQuadrance secondQuadrance
            associatedQuadrance) := by
          unfold firstCoefficient Tangent.firstWeight QuadTriple.Basic.archimedesFunction
          ring1
        _ = 0 := by rw [onQuadrola]; ring1
    exact Group.eq_of_sub_eq_zero differenceZero
  have secondCoefficientSquare :
      secondCoefficient ^ 2 =
        4 * associatedQuadrance * firstQuadrance := by
    unfold Quadrola.Contains Quadrola.evaluate at onQuadrola
    have differenceZero :
        secondCoefficient ^ 2 -
          4 * associatedQuadrance * firstQuadrance = 0 := by
      calc
        secondCoefficient ^ 2 -
            4 * associatedQuadrance * firstQuadrance =
          -(QuadTriple.Basic.archimedesFunction firstQuadrance secondQuadrance
            associatedQuadrance) := by
          unfold secondCoefficient Tangent.secondWeight QuadTriple.Basic.archimedesFunction
          ring1
        _ = 0 := by rw [onQuadrola]; ring1
    exact Group.eq_of_sub_eq_zero differenceZero
  have normalXFormula :
      normalX = firstCoefficient * firstX + secondCoefficient * secondX := by
    unfold normalX Tangent.tangentNormalX firstCoefficient secondCoefficient
      firstQuadrance secondQuadrance firstX secondX
    rfl
  have normalYFormula :
      normalY = firstCoefficient * firstY + secondCoefficient * secondY := by
    unfold normalY Tangent.tangentNormalY firstCoefficient secondCoefficient
      firstQuadrance secondQuadrance firstY secondY
    rfl
  have firstDotFormula :
      firstDot = firstCoefficient * firstQuadrance +
        secondCoefficient * mixedProduct := by
    unfold firstDot mixedProduct
    rw [normalXFormula, normalYFormula, firstQuadranceFormula]
    ring1
  have secondDotFormula :
      secondDot = firstCoefficient * mixedProduct +
        secondCoefficient * secondQuadrance := by
    unfold secondDot mixedProduct
    rw [normalXFormula, normalYFormula, secondQuadranceFormula]
    ring1
  have dotCrossProduct :
      firstDot ^ 2 * secondQuadrance =
        secondDot ^ 2 * firstQuadrance := by
    rw [firstDotFormula, secondDotFormula]
    calc
      (firstCoefficient * firstQuadrance +
            secondCoefficient * mixedProduct) ^ 2 * secondQuadrance =
        (firstCoefficient * mixedProduct +
            secondCoefficient * secondQuadrance) ^ 2 * firstQuadrance +
          (firstQuadrance * secondQuadrance - mixedProduct ^ 2) *
            (firstCoefficient ^ 2 * firstQuadrance -
              secondCoefficient ^ 2 * secondQuadrance) := by ring1
      _ = (firstCoefficient * mixedProduct +
          secondCoefficient * secondQuadrance) ^ 2 * firstQuadrance := by
        rw [firstCoefficientSquare, secondCoefficientSquare]
        ring1
  let tangent := Tangent.tangentLine firstFocus secondFocus associatedQuadrance point
    normalNonNull
  let firstLine := Incidence.lineThrough point firstFocus pointFirstDistinct
  let secondLine := Incidence.lineThrough point secondFocus pointSecondDistinct
  have firstNumerator :
      (tangent.a * firstLine.b - firstLine.a * tangent.b) ^ 2 =
        firstDot ^ 2 := by
    unfold tangent Tangent.tangentLine firstLine Incidence.lineThrough firstDot normalX normalY
      firstX firstY
    ring1
  have secondNumerator :
      (tangent.a * secondLine.b - secondLine.a * tangent.b) ^ 2 =
        secondDot ^ 2 := by
    unfold tangent Tangent.tangentLine secondLine Incidence.lineThrough secondDot normalX normalY
      secondX secondY
    ring1
  have firstNorm : Line.Basic.lineNorm firstLine = firstQuadrance := by
    unfold firstLine firstQuadrance
    exact Quadrance.lineThrough_norm_eq_quadrance point firstFocus pointFirstDistinct
  have secondNorm : Line.Basic.lineNorm secondLine = secondQuadrance := by
    unfold secondLine secondQuadrance
    exact Quadrance.lineThrough_norm_eq_quadrance point secondFocus pointSecondDistinct
  have tangentNonNull := Tangent.tangentLine_nonNull firstFocus secondFocus
    associatedQuadrance point normalNonNull
  have firstDenominatorNonzero :
      Line.Basic.lineNorm tangent * Line.Basic.lineNorm firstLine ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero tangentNonNull firstFocusLineNonNull
  have secondDenominatorNonzero :
      Line.Basic.lineNorm tangent * Line.Basic.lineNorm secondLine ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero tangentNonNull secondFocusLineNonNull
  have firstDenominatorNonzero' :
      Line.Basic.lineNorm tangent * firstQuadrance ≠ 0 := by
    rw [← firstNorm]
    exact firstDenominatorNonzero
  have secondDenominatorNonzero' :
      Line.Basic.lineNorm tangent * secondQuadrance ≠ 0 := by
    rw [← secondNorm]
    exact secondDenominatorNonzero
  unfold Spread.spread
  rw [firstNumerator, secondNumerator, firstNorm, secondNorm]
  change
    firstDot ^ 2 / (Line.Basic.lineNorm tangent * firstQuadrance) =
      secondDot ^ 2 / (Line.Basic.lineNorm tangent * secondQuadrance)
  apply Ratio.ratio_eq_of_cross_product firstDenominatorNonzero'
    secondDenominatorNonzero'
  calc
    firstDot ^ 2 * (Line.Basic.lineNorm tangent * secondQuadrance) =
        Line.Basic.lineNorm tangent * (firstDot ^ 2 * secondQuadrance) := by ring1
    _ = Line.Basic.lineNorm tangent * (secondDot ^ 2 * firstQuadrance) := by
      rw [dotCrossProduct]
    _ = secondDot ^ 2 * (Line.Basic.lineNorm tangent * firstQuadrance) := by ring1

end Conics.Quadrola.Reflection

end Purelib.Geometry

end

end
