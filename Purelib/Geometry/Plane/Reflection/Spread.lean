module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Plane.Reflection.Line
import Purelib.Geometry.Plane.Reflection.Point
public import Purelib.Polynomial.Recurrence.Spread.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Reflection

open Purelib.Polynomial.Recurrence

section
public section

/-!
# Divine Proportions, Theorem 98: polygon corner triangles

The source construction uses only three successive polygon vertices and the
three finite reflections relating them.  `PolygonTriangleConfiguration`
stores precisely that finite window; no polygon indexed by all integers is
introduced.
-/

namespace Purelib.Geometry.Plane.Reflection.Spread

variable {K : Type*} [ExplicitField K]

/-- Exercise 14.2: at any requested finite index `k`, reflecting `A₀` in the star line `lₖ` gives the polygon vertex
`A₂ₖ`, whose quadrance from `A₀` is `4 Sₖ(s) Q`. The caller supplies the already-computed finite spread value of
`l₀,lₖ`; no infinite point or line sequence is formed. -/
theorem exercise_14_2 [DecidableEq K]
    (index : Nat) (value : K) (center initialPoint : Plane.Point K)
    (centerInitialDistinct : center ≠ initialPoint)
    (initialRadialNonNull :
      ¬ (Incidence.lineThrough center initialPoint centerInitialDistinct).IsNull)
    (mirror : Plane.Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (centerOnMirror : mirror.Contains center)
    (indexedSpread :
      Spread.spread (Incidence.lineThrough center initialPoint centerInitialDistinct) mirror
          initialRadialNonNull mirrorNonNull =
        Spread.Basic.spreadPolynomial index value) :
    Quadrance.quadrance initialPoint (Reflection.Point.reflectPoint mirror mirrorNonNull initialPoint) =
      4 * Spread.Basic.spreadPolynomial index value * Quadrance.quadrance center initialPoint := by
  calc
    Quadrance.quadrance initialPoint (Reflection.Point.reflectPoint mirror mirrorNonNull initialPoint) =
        4 * Spread.spread (Incidence.lineThrough center initialPoint centerInitialDistinct)
          mirror initialRadialNonNull mirrorNonNull *
            Quadrance.quadrance center initialPoint :=
      Reflection.Point.reflectPoint_chord_quadrance_eq_spread center initialPoint
        centerInitialDistinct initialRadialNonNull mirror mirrorNonNull
        centerOnMirror
    _ = 4 * Spread.Basic.spreadPolynomial index value * Quadrance.quadrance center initialPoint := by
      rw [indexedSpread]

end Purelib.Geometry.Plane.Reflection.Spread

end

section
public section

/-!
# Divine Proportions, §7.5: spread reflection

The proof clears the two finite spread denominators and factors the resulting
polynomial.  The two factors say respectively that the original lines are
parallel or that the reflected first line is parallel to the second.  The
common-point and distinctness hypotheses eliminate the former.
-/

namespace Purelib.Geometry.Plane.Reflection.Spread

variable {K : Type*} [ExplicitField K]

section
open _root_.Purelib.Geometry
/-- Factor the cleared difference of two spreads with a common mirror.

The factors are the original direction determinant and the determinant between the reflected first line and the second
line; the identity requires no non-null hypotheses. -/
private theorem
  reflection_spread_factorization
    (mirror first second : Line K) :
    Basic.lineNorm second *
          (first.a * mirror.b - mirror.a * first.b) ^ 2 -
        Basic.lineNorm first *
          (second.a * mirror.b - mirror.a * second.b) ^ 2 =
      -(first.a * second.b - second.a * first.b) *
        (Line.reflectedLineA mirror first * second.b -
          second.a * Line.reflectedLineB mirror first) := by
  unfold Basic.lineNorm Line.reflectedLineA Line.reflectedLineB
  ring1
end

/-- Reflecting a non-null target in a non-null mirror preserves its spread with the mirror. This direct coefficient form
does not need an intersection or a distinctness hypothesis and drives the finite reflection chain in Theorem 58. -/
theorem spread_reflectLine_mirror [DecidableEq K]
    (mirror target : Plane.Line K)
    (mirrorNonNull : ¬ mirror.IsNull)
    (targetNonNull : ¬ target.IsNull) :
    let reflectedNonNull := Line.reflectLine_nonNull mirror target mirrorNonNull
      targetNonNull
    Spread.spread (Line.reflectLine mirror target mirrorNonNull) mirror
        reflectedNonNull mirrorNonNull =
      Spread.spread target mirror targetNonNull mirrorNonNull := by
  dsimp only
  let reflectedNonNull := Line.reflectLine_nonNull mirror target mirrorNonNull
    targetNonNull
  have reflectedDenominatorNonzero :
      Basic.lineNorm (Line.reflectLine mirror target mirrorNonNull) * Basic.lineNorm mirror ≠ 0 :=
    ExplicitField.mul_ne_zero reflectedNonNull mirrorNonNull
  have targetDenominatorNonzero :
      Basic.lineNorm target * Basic.lineNorm mirror ≠ 0 :=
    ExplicitField.mul_ne_zero targetNonNull mirrorNonNull
  unfold Spread.spread
  apply Ratio.ratio_eq_of_cross_product reflectedDenominatorNonzero
    targetDenominatorNonzero
  unfold Line.reflectLine Line.reflectedLineA Line.reflectedLineB Basic.lineNorm
  ring1

/-- Theorem 52 (Spread reflection). `¬ first.Equivalent second` is the quotient-free form of the book's distinct-line
hypothesis. -/
theorem spread_reflection [DecidableEq K]
    (mirror first second : Plane.Line K) (point : Plane.Point K)
    (mirrorNonNull : ¬ mirror.IsNull)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (mirrorContains : mirror.Contains point)
    (firstContains : first.Contains point)
    (secondContains : second.Contains point)
    (distinct : ¬ first.Equivalent second) :
    (Line.reflectLine mirror first mirrorNonNull).Equivalent second ↔
      Spread.spread first mirror firstNonNull mirrorNonNull =
        Spread.spread second mirror secondNonNull mirrorNonNull := by
  have firstDenominatorNonzero :
      Line.Basic.lineNorm first * Line.Basic.lineNorm mirror ≠ 0 :=
    ExplicitField.mul_ne_zero firstNonNull mirrorNonNull
  have secondDenominatorNonzero :
      Line.Basic.lineNorm second * Line.Basic.lineNorm mirror ≠ 0 :=
    ExplicitField.mul_ne_zero secondNonNull mirrorNonNull
  constructor
  · intro reflectedEquivalent
    have reflectedDeterminantZero :
        Line.reflectedLineA mirror first * second.b -
            second.a * Line.reflectedLineB mirror first = 0 := by
      unfold Plane.Line.Equivalent Line.reflectLine at reflectedEquivalent
      calc
        Line.reflectedLineA mirror first * second.b -
            second.a * Line.reflectedLineB mirror first =
          second.a * Line.reflectedLineB mirror first -
            second.a * Line.reflectedLineB mirror first := by
              rw [reflectedEquivalent.1]
        _ = 0 := by ring1
    have balance :
        Line.Basic.lineNorm second *
              (first.a * mirror.b - mirror.a * first.b) ^ 2 =
          Line.Basic.lineNorm first *
              (second.a * mirror.b - mirror.a * second.b) ^ 2 := by
      have differenceZero :
          Line.Basic.lineNorm second *
                (first.a * mirror.b - mirror.a * first.b) ^ 2 -
              Line.Basic.lineNorm first *
                (second.a * mirror.b - mirror.a * second.b) ^ 2 = 0 := by
        calc
          Line.Basic.lineNorm second *
                (first.a * mirror.b - mirror.a * first.b) ^ 2 -
              Line.Basic.lineNorm first *
                (second.a * mirror.b - mirror.a * second.b) ^ 2 =
            -(first.a * second.b - second.a * first.b) *
              (Line.reflectedLineA mirror first * second.b -
                second.a * Line.reflectedLineB mirror first) :=
              reflection_spread_factorization mirror
                first second
          _ = 0 := by rw [reflectedDeterminantZero]; ring1
      exact Group.eq_of_sub_eq_zero differenceZero
    unfold Spread.spread
    apply Ratio.ratio_eq_of_cross_product firstDenominatorNonzero
      secondDenominatorNonzero
    calc
      (first.a * mirror.b - mirror.a * first.b) ^ 2 *
          (Line.Basic.lineNorm second * Line.Basic.lineNorm mirror) =
        (Line.Basic.lineNorm second *
          (first.a * mirror.b - mirror.a * first.b) ^ 2) *
            Line.Basic.lineNorm mirror := by ring1
      _ = (Line.Basic.lineNorm first *
          (second.a * mirror.b - mirror.a * second.b) ^ 2) *
            Line.Basic.lineNorm mirror := by rw [balance]
      _ = (second.a * mirror.b - mirror.a * second.b) ^ 2 *
          (Line.Basic.lineNorm first * Line.Basic.lineNorm mirror) := by ring1
  · intro equalSpreads
    unfold Spread.spread at equalSpreads
    have crossProduct := (fun {K : Type _} [ExplicitField K] {leftNumerator rightNumerator
      leftDenominator rightDenominator : K} (leftNonzero : leftDenominator ≠ 0) (rightNonzero : rightDenominator ≠ 0)
      (ratiosEqual : leftNumerator / leftDenominator = rightNumerator / rightDenominator) =>
      (Purelib.Algebra.Field.Ratio.cross_product_of_ratio_eq (K := K) (leftNumerator := leftNumerator) (rightNumerator
      := rightNumerator) (leftDenominator := leftDenominator) (rightDenominator := rightDenominator) leftNonzero
      rightNonzero ratiosEqual : leftNumerator * rightDenominator = rightNumerator * leftDenominator))
      firstDenominatorNonzero
      secondDenominatorNonzero equalSpreads
    have scaledDifference :
        (Line.Basic.lineNorm second *
              (first.a * mirror.b - mirror.a * first.b) ^ 2 -
            Line.Basic.lineNorm first *
              (second.a * mirror.b - mirror.a * second.b) ^ 2) *
          Line.Basic.lineNorm mirror = 0 := by
      calc
        (Line.Basic.lineNorm second *
                (first.a * mirror.b - mirror.a * first.b) ^ 2 -
              Line.Basic.lineNorm first *
                (second.a * mirror.b - mirror.a * second.b) ^ 2) *
            Line.Basic.lineNorm mirror =
          (first.a * mirror.b - mirror.a * first.b) ^ 2 *
              (Line.Basic.lineNorm second * Line.Basic.lineNorm mirror) -
            (second.a * mirror.b - mirror.a * second.b) ^ 2 *
              (Line.Basic.lineNorm first * Line.Basic.lineNorm mirror) := by ring1
        _ = 0 := by rw [crossProduct]; ring1
    have differenceZero :
        Line.Basic.lineNorm second *
              (first.a * mirror.b - mirror.a * first.b) ^ 2 -
            Line.Basic.lineNorm first *
              (second.a * mirror.b - mirror.a * second.b) ^ 2 = 0 := by
      apply ExplicitField.eq_of_mul_eq_mul_right
        (show Line.Basic.lineNorm mirror ≠ 0 from mirrorNonNull)
      simpa only [zero_mul] using scaledDifference
    have firstSecondDeterminantNonzero :
        first.a * second.b - second.a * first.b ≠ 0 := by
      intro determinantZero
      apply distinct
      apply Relations.line_equivalent_of_parallel_and_common_point first second point
      · exact determinantZero
      · exact firstContains
      · exact secondContains
    have reflectedProductZero :
        (first.a * second.b - second.a * first.b) *
          (Line.reflectedLineA mirror first * second.b -
            second.a * Line.reflectedLineB mirror first) = 0 := by
      calc
        (first.a * second.b - second.a * first.b) *
            (Line.reflectedLineA mirror first * second.b -
              second.a * Line.reflectedLineB mirror first) =
          -(Line.Basic.lineNorm second *
                (first.a * mirror.b - mirror.a * first.b) ^ 2 -
              Line.Basic.lineNorm first *
                (second.a * mirror.b - mirror.a * second.b) ^ 2) := by
            rw [reflection_spread_factorization mirror
              first second]
            ring1
        _ = 0 := by rw [differenceZero]; ring1
    have reflectedDeterminantZero :
        Line.reflectedLineA mirror first * second.b -
            second.a * Line.reflectedLineB mirror first = 0 := by
      by_cases determinantZero :
          Line.reflectedLineA mirror first * second.b -
              second.a * Line.reflectedLineB mirror first = 0
      · exact determinantZero
      · exact False.elim
          ((ExplicitField.mul_ne_zero firstSecondDeterminantNonzero
            determinantZero) reflectedProductZero)
    have reflectedParallel :
        (Line.reflectLine mirror first mirrorNonNull).Parallel second := by
      exact reflectedDeterminantZero
    have reflectedContains :
        (Line.reflectLine mirror first mirrorNonNull).Contains point :=
      Line.reflectLine_contains_common_point mirror first mirrorNonNull point
        mirrorContains firstContains
    exact Relations.line_equivalent_of_parallel_and_common_point
      (Line.reflectLine mirror first mirrorNonNull) second point reflectedParallel
      reflectedContains secondContains

end Purelib.Geometry.Plane.Reflection.Spread

end

end
