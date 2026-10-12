module
public import Purelib.Data.Nat.Order
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Spread.Squares
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Spread

section
@[expose] public section

/-!
# Divine Proportions, §6.9: vertex bisectors

An explicit witness `r² = ‖l₁‖‖l₂‖` produces the two normalized
bisectors `r l₁ ± ‖l₁‖ l₂`.  This formulation is equivalent to the
book's longer coefficient display, but is symmetric enough that all finite
field cancellations remain visible.
-/

namespace Purelib.Geometry.Plane.Line.Spread.Classification

variable {K : Type*} [ExplicitField K]

/-- Two displayed equal-spread bisectors of the same nonparallel pair are parallel or perpendicular. This quotient-free
algebraic form is stronger than the incidence-specific observation used in Theorem 58. -/
theorem equal_spread_lines_parallel_or_perpendicular
  [DecidableEq K]
    (first second left right : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (leftNonNull : ¬ left.IsNull) (rightNonNull : ¬ right.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (leftEqual :
      Spread.spread first left firstNonNull leftNonNull =
        Spread.spread second left secondNonNull leftNonNull)
    (rightEqual :
      Spread.spread first right firstNonNull rightNonNull =
        Spread.spread second right secondNonNull rightNonNull) :
    left.Parallel right ∨ left.Perpendicular right := by
  let firstSecondDeterminant :=
    first.a * second.b - second.a * first.b
  let traceCoefficient :=
    -(first.a * second.b + first.b * second.a)
  let mixedCoefficient :=
    first.a * second.a - first.b * second.b
  let bisectorForm := fun candidate : Plane.Line K =>
    traceCoefficient * (candidate.a ^ 2 - candidate.b ^ 2) +
      2 * mixedCoefficient * candidate.a * candidate.b
  have determinantNonzero : firstSecondDeterminant ≠ 0 := notParallel
  have formZero (candidate : Plane.Line K)
      (candidateNonNull : ¬ candidate.IsNull)
      (equalSpreads :
        Spread.spread first candidate firstNonNull candidateNonNull =
          Spread.spread second candidate secondNonNull candidateNonNull) :
      bisectorForm candidate = 0 := by
    have balance := Purelib.Geometry.Plane.Line.Spread.Squares.equal_spreads_norm_balance first second candidate
      firstNonNull secondNonNull candidateNonNull equalSpreads
    have differenceZero :
        Basic.lineNorm second *
              (first.a * candidate.b - candidate.a * first.b) ^ 2 -
            Basic.lineNorm first *
              (second.a * candidate.b - candidate.a * second.b) ^ 2 = 0 := by
      rw [balance]
      ring1
    have factored :
        firstSecondDeterminant * bisectorForm candidate = 0 := by
      calc
        firstSecondDeterminant * bisectorForm candidate =
            Basic.lineNorm second *
                (first.a * candidate.b - candidate.a * first.b) ^ 2 -
              Basic.lineNorm first *
                (second.a * candidate.b - candidate.a * second.b) ^ 2 := by
          unfold firstSecondDeterminant bisectorForm traceCoefficient
            mixedCoefficient Basic.lineNorm
          ring1
        _ = 0 := differenceZero
    by_cases formIsZero : bisectorForm candidate = 0
    · exact formIsZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero determinantNonzero formIsZero)
          factored)
  have leftFormZero := formZero left leftNonNull leftEqual
  have rightFormZero := formZero right rightNonNull rightEqual
  let betweenDeterminant := left.a * right.b - right.a * left.b
  let betweenDot := left.a * right.a + left.b * right.b
  have traceTimesProductZero :
      traceCoefficient * (betweenDeterminant * betweenDot) = 0 := by
    calc
      traceCoefficient * (betweenDeterminant * betweenDot) =
          bisectorForm left * right.a * right.b -
            bisectorForm right * left.a * left.b := by
        unfold bisectorForm betweenDeterminant betweenDot
        ring1
      _ = 0 := by rw [leftFormZero, rightFormZero]; ring1
  have twiceMixedTimesProductZero :
      2 * (mixedCoefficient * (betweenDeterminant * betweenDot)) = 0 := by
    calc
      2 * (mixedCoefficient * (betweenDeterminant * betweenDot)) =
          -(bisectorForm left * (right.a ^ 2 - right.b ^ 2) -
            bisectorForm right * (left.a ^ 2 - left.b ^ 2)) := by
        unfold bisectorForm betweenDeterminant betweenDot
        ring1
      _ = 0 := by rw [leftFormZero, rightFormZero]; ring1
  have mixedTimesProductZero :
      mixedCoefficient * (betweenDeterminant * betweenDot) = 0 := by
    by_cases productZero :
        mixedCoefficient * (betweenDeterminant * betweenDot) = 0
    · exact productZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero twoNonzero productZero)
          twiceMixedTimesProductZero)
  have coefficientSquares :
      traceCoefficient ^ 2 + mixedCoefficient ^ 2 =
        Basic.lineNorm first * Basic.lineNorm second := by
    unfold traceCoefficient mixedCoefficient Basic.lineNorm
    ring1
  have normTimesProductZero :
      (Basic.lineNorm first * Basic.lineNorm second) *
        (betweenDeterminant * betweenDot) = 0 := by
    calc
      (Basic.lineNorm first * Basic.lineNorm second) *
          (betweenDeterminant * betweenDot) =
        traceCoefficient *
            (traceCoefficient * (betweenDeterminant * betweenDot)) +
          mixedCoefficient *
            (mixedCoefficient * (betweenDeterminant * betweenDot)) := by
              rw [← coefficientSquares]
              ring1
      _ = 0 := by
        rw [traceTimesProductZero, mixedTimesProductZero]
        ring1
  have betweenProductZero : betweenDeterminant * betweenDot = 0 := by
    have normProductNonzero : Basic.lineNorm first * Basic.lineNorm second ≠ 0 :=
      ExplicitField.mul_ne_zero firstNonNull secondNonNull
    by_cases productZero : betweenDeterminant * betweenDot = 0
    · exact productZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero normProductNonzero productZero)
          normTimesProductZero)
  by_cases determinantZero : betweenDeterminant = 0
  · left
    exact determinantZero
  · right
    by_cases dotZero : betweenDot = 0
    · exact dotZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero determinantZero dotZero)
          betweenProductZero)
end Purelib.Geometry.Plane.Line.Spread.Classification

end
