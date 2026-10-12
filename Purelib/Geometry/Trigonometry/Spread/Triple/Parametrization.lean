module
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Trigonometry.Spread.Triple

section
@[expose] public section

/-!
# Divine Proportions, Chapter 7: the triple spread formula

The proof is performed directly on the six finite line coefficients.  A
single explicit common denominator replaces the book's auxiliary triangle,
and every cancellation is witnessed by the three non-null hypotheses.
-/

namespace Purelib.Geometry.Trigonometry.Spread.Triple.Parametrization

variable {K : Type*} [ExplicitField K]

/-- Exercise 7.5: the displayed two-parameter rational construction always produces a spread triple. The hypotheses are
exactly the two denominators which the printed fractions require to be nonzero. -/
theorem exercise_7_5
    (u v : K)
    (uDenominatorNonzero : 1 + u ^ 2 ≠ 0)
    (vDenominatorNonzero : 1 + v ^ 2 ≠ 0) :
    TripleSpread.SpreadTriple
      (u ^ 2 / (1 + u ^ 2))
      (v ^ 2 / (1 + v ^ 2))
      ((u - v) ^ 2 / ((1 + u ^ 2) * (1 + v ^ 2))) := by
  let uDenominator := 1 + u ^ 2
  let vDenominator := 1 + v ^ 2
  let denominator := uDenominator * vDenominator
  let firstNumerator := u ^ 2 * vDenominator
  let secondNumerator := v ^ 2 * uDenominator
  let thirdNumerator := (u - v) ^ 2
  let product := u * v * (u - v)
  have denominatorNonzero : denominator ≠ 0 :=
    ExplicitField.mul_ne_zero uDenominatorNonzero
      vDenominatorNonzero
  have firstValue :
      u ^ 2 / (1 + u ^ 2) = firstNumerator / denominator := by
    apply Ratio.ratio_eq_of_cross_product uDenominatorNonzero denominatorNonzero
    unfold firstNumerator denominator uDenominator vDenominator
    ring1
  have secondValue :
      v ^ 2 / (1 + v ^ 2) = secondNumerator / denominator := by
    apply Ratio.ratio_eq_of_cross_product vDenominatorNonzero denominatorNonzero
    unfold secondNumerator denominator uDenominator vDenominator
    ring1
  have thirdValue :
      (u - v) ^ 2 / ((1 + u ^ 2) * (1 + v ^ 2)) =
        thirdNumerator / denominator := by
    unfold thirdNumerator denominator uDenominator vDenominator
    rfl
  have numeratorProduct :
      firstNumerator * secondNumerator * thirdNumerator =
        denominator * product ^ 2 := by
    unfold firstNumerator secondNumerator thirdNumerator denominator product
      uDenominator vDenominator
    ring1
  have numeratorIdentity :
      (firstNumerator + secondNumerator + thirdNumerator) ^ 2 =
        2 * (firstNumerator ^ 2 + secondNumerator ^ 2 +
          thirdNumerator ^ 2) + 4 * product ^ 2 := by
    unfold firstNumerator secondNumerator thirdNumerator product
      uDenominator vDenominator
    ring1
  have fractionIdentity := Purelib.Geometry.Trigonometry.Spread.Triple.triple_fraction_identity firstNumerator
    secondNumerator thirdNumerator denominator product denominatorNonzero
    numeratorProduct numeratorIdentity
  unfold TripleSpread.SpreadTriple TripleSpread.tripleSpreadFunction
  rw [firstValue, secondValue, thirdValue, fractionIdentity]
  ring1

/-- Exercise 7.5's requested counterexample: `{1,0,1}` is a spread triple, but its first entry cannot have the displayed
parametrized form in any nontrivial constructive explicit field. -/
theorem exercise_7_5_counterexample [Nontrivial K] :
    TripleSpread.SpreadTriple (1 : K) 0 1 ∧
      ¬ ∃ u v : K,
        1 + u ^ 2 ≠ 0 ∧
        1 + v ^ 2 ≠ 0 ∧
        u ^ 2 / (1 + u ^ 2) = 1 ∧
        v ^ 2 / (1 + v ^ 2) = 0 ∧
        (u - v) ^ 2 / ((1 + u ^ 2) * (1 + v ^ 2)) = 1 := by
  constructor
  · unfold TripleSpread.SpreadTriple TripleSpread.tripleSpreadFunction
    ring1
  · rintro ⟨u, v, uDenominatorNonzero, _vDenominatorNonzero,
      firstValue, _secondValue, _thirdValue⟩
    have multiplied := congrArg (fun value : K => value * (1 + u ^ 2))
      firstValue
    rw [ExplicitField.div_mul_cancel (u ^ 2) uDenominatorNonzero]
      at multiplied
    have oneEqualsZero : (1 : K) = 0 := by
      calc
        1 = 1 * (1 + u ^ 2) - u ^ 2 := by ring1
        _ = 0 := by rw [← multiplied]; ring1
    exact one_ne_zero oneEqualsZero
end Purelib.Geometry.Trigonometry.Spread.Triple.Parametrization

end
