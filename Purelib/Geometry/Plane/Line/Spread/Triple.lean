module
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Spread
public import Purelib.Geometry.Trigonometry.Spread.Triple
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

open Purelib.Geometry.Trigonometry.Spread.Triple

section
@[expose] public section

/-!
# Divine Proportions, Chapter 7: the triple spread formula

The proof is performed directly on the six finite line coefficients.  A
single explicit common denominator replaces the book's auxiliary triangle,
and every cancellation is witnessed by the three non-null hypotheses.
-/

namespace Purelib.Geometry.Plane.Line.Spread.Triple

variable {K : Type*} [ExplicitField K]

/-- The three pairwise spreads of non-null lines satisfy the triple-spread polynomial identity.

Their squared sum equals twice the sum of their squares plus four times their product; no distinctness or characteristic
restriction is required. -/
theorem triple_spread_formula
    (first second third : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull) :
    let s₁ := Spread.spread second third secondNonNull thirdNonNull
    let s₂ := Spread.spread first third firstNonNull thirdNonNull
    let s₃ := Spread.spread first second firstNonNull secondNonNull
    (s₁ + s₂ + s₃) ^ 2 =
      2 * (s₁ ^ 2 + s₂ ^ 2 + s₃ ^ 2) + 4 * s₁ * s₂ * s₃ := by
  dsimp only
  let firstNorm := Basic.lineNorm first
  let secondNorm := Basic.lineNorm second
  let thirdNorm := Basic.lineNorm third
  let firstCross := second.a * third.b - third.a * second.b
  let secondCross := first.a * third.b - third.a * first.b
  let thirdCross := first.a * second.b - second.a * first.b
  let denominator := firstNorm * secondNorm * thirdNorm
  let firstNumerator := firstNorm * firstCross ^ 2
  let secondNumerator := secondNorm * secondCross ^ 2
  let thirdNumerator := thirdNorm * thirdCross ^ 2
  let crossProduct := firstCross * secondCross * thirdCross
  have denominatorNonzero : denominator ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero firstNonNull secondNonNull)
      thirdNonNull
  have firstSpread :
      Spread.spread second third secondNonNull thirdNonNull =
        firstNumerator / denominator := by
    unfold Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero secondNonNull thirdNonNull)
      denominatorNonzero
    unfold firstNumerator denominator firstNorm secondNorm thirdNorm firstCross Basic.lineNorm
    ring1
  have secondSpread :
      Spread.spread first third firstNonNull thirdNonNull =
        secondNumerator / denominator := by
    unfold Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero firstNonNull thirdNonNull)
      denominatorNonzero
    unfold secondNumerator denominator firstNorm secondNorm thirdNorm secondCross Basic.lineNorm
    ring1
  have thirdSpread :
      Spread.spread first second firstNonNull secondNonNull =
        thirdNumerator / denominator := by
    unfold Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero firstNonNull secondNonNull)
      denominatorNonzero
    unfold thirdNumerator denominator firstNorm secondNorm thirdNorm thirdCross Basic.lineNorm
    ring1
  have numeratorProduct :
      firstNumerator * secondNumerator * thirdNumerator =
        denominator * crossProduct ^ 2 := by
    unfold firstNumerator secondNumerator thirdNumerator denominator crossProduct
    ring1
  have clearedIdentity :
      (firstNumerator + secondNumerator + thirdNumerator) ^ 2 =
        2 * (firstNumerator ^ 2 + secondNumerator ^ 2 +
          thirdNumerator ^ 2) +
        4 * crossProduct ^ 2 := by
    unfold firstNumerator secondNumerator thirdNumerator crossProduct
    unfold firstNorm secondNorm thirdNorm firstCross secondCross thirdCross Basic.lineNorm
    ring1
  rw [firstSpread, secondSpread, thirdSpread]
  exact Purelib.Geometry.Trigonometry.Spread.Triple.triple_fraction_identity firstNumerator secondNumerator
    thirdNumerator
    denominator crossProduct denominatorNonzero numeratorProduct clearedIdentity

/-- The three pairwise spreads of non-null lines form a spread triple.

The non-nullness hypotheses make all three spreads defined, and their values satisfy the triple-spread polynomial
relation (Theorem 47). -/
theorem three_lines_form_spreadTriple
    (first second third : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull) :
    TripleSpread.SpreadTriple
      (Spread.spread second third secondNonNull thirdNonNull)
      (Spread.spread first third firstNonNull thirdNonNull)
      (Spread.spread first second firstNonNull secondNonNull) := by
  unfold TripleSpread.SpreadTriple TripleSpread.tripleSpreadFunction
  rw [triple_spread_formula first second third firstNonNull secondNonNull
    thirdNonNull]
  ring1

/-- Theorem 51 (Equal spreads). The third spread is forced into the two finite alternatives `0` and the logistic value
`4s(1-s)`. -/
theorem equal_spreads [DecidableEq K]
    (first second third : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull)
    (equalSpreads :
      Spread.spread first second firstNonNull secondNonNull =
        Spread.spread second third secondNonNull thirdNonNull) :
    let s := Spread.spread first second firstNonNull secondNonNull
    let r := Spread.spread first third firstNonNull thirdNonNull
    r = 0 ∨ r = 4 * s * (1 - s) := by
  dsimp only
  let s := Spread.spread first second firstNonNull secondNonNull
  let r := Spread.spread first third firstNonNull thirdNonNull
  change s = Spread.spread second third secondNonNull thirdNonNull at equalSpreads
  have triple := triple_spread_formula first second third firstNonNull
    secondNonNull thirdNonNull
  change
    (Spread.spread second third secondNonNull thirdNonNull + r + s) ^ 2 =
      2 * ((Spread.spread second third secondNonNull thirdNonNull) ^ 2 +
        r ^ 2 + s ^ 2) +
        4 * Spread.spread second third secondNonNull thirdNonNull * r * s at triple
  rw [← equalSpreads] at triple
  have equation :
      (2 * s + r) ^ 2 =
        2 * (2 * s ^ 2 + r ^ 2) + 4 * s ^ 2 * r := by
    calc
      (2 * s + r) ^ 2 = (s + r + s) ^ 2 := by ring1
      _ = 2 * (s ^ 2 + r ^ 2 + s ^ 2) + 4 * s * r * s := triple
      _ = 2 * (2 * s ^ 2 + r ^ 2) + 4 * s ^ 2 * r := by ring1
  have factorZero : r * (r - 4 * s * (1 - s)) = 0 := by
    calc
      r * (r - 4 * s * (1 - s)) =
          -((2 * s + r) ^ 2 -
            (2 * (2 * s ^ 2 + r ^ 2) + 4 * s ^ 2 * r)) := by ring1
      _ = 0 := by rw [equation]; ring1
  by_cases rZero : r = 0
  · exact Or.inl rZero
  · right
    have secondFactorZero : r - 4 * s * (1 - s) = 0 := by
      by_cases factorZeroCase : r - 4 * s * (1 - s) = 0
      · exact factorZeroCase
      · exact False.elim
          ((ExplicitField.mul_ne_zero rZero factorZeroCase) factorZero)
    calc
      r = (r - 4 * s * (1 - s)) + 4 * s * (1 - s) := by ring1
      _ = 4 * s * (1 - s) := by rw [secondFactorZero]; ring1

end Purelib.Geometry.Plane.Line.Spread.Triple

end
