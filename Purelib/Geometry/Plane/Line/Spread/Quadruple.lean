module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Spread.Triple
public import Purelib.Geometry.Trigonometry.Spread.Quadruple
import Purelib.Geometry.Trigonometry.Spread.Triple
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Spread

open Purelib.Geometry.Trigonometry.Spread

open Purelib.Geometry.Trigonometry.Spread.Triple

section
@[expose] public section

/-!
# Divine Proportions, §7.7: quadruple spread and cross formulas

The scalar elimination is kept separate from the geometric specialization.
Two displayed spread triples give two explicit quadratic equations with a
common root; the finite quadratic-compatibility calculation then yields the
four-variable polynomial.
-/

namespace Purelib.Geometry.Plane.Line.Spread.Quadruple

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The polynomial clause of Theorem 54, without the characteristic assumption needed only by its two quotient formulas.
-/
theorem quadruple_spread_relation
    (first second third fourth : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull) (fourthNonNull : ¬ fourth.IsNull) :
    let s₁₂ := Spread.spread first second firstNonNull secondNonNull
    let s₂₃ := Spread.spread second third secondNonNull thirdNonNull
    let s₃₄ := Spread.spread third fourth thirdNonNull fourthNonNull
    let s₁₄ := Spread.spread first fourth firstNonNull fourthNonNull
    Quadruple.quadrupleSpreadFunction s₁₂ s₂₃ s₃₄ s₁₄ = 0 := by
  dsimp only
  let s₁₂ := Spread.spread first second firstNonNull secondNonNull
  let s₂₃ := Spread.spread second third secondNonNull thirdNonNull
  let s₃₄ := Spread.spread third fourth thirdNonNull fourthNonNull
  let s₁₄ := Spread.spread first fourth firstNonNull fourthNonNull
  let s₁₃ := Spread.spread first third firstNonNull thirdNonNull
  have firstRaw := Triple.three_lines_form_spreadTriple first second third firstNonNull
    secondNonNull thirdNonNull
  have firstTriple : TripleSpread.SpreadTriple s₁₂ s₂₃ s₁₃ := by
    exact Purelib.Geometry.Trigonometry.Spread.Triple.spreadTriple_reorder firstRaw
  have secondTriple : TripleSpread.SpreadTriple s₃₄ s₁₄ s₁₃ :=
    Triple.three_lines_form_spreadTriple first third fourth firstNonNull thirdNonNull
      fourthNonNull
  exact Quadruple.two_spread_triples_compatibility s₁₂ s₂₃ s₃₄ s₁₄ s₁₃
    firstTriple secondTriple

/-- Theorem 54 (Quadruple spread formula), including both diagonal-spread formulas under their exact nondegeneracy
hypotheses. -/
theorem quadruple_spread_formula
    (first second third fourth : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull) (fourthNonNull : ¬ fourth.IsNull)
    (twoNonzero : (2 : K) ≠ 0) :
    let s₁₂ := Spread.spread first second firstNonNull secondNonNull
    let s₂₃ := Spread.spread second third secondNonNull thirdNonNull
    let s₃₄ := Spread.spread third fourth thirdNonNull fourthNonNull
    let s₁₄ := Spread.spread first fourth firstNonNull fourthNonNull
    let s₁₃ := Spread.spread first third firstNonNull thirdNonNull
    let s₂₄ := Spread.spread second fourth secondNonNull fourthNonNull
    Quadruple.quadrupleSpreadFunction s₁₂ s₂₃ s₃₄ s₁₄ = 0 ∧
      (s₁₂ + s₂₃ - 2 * s₁₂ * s₂₃ ≠
          s₃₄ + s₁₄ - 2 * s₃₄ * s₁₄ →
        let denominator :=
          2 * (s₁₂ + s₂₃ - s₃₄ - s₁₄ -
            2 * s₁₂ * s₂₃ + 2 * s₃₄ * s₁₄)
        denominator ≠ 0 ∧
          s₁₃ = ((s₁₂ - s₂₃) ^ 2 - (s₃₄ - s₁₄) ^ 2) /
            denominator) ∧
      (s₂₃ + s₃₄ - 2 * s₂₃ * s₃₄ ≠
          s₁₂ + s₁₄ - 2 * s₁₂ * s₁₄ →
        let denominator :=
          2 * (s₂₃ + s₃₄ - s₁₂ - s₁₄ -
            2 * s₂₃ * s₃₄ + 2 * s₁₂ * s₁₄)
        denominator ≠ 0 ∧
          s₂₄ = ((s₂₃ - s₃₄) ^ 2 - (s₁₂ - s₁₄) ^ 2) /
            denominator) := by
  dsimp only
  let s₁₂ := Spread.spread first second firstNonNull secondNonNull
  let s₂₃ := Spread.spread second third secondNonNull thirdNonNull
  let s₃₄ := Spread.spread third fourth thirdNonNull fourthNonNull
  let s₁₄ := Spread.spread first fourth firstNonNull fourthNonNull
  let s₁₃ := Spread.spread first third firstNonNull thirdNonNull
  let s₂₄ := Spread.spread second fourth secondNonNull fourthNonNull
  have firstRaw := Triple.three_lines_form_spreadTriple first second third firstNonNull
    secondNonNull thirdNonNull
  have firstTriple : TripleSpread.SpreadTriple s₁₂ s₂₃ s₁₃ := by
    exact Purelib.Geometry.Trigonometry.Spread.Triple.spreadTriple_reorder firstRaw
  have secondTriple : TripleSpread.SpreadTriple s₃₄ s₁₄ s₁₃ :=
    Triple.three_lines_form_spreadTriple first third fourth firstNonNull thirdNonNull
      fourthNonNull
  have thirdRaw := Triple.three_lines_form_spreadTriple second third fourth
    secondNonNull thirdNonNull fourthNonNull
  have thirdTriple : TripleSpread.SpreadTriple s₂₃ s₃₄ s₂₄ := by
    exact Purelib.Geometry.Trigonometry.Spread.Triple.spreadTriple_reorder thirdRaw
  have fourthRaw := Triple.three_lines_form_spreadTriple first second fourth
    firstNonNull secondNonNull fourthNonNull
  have fourthTriple : TripleSpread.SpreadTriple s₁₂ s₁₄ s₂₄ := by
    exact Purelib.Geometry.Trigonometry.Spread.Triple.spreadTriple_swap_last
      (Purelib.Geometry.Trigonometry.Spread.Triple.spreadTriple_reorder fourthRaw)
  have firstResult := Quadruple.two_spread_triples s₁₂ s₂₃ s₃₄ s₁₄ s₁₃
    twoNonzero firstTriple secondTriple
  have secondResult := Quadruple.two_spread_triples s₂₃ s₃₄ s₁₂ s₁₄ s₂₄
    twoNonzero thirdTriple fourthTriple
  exact ⟨firstResult.1, firstResult.2, secondResult.2⟩
end Purelib.Geometry.Plane.Line.Spread.Quadruple

end
