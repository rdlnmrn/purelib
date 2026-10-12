module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Cross
import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Spread.Quadruple
import Purelib.Geometry.Plane.Line.Spread.Triple
import Purelib.Geometry.Plane.Line.Trigonometry.Conversion
import Purelib.Geometry.Trigonometry.Cross.Quadruple
public import Purelib.Geometry.Trigonometry.Spread.Quadruple
import Purelib.Geometry.Trigonometry.Spread.Triple
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Spread

open Purelib.Geometry.Trigonometry

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

namespace Purelib.Geometry.Plane.Line.Cross.Quadruple

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Four non-null lines have consecutive crosses satisfying the quadruple-spread polynomial.

The relation follows by complementing each consecutive spread and imposes no nonzero-two hypothesis. -/
theorem quadruple_cross_formula
    (first second third fourth : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull) (fourthNonNull : ¬ fourth.IsNull) :
    Quadruple.quadrupleSpreadFunction
      (Cross.cross first second firstNonNull secondNonNull)
      (Cross.cross second third secondNonNull thirdNonNull)
      (Cross.cross third fourth thirdNonNull fourthNonNull)
      (Cross.cross first fourth firstNonNull fourthNonNull) = 0 := by
  let s₁₂ := Spread.spread first second firstNonNull secondNonNull
  let s₂₃ := Spread.spread second third secondNonNull thirdNonNull
  let s₃₄ := Spread.spread third fourth thirdNonNull fourthNonNull
  let s₁₄ := Spread.spread first fourth firstNonNull fourthNonNull
  have spreadRelation := Quadruple.quadruple_spread_relation first second third fourth
    firstNonNull secondNonNull thirdNonNull fourthNonNull
  have firstComplement :
      Cross.cross first second firstNonNull secondNonNull = 1 - s₁₂ := by
    have sum := Trigonometry.Conversion.spread_add_cross first second firstNonNull secondNonNull
    unfold s₁₂
    calc
      Cross.cross first second firstNonNull secondNonNull =
          (Spread.spread first second firstNonNull secondNonNull +
            Cross.cross first second firstNonNull secondNonNull) -
            Spread.spread first second firstNonNull secondNonNull := by ring1
      _ = 1 - Spread.spread first second firstNonNull secondNonNull := by rw [sum]
  have secondComplement :
      Cross.cross second third secondNonNull thirdNonNull = 1 - s₂₃ := by
    have sum := Trigonometry.Conversion.spread_add_cross second third secondNonNull thirdNonNull
    unfold s₂₃
    calc
      Cross.cross second third secondNonNull thirdNonNull =
          (Spread.spread second third secondNonNull thirdNonNull +
            Cross.cross second third secondNonNull thirdNonNull) -
            Spread.spread second third secondNonNull thirdNonNull := by ring1
      _ = 1 - Spread.spread second third secondNonNull thirdNonNull := by rw [sum]
  have thirdComplement :
      Cross.cross third fourth thirdNonNull fourthNonNull = 1 - s₃₄ := by
    have sum := Trigonometry.Conversion.spread_add_cross third fourth thirdNonNull fourthNonNull
    unfold s₃₄
    calc
      Cross.cross third fourth thirdNonNull fourthNonNull =
          (Spread.spread third fourth thirdNonNull fourthNonNull +
            Cross.cross third fourth thirdNonNull fourthNonNull) -
            Spread.spread third fourth thirdNonNull fourthNonNull := by ring1
      _ = 1 - Spread.spread third fourth thirdNonNull fourthNonNull := by rw [sum]
  have fourthComplement :
      Cross.cross first fourth firstNonNull fourthNonNull = 1 - s₁₄ := by
    have sum := Trigonometry.Conversion.spread_add_cross first fourth firstNonNull fourthNonNull
    unfold s₁₄
    calc
      Cross.cross first fourth firstNonNull fourthNonNull =
          (Spread.spread first fourth firstNonNull fourthNonNull +
            Cross.cross first fourth firstNonNull fourthNonNull) -
            Spread.spread first fourth firstNonNull fourthNonNull := by ring1
      _ = 1 - Spread.spread first fourth firstNonNull fourthNonNull := by rw [sum]
  rw [firstComplement, secondComplement, thirdComplement, fourthComplement,
    Quadruple.quadrupleSpreadFunction_complement]
  exact spreadRelation

/-- Corrected Exercise 7.14. Both printed right-hand sides determine the complements of the requested diagonal crosses.
-/
theorem exercise_7_14_corrected
    (first second third fourth : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull) (fourthNonNull : ¬ fourth.IsNull)
    (twoNonzero : (2 : K) ≠ 0) :
    let c₁₂ := Cross.cross first second firstNonNull secondNonNull
    let c₂₃ := Cross.cross second third secondNonNull thirdNonNull
    let c₃₄ := Cross.cross third fourth thirdNonNull fourthNonNull
    let c₁₄ := Cross.cross first fourth firstNonNull fourthNonNull
    let c₁₃ := Cross.cross first third firstNonNull thirdNonNull
    let c₂₄ := Cross.cross second fourth secondNonNull fourthNonNull
    (c₁₂ + c₂₃ - 2 * c₁₂ * c₂₃ ≠
        c₃₄ + c₁₄ - 2 * c₃₄ * c₁₄ →
      let denominator :=
        2 * (c₁₂ + c₂₃ - c₃₄ - c₁₄ -
          2 * c₁₂ * c₂₃ + 2 * c₃₄ * c₁₄)
      denominator ≠ 0 ∧
        c₁₃ = 1 -
          ((c₁₂ - c₂₃) ^ 2 - (c₃₄ - c₁₄) ^ 2) /
            denominator) ∧
    (c₂₃ + c₃₄ - 2 * c₂₃ * c₃₄ ≠
        c₁₂ + c₁₄ - 2 * c₁₂ * c₁₄ →
      let denominator :=
        2 * (c₂₃ + c₃₄ - c₁₂ - c₁₄ -
          2 * c₂₃ * c₃₄ + 2 * c₁₂ * c₁₄)
      denominator ≠ 0 ∧
        c₂₄ = 1 -
          ((c₂₃ - c₃₄) ^ 2 - (c₁₂ - c₁₄) ^ 2) /
            denominator) := by
  dsimp only
  let c₁₂ := Cross.cross first second firstNonNull secondNonNull
  let c₂₃ := Cross.cross second third secondNonNull thirdNonNull
  let c₃₄ := Cross.cross third fourth thirdNonNull fourthNonNull
  let c₁₄ := Cross.cross first fourth firstNonNull fourthNonNull
  let c₁₃ := Cross.cross first third firstNonNull thirdNonNull
  let c₂₄ := Cross.cross second fourth secondNonNull fourthNonNull
  have firstRaw := Triple.three_lines_form_spreadTriple first second third firstNonNull
    secondNonNull thirdNonNull
  have firstSpreadTriple : TripleSpread.SpreadTriple
      (Spread.spread first second firstNonNull secondNonNull)
      (Spread.spread second third secondNonNull thirdNonNull)
      (Spread.spread first third firstNonNull thirdNonNull) :=
    Purelib.Geometry.Trigonometry.Spread.Triple.spreadTriple_reorder firstRaw
  have firstCrossTriple : TripleSpread.SpreadTriple (1 - c₁₂) (1 - c₂₃) (1 - c₁₃) := by
    unfold c₁₂ c₂₃ c₁₃
    rw [← Trigonometry.Conversion.spread_eq_one_sub_cross first second firstNonNull secondNonNull,
      ← Trigonometry.Conversion.spread_eq_one_sub_cross second third secondNonNull thirdNonNull,
      ← Trigonometry.Conversion.spread_eq_one_sub_cross first third firstNonNull thirdNonNull]
    exact firstSpreadTriple
  have secondSpreadTriple : TripleSpread.SpreadTriple
      (Spread.spread third fourth thirdNonNull fourthNonNull)
      (Spread.spread first fourth firstNonNull fourthNonNull)
      (Spread.spread first third firstNonNull thirdNonNull) :=
    Triple.three_lines_form_spreadTriple first third fourth firstNonNull thirdNonNull
      fourthNonNull
  have secondCrossTriple : TripleSpread.SpreadTriple (1 - c₃₄) (1 - c₁₄) (1 - c₁₃) := by
    unfold c₃₄ c₁₄ c₁₃
    rw [← Trigonometry.Conversion.spread_eq_one_sub_cross third fourth thirdNonNull fourthNonNull,
      ← Trigonometry.Conversion.spread_eq_one_sub_cross first fourth firstNonNull fourthNonNull,
      ← Trigonometry.Conversion.spread_eq_one_sub_cross first third firstNonNull thirdNonNull]
    exact secondSpreadTriple
  have thirdRaw := Triple.three_lines_form_spreadTriple second third fourth
    secondNonNull thirdNonNull fourthNonNull
  have thirdSpreadTriple : TripleSpread.SpreadTriple
      (Spread.spread second third secondNonNull thirdNonNull)
      (Spread.spread third fourth thirdNonNull fourthNonNull)
      (Spread.spread second fourth secondNonNull fourthNonNull) :=
    Purelib.Geometry.Trigonometry.Spread.Triple.spreadTriple_reorder thirdRaw
  have thirdCrossTriple : TripleSpread.SpreadTriple (1 - c₂₃) (1 - c₃₄) (1 - c₂₄) := by
    unfold c₂₃ c₃₄ c₂₄
    rw [← Trigonometry.Conversion.spread_eq_one_sub_cross second third secondNonNull thirdNonNull,
      ← Trigonometry.Conversion.spread_eq_one_sub_cross third fourth thirdNonNull fourthNonNull,
      ← Trigonometry.Conversion.spread_eq_one_sub_cross second fourth secondNonNull fourthNonNull]
    exact thirdSpreadTriple
  have fourthRaw := Triple.three_lines_form_spreadTriple first second fourth
    firstNonNull secondNonNull fourthNonNull
  have fourthSpreadTriple : TripleSpread.SpreadTriple
      (Spread.spread first second firstNonNull secondNonNull)
      (Spread.spread first fourth firstNonNull fourthNonNull)
      (Spread.spread second fourth secondNonNull fourthNonNull) :=
    Purelib.Geometry.Trigonometry.Spread.Triple.spreadTriple_swap_last
      (Purelib.Geometry.Trigonometry.Spread.Triple.spreadTriple_reorder fourthRaw)
  have fourthCrossTriple : TripleSpread.SpreadTriple (1 - c₁₂) (1 - c₁₄) (1 - c₂₄) := by
    unfold c₁₂ c₁₄ c₂₄
    rw [← Trigonometry.Conversion.spread_eq_one_sub_cross first second firstNonNull secondNonNull,
      ← Trigonometry.Conversion.spread_eq_one_sub_cross first fourth firstNonNull fourthNonNull,
      ← Trigonometry.Conversion.spread_eq_one_sub_cross second fourth secondNonNull fourthNonNull]
    exact fourthSpreadTriple
  constructor
  · intro centersDistinct
    exact Cross.Quadruple.two_cross_triples_common_value c₁₂ c₂₃ c₃₄ c₁₄ c₁₃
      twoNonzero firstCrossTriple secondCrossTriple centersDistinct
  · intro centersDistinct
    exact Cross.Quadruple.two_cross_triples_common_value c₂₃ c₃₄ c₁₂ c₁₄ c₂₄
      twoNonzero thirdCrossTriple fourthCrossTriple centersDistinct

end Purelib.Geometry.Plane.Line.Cross.Quadruple

end
