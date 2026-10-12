module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Turn.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

section
@[expose] public section

/-!
# Divine Proportions, §§7.3 and 9.2: turns and the triple twist formula

The oriented turn is retained as the explicit determinant/dot quotient.  Its
cyclic three-line identity is linear; squaring that finite identity gives the
book's Triple twist formula without separating null and non-null cases.
-/

namespace Purelib.Geometry.Plane.Line.Turn.Triple

variable {K : Type*} [ExplicitField K]

/-- The sum of the three cyclic turns equals their product.

Every consecutive pair of displayed lines is non-perpendicular, certifying the three dot-product denominators. -/
theorem triple_turn_formula
    (first second third : Plane.Line K)
    (firstSecondNotPerpendicular : ¬ first.Perpendicular second)
    (secondThirdNotPerpendicular : ¬ second.Perpendicular third)
    (thirdFirstNotPerpendicular : ¬ third.Perpendicular first) :
    let r₁ := Turn.Basic.turn second third secondThirdNotPerpendicular
    let r₂ := Turn.Basic.turn third first thirdFirstNotPerpendicular
    let r₃ := Turn.Basic.turn first second firstSecondNotPerpendicular
    r₁ + r₂ + r₃ = r₁ * r₂ * r₃ := by
  dsimp only
  let firstNumerator := second.a * third.b - third.a * second.b
  let secondNumerator := third.a * first.b - first.a * third.b
  let thirdNumerator := first.a * second.b - second.a * first.b
  let firstDenominator := second.a * third.a + second.b * third.b
  let secondDenominator := third.a * first.a + third.b * first.b
  let thirdDenominator := first.a * second.a + first.b * second.b
  let denominator := firstDenominator * secondDenominator * thirdDenominator
  have firstDenominatorNonzero : firstDenominator ≠ 0 :=
    secondThirdNotPerpendicular
  have secondDenominatorNonzero : secondDenominator ≠ 0 :=
    thirdFirstNotPerpendicular
  have thirdDenominatorNonzero : thirdDenominator ≠ 0 :=
    firstSecondNotPerpendicular
  have denominatorNonzero : denominator ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero firstDenominatorNonzero
        secondDenominatorNonzero)
      thirdDenominatorNonzero
  have firstCancel :
      (firstNumerator / firstDenominator) * firstDenominator =
        firstNumerator :=
    ExplicitField.div_mul_cancel firstNumerator firstDenominatorNonzero
  have secondCancel :
      (secondNumerator / secondDenominator) * secondDenominator =
        secondNumerator :=
    ExplicitField.div_mul_cancel secondNumerator secondDenominatorNonzero
  have thirdCancel :
      (thirdNumerator / thirdDenominator) * thirdDenominator =
        thirdNumerator :=
    ExplicitField.div_mul_cancel thirdNumerator thirdDenominatorNonzero
  have numeratorIdentity :
      firstNumerator * secondDenominator * thirdDenominator +
          secondNumerator * firstDenominator * thirdDenominator +
          thirdNumerator * firstDenominator * secondDenominator =
        firstNumerator * secondNumerator * thirdNumerator := by
    unfold firstNumerator secondNumerator thirdNumerator
    unfold firstDenominator secondDenominator thirdDenominator
    ring1
  unfold Turn.Basic.turn
  change
    firstNumerator / firstDenominator +
        secondNumerator / secondDenominator +
        thirdNumerator / thirdDenominator =
      (firstNumerator / firstDenominator) *
        (secondNumerator / secondDenominator) *
        (thirdNumerator / thirdDenominator)
  apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
  calc
    (firstNumerator / firstDenominator +
          secondNumerator / secondDenominator +
          thirdNumerator / thirdDenominator) * denominator =
      ((firstNumerator / firstDenominator) * firstDenominator) *
          secondDenominator * thirdDenominator +
        ((secondNumerator / secondDenominator) * secondDenominator) *
          firstDenominator * thirdDenominator +
        ((thirdNumerator / thirdDenominator) * thirdDenominator) *
          firstDenominator * secondDenominator := by
            unfold denominator
            ring1
    _ = firstNumerator * secondDenominator * thirdDenominator +
          secondNumerator * firstDenominator * thirdDenominator +
          thirdNumerator * firstDenominator * secondDenominator := by
      rw [firstCancel, secondCancel, thirdCancel]
    _ = firstNumerator * secondNumerator * thirdNumerator := numeratorIdentity
    _ =
        ((firstNumerator / firstDenominator) *
            (secondNumerator / secondDenominator) *
            (thirdNumerator / thirdDenominator)) * denominator := by
      unfold denominator
      calc
        firstNumerator * secondNumerator * thirdNumerator =
            ((firstNumerator / firstDenominator) * firstDenominator) *
              ((secondNumerator / secondDenominator) * secondDenominator) *
              ((thirdNumerator / thirdDenominator) * thirdDenominator) := by
                rw [firstCancel, secondCancel, thirdCancel]
        _ =
            ((firstNumerator / firstDenominator) *
                (secondNumerator / secondDenominator) *
                (thirdNumerator / thirdDenominator)) *
              (firstDenominator * secondDenominator * thirdDenominator) := by
                ring1
end Purelib.Geometry.Plane.Line.Turn.Triple

end
