module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Spread
public import Purelib.Geometry.Trigonometry.Spread.Number.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Spread

open Purelib.Geometry.Trigonometry.Spread

section
@[expose] public section

/-!
# Divine Proportions, Chapter 6: spread, cross, and twist

The ratio notions carry explicit non-null/non-perpendicular certificates for
their denominators.  They are otherwise ordinary finite field expressions.
-/

namespace Purelib.Geometry.Plane.Line.Spread.Realization

variable {K : Type*} [ExplicitField K]

/-- Theorem 34, forward clause: every spread is a spread number. -/
theorem spread_isSpreadNumber (first second : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull) :
    Number.Basic.IsSpreadNumber (Spread.spread first second firstNonNull secondNonNull) := by
  let determinant := first.a * second.b - second.a * first.b
  let dot := first.a * second.a + first.b * second.b
  let denominator := Basic.lineNorm first * Basic.lineNorm second
  have denominatorNonzero : denominator ≠ 0 :=
    Purelib.Geometry.Plane.Line.Spread.normProductNonzero first second firstNonNull secondNonNull
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ denominatorNonzero
  refine ⟨determinant * dot / denominator, ?_⟩
  have fibonacci :
      (first.a * second.b - second.a * first.b) ^ 2 +
        (first.a * second.a + first.b * second.b) ^ 2 =
      Basic.lineNorm first * Basic.lineNorm second := by
    unfold Basic.lineNorm
    ring1
  unfold Spread.spread determinant dot denominator
  simp only [ExplicitField.div_eq_mul_inv]
  rw [show 1 -
      (first.a * second.b - second.a * first.b) ^ 2 *
        (Basic.lineNorm first * Basic.lineNorm second)⁻¹ =
      (first.a * second.a + first.b * second.b) ^ 2 *
        (Basic.lineNorm first * Basic.lineNorm second)⁻¹ by
    calc
      1 - (first.a * second.b - second.a * first.b) ^ 2 *
          (Basic.lineNorm first * Basic.lineNorm second)⁻¹ =
        (Basic.lineNorm first * Basic.lineNorm second) *
            (Basic.lineNorm first * Basic.lineNorm second)⁻¹ -
          (first.a * second.b - second.a * first.b) ^ 2 *
            (Basic.lineNorm first * Basic.lineNorm second)⁻¹ := by
              rw [denominatorCancel]
      _ = (first.a * second.a + first.b * second.b) ^ 2 *
          (Basic.lineNorm first * Basic.lineNorm second)⁻¹ := by
            rw [← fibonacci]
            ring1]
  ring1

/-- Theorem 34, converse clause: the square witness constructs two concrete non-null lines whose spread is the requested
value. -/
theorem spreadNumber_realized [Nontrivial K] [DecidableEq K]
    (value root : K) (square : value * (1 - value) = root ^ 2) :
    ∃ first second : Plane.Line K,
      ∃ firstNonNull : ¬ first.IsNull,
      ∃ secondNonNull : ¬ second.IsNull,
        Spread.spread first second firstNonNull secondNonNull = value := by
  let vertical : Plane.Line K :=
    { a := 0, b := 1, c := 0,
      direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0) }
  have verticalNonNull : ¬ vertical.IsNull := by
    unfold Plane.Line.IsNull vertical
    intro normZero
    exact (one_ne_zero : (1 : K) ≠ 0) (by
      calc
        (1 : K) = 0 ^ 2 + 1 ^ 2 := by ring1
        _ = 0 := normZero)
  by_cases valueIsOne : value = 1
  · let horizontal : Plane.Line K :=
      { a := 1, b := 0, c := 0,
        direction_nonzero := Or.inl (one_ne_zero : (1 : K) ≠ 0) }
    have horizontalNonNull : ¬ horizontal.IsNull := by
      unfold Plane.Line.IsNull horizontal
      intro normZero
      exact (one_ne_zero : (1 : K) ≠ 0) (by
        calc
          (1 : K) = 1 ^ 2 + 0 ^ 2 := by ring1
          _ = 0 := normZero)
    refine ⟨vertical, horizontal, verticalNonNull, horizontalNonNull, ?_⟩
    have oneInverse : (1 : K)⁻¹ = 1 := by
      calc
        (1 : K)⁻¹ = 1 * (1 : K)⁻¹ := by rw [one_mul]
        _ = 1 := ExplicitField.mul_inv_cancel 1 one_ne_zero
    unfold Spread.spread
    rw [show
      ((vertical.a * horizontal.b - horizontal.a * vertical.b) ^ 2) =
          (1 : K) by unfold vertical horizontal; ring1]
    rw [show Basic.lineNorm vertical * Basic.lineNorm horizontal = (1 : K) by
      unfold Basic.lineNorm vertical horizontal
      ring1]
    rw [valueIsOne]
    simp only [ExplicitField.div_eq_mul_inv]
    rw [oneInverse]
    ring1
  · have differenceNonzero : 1 - value ≠ 0 := (fun {K : Type _} [ExplicitField K] {value : K}
    (notOne : value ≠ 1) => (ExplicitField.one_sub_ne_zero_of_ne_one (K := K) (value := value)
    notOne : 1 - value ≠ 0)) valueIsOne
    let target : Plane.Line K :=
      { a := root
        b := 1 - value
        c := 0
        direction_nonzero := Or.inr differenceNonzero }
    have targetNorm : Basic.lineNorm target = 1 - value := by
      unfold Basic.lineNorm target
      calc
        root ^ 2 + (1 - value) ^ 2 =
            value * (1 - value) + (1 - value) ^ 2 := by rw [← square]
        _ = 1 - value := by ring1
    have targetNonNull : ¬ target.IsNull := by
      intro targetNull
      apply differenceNonzero
      calc
        1 - value = Basic.lineNorm target := targetNorm.symm
        _ = 0 := targetNull
    refine ⟨vertical, target, verticalNonNull, targetNonNull, ?_⟩
    have differenceCancel :
        (1 - value) * (1 - value)⁻¹ = (1 : K) :=
      ExplicitField.mul_inv_cancel _ differenceNonzero
    unfold Spread.spread
    rw [show Basic.lineNorm vertical = (1 : K) by
      unfold Basic.lineNorm vertical
      ring1, targetNorm]
    unfold vertical target
    simp only [ExplicitField.div_eq_mul_inv]
    rw [one_mul]
    calc
      (0 * (1 - value) - root * 1) ^ 2 * (1 - value)⁻¹ =
          root ^ 2 * (1 - value)⁻¹ := by ring1
      _ = value * (1 - value) * (1 - value)⁻¹ := by rw [square]
      _ = value := by rw [mul_assoc, differenceCancel, mul_one]
end Purelib.Geometry.Plane.Line.Spread.Realization

end
