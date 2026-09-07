import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.NaturalLp

/-!
# Natural-powered finite Lp geometry

Natural powers of rational separations satisfy a uniform constructive
quasi-triangle estimate.  The factor `2 ^ exponent` is intentionally coarse:
it is obtained from a finite maximum comparison and works also at exponent
zero, without roots, real exponentiation, or convexity machinery.
-/

namespace FiniteMeasure

/-- A nonnegative quantity bounded by a sum has its natural power bounded by
`2 ^ exponent` times the sum of the two component powers. -/
theorem pow_le_two_pow_mul_add
    (exponent : Nat) (value left right : Coordinate)
    (valueNonnegative : 0 ≤ value)
    (leftNonnegative : 0 ≤ left)
    (rightNonnegative : 0 ≤ right)
    (bound : value ≤ left + right) :
    value ^ exponent ≤
      (2 : Coordinate) ^ exponent *
        (left ^ exponent + right ^ exponent) := by
  have sumNonnegative : 0 ≤ left + right :=
    add_nonneg leftNonnegative rightNonnegative
  have sumLe : left + right ≤ 2 * max left right := by
    by_cases order : left ≤ right
    · rw [max_eq_right order]
      calc
        left + right ≤ right + right :=
          RFAP.ConstructiveFraction.add_le_add_direct order le_rfl
        _ = 2 * right := by ring1
    · have reverse : right ≤ left :=
        (RFAP.ConstructiveFraction.lt_of_not_ge_direct order).le
      rw [max_eq_left reverse]
      calc
        left + right ≤ left + left :=
          RFAP.ConstructiveFraction.add_le_add_direct le_rfl reverse
        _ = 2 * left := by ring1
  have valueLeTwice : value ≤ 2 * max left right :=
    bound.trans sumLe
  have valuePowerLe : value ^ exponent ≤
      (2 * max left right) ^ exponent :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      valueNonnegative valueLeTwice exponent
  have maximumPowerLe : (max left right) ^ exponent ≤
      left ^ exponent + right ^ exponent := by
    by_cases order : left ≤ right
    · rw [max_eq_right order]
      calc
        right ^ exponent = 0 + right ^ exponent := by ring1
        _ ≤ left ^ exponent + right ^ exponent :=
          RFAP.ConstructiveFraction.add_le_add_direct
            (RFAP.ConstructiveFraction.pow_nonneg_direct
              leftNonnegative exponent) le_rfl
    · have reverse : right ≤ left :=
        (RFAP.ConstructiveFraction.lt_of_not_ge_direct order).le
      rw [max_eq_left reverse]
      calc
        left ^ exponent = left ^ exponent + 0 := by ring1
        _ ≤ left ^ exponent + right ^ exponent :=
          RFAP.ConstructiveFraction.add_le_add_direct le_rfl
            (RFAP.ConstructiveFraction.pow_nonneg_direct
              rightNonnegative exponent)
  have scaledMaximumPowerLe :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      maximumPowerLe
      (RFAP.ConstructiveFraction.pow_nonneg_direct
        (by decide : (0 : Coordinate) ≤ 2) exponent)
  calc
    value ^ exponent ≤ (2 * max left right) ^ exponent := valuePowerLe
    _ = (2 : Coordinate) ^ exponent * (max left right) ^ exponent := by
      rw [mul_pow]
    _ ≤ (2 : Coordinate) ^ exponent *
          (left ^ exponent + right ^ exponent) := scaledMaximumPowerLe

/-- Natural-powered subadditivity of rational magnitude, with an explicit
constructive quasi-triangle factor. -/
theorem rationalSeparation_add_pow_le_two_pow_mul
    (exponent : Nat) (left right : Coordinate) :
    rationalSeparation (left + right) 0 ^ exponent ≤
      (2 : Coordinate) ^ exponent *
        (rationalSeparation left 0 ^ exponent +
          rationalSeparation right 0 ^ exponent) :=
  pow_le_two_pow_mul_add exponent
    (rationalSeparation (left + right) 0)
    (rationalSeparation left 0) (rationalSeparation right 0)
    (rationalSeparation_nonneg _ _)
    (rationalSeparation_nonneg _ _)
    (rationalSeparation_nonneg _ _)
    (rationalSeparation_add_zero_le left right)

/-- Natural-powered rational triangle inequality with the same explicit
factor. -/
theorem rationalSeparation_pow_triangle_le_two_pow_mul
    (exponent : Nat) (left middle right : Coordinate) :
    rationalSeparation left right ^ exponent ≤
      (2 : Coordinate) ^ exponent *
        (rationalSeparation left middle ^ exponent +
          rationalSeparation middle right ^ exponent) :=
  pow_le_two_pow_mul_add exponent
    (rationalSeparation left right)
    (rationalSeparation left middle) (rationalSeparation middle right)
    (rationalSeparation_nonneg _ _)
    (rationalSeparation_nonneg _ _)
    (rationalSeparation_nonneg _ _)
    (rationalSeparation_triangle left middle right)

namespace FiniteContent

/-- Root-free quasi-triangle inequality for every displayed natural-powered
finite Lp quantity. -/
theorem poweredLp_add_le_two_pow_mul {α : Type}
    (content : FiniteContent α) (exponent : Nat)
    (left right : α → Coordinate) :
    content.poweredLp exponent (fun item => left item + right item) ≤
      (2 : Coordinate) ^ exponent *
        (content.poweredLp exponent left +
          content.poweredLp exponent right) := by
  unfold poweredLp
  calc
    content.integral (fun item =>
        rationalSeparation (left item + right item) 0 ^ exponent) ≤
      content.integral (fun item =>
        (2 : Coordinate) ^ exponent *
          (rationalSeparation (left item) 0 ^ exponent +
            rationalSeparation (right item) 0 ^ exponent)) := by
      apply content.integral_mono
      intro atom member
      exact rationalSeparation_add_pow_le_two_pow_mul exponent
        (left atom.item) (right atom.item)
    _ = (2 : Coordinate) ^ exponent *
        (content.integral (fun item =>
            rationalSeparation (left item) 0 ^ exponent) +
          content.integral (fun item =>
            rationalSeparation (right item) 0 ^ exponent)) := by
      rw [content.integral_scale, content.integral_add]

/-- Three-observable quasi-triangle inequality for natural-powered finite Lp
distance. -/
theorem poweredLpDistance_le_two_pow_mul {α : Type}
    (content : FiniteContent α) (exponent : Nat)
    (left middle right : α → Coordinate) :
    content.poweredLpDistance exponent left right ≤
      (2 : Coordinate) ^ exponent *
        (content.poweredLpDistance exponent left middle +
          content.poweredLpDistance exponent middle right) := by
  unfold poweredLpDistance
  calc
    content.integral (fun item =>
        rationalSeparation (left item) (right item) ^ exponent) ≤
      content.integral (fun item =>
        (2 : Coordinate) ^ exponent *
          (rationalSeparation (left item) (middle item) ^ exponent +
            rationalSeparation (middle item) (right item) ^ exponent)) := by
      apply content.integral_mono
      intro atom member
      exact rationalSeparation_pow_triangle_le_two_pow_mul exponent
        (left atom.item) (middle atom.item) (right atom.item)
    _ = (2 : Coordinate) ^ exponent *
        (content.integral (fun item =>
            rationalSeparation (left item) (middle item) ^ exponent) +
          content.integral (fun item =>
            rationalSeparation (middle item) (right item) ^ exponent)) := by
      rw [content.integral_scale, content.integral_add]

end FiniteContent

namespace Distribution

theorem poweredLp_add_le_two_pow_mul {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (left right : α → Coordinate) :
    distribution.poweredLp exponent (fun item => left item + right item) ≤
      (2 : Coordinate) ^ exponent *
        (distribution.poweredLp exponent left +
          distribution.poweredLp exponent right) :=
  distribution.toFiniteContent.poweredLp_add_le_two_pow_mul
    exponent left right

theorem poweredLpDistance_le_two_pow_mul {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (left middle right : α → Coordinate) :
    distribution.poweredLpDistance exponent left right ≤
      (2 : Coordinate) ^ exponent *
        (distribution.poweredLpDistance exponent left middle +
          distribution.poweredLpDistance exponent middle right) :=
  distribution.toFiniteContent.poweredLpDistance_le_two_pow_mul
    exponent left middle right

end Distribution

end FiniteMeasure
