module

public import Purelib.Geometry.Rational.Box.Square.Centered.Separation
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # The original signed-square center and its possible sums

The retained zero outside side and its exact radius-squared margin identify
the selected signed center coordinate. Adding that center to any point in
the same original square gives a three-radius coordinate floor. The resulting
sum norm floor retains the original side witness and square.
-/

public section

namespace Purelib.Geometry.Rational.Box.Square.Centered.Separation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- Two positive original rational coordinates with equal squares are equal. -/
private theorem positive_square_eq {first last : Fraction.Rational}
    (firstPositive : 0 < first) (lastPositive : 0 < last) (squares : first ^ 2 = last ^ 2) : first = last := by
  apply Fraction.Field.mul_right_cancel_of_ne
    (Arithmetic.add_pos_of_pos_of_nonneg_direct firstPositive lastPositive.le).ne'
  calc
    first * (first + last) = first ^ 2 + first * last := by ring1
    _ = last ^ 2 + first * last := congrArg (fun value => value + first * last) squares
    _ = last * (first + last) := by ring1

/-- A positive selected center coordinate gives the original three-radius sum-coordinate floor. -/
private theorem positive_sum_square {center value radius : Fraction.Rational}
    (positive : 0 < radius) (selected : center = 2 * radius) (lower : center - radius ≤ value) :
    9 * radius ^ 2 ≤ (center + value) ^ 2 := by
  have sumLower : 3 * radius ≤ center + value := by
    calc
      _ = center + (center - radius) := by rewrite [selected]; ring1
      _ ≤ _ := Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) lower
  exact (show 9 * radius ^ 2 = (3 * radius) ^ 2 by ring1).trans_le
    (Arithmetic.pow_le_pow_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel) positive.le) sumLower 2)

/-- A negative selected center coordinate gives the same original sum-coordinate square floor. -/
private theorem negative_sum_square {center value radius : Fraction.Rational}
    (positive : 0 < radius) (selected : center = -(2 * radius)) (upper : value ≤ center + radius) :
    9 * radius ^ 2 ≤ (center + value) ^ 2 := by
  have selectedNegative : -center = 2 * radius := by rewrite [selected]; ring1
  have negativeLower : -center - radius ≤ -value :=
    (show -center - radius = -(center + radius) by ring1).trans_le
      (Arithmetic.neg_le_neg_direct upper)
  exact (positive_sum_square positive selectedNegative negativeLower).trans_eq
    (show (-center + -value) ^ 2 = (center + value) ^ 2 by ring1)

/-- The original exact center and every point of its retained signed square have a nine-radius-squared sum floor. -/
theorem center_sum_normSq_lower {center value : Canonical} (separation : Centered.Separation center)
    (inside : (Affine.centeredSquare center separation.radius separation.positive.le).Contains value) :
    9 * separation.radius ^ 2 ≤ Norm.Basic.normSq (center + value) := by
  have margin := separation.zero_margin
  cases side : separation.zero with
  | left less =>
      rewrite [side] at margin
      change ((center.re - separation.radius) - 0) ^ 2 = separation.radius ^ 2 at margin
      rewrite [show center.re - separation.radius - 0 = center.re - separation.radius by ring1] at margin
      change (0 : Fraction.Rational) < center.re - separation.radius at less
      have gap := positive_square_eq less separation.positive margin
      have selected : center.re = 2 * separation.radius := by
        calc
          center.re = (center.re - separation.radius) + separation.radius := by ring1
          _ = separation.radius + separation.radius := congrArg (fun value => value + separation.radius) gap
          _ = _ := by ring1
      have lower := positive_sum_square separation.positive selected inside.1
      change _ ≤ (center.re + value.re) ^ 2 + (center.im + value.im) ^ 2
      exact lower.trans ((show (center.re + value.re) ^ 2 = (center.re + value.re) ^ 2 + 0 by ring1).trans_le
        (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
          (Arithmetic.sq_nonneg_direct (center.im + value.im))))
  | right less =>
      rewrite [side] at margin
      change (0 - (center.re + separation.radius)) ^ 2 = separation.radius ^ 2 at margin
      change center.re + separation.radius < (0 : Fraction.Rational) at less
      have gap := positive_square_eq (Arithmetic.sub_pos_direct less) separation.positive margin
      have selected : center.re = -(2 * separation.radius) := by
        calc
          center.re = -(0 - (center.re + separation.radius)) - separation.radius := by ring1
          _ = -separation.radius - separation.radius := congrArg (fun value => -value - separation.radius) gap
          _ = _ := by ring1
      have lower := negative_sum_square separation.positive selected inside.2.1
      change _ ≤ (center.re + value.re) ^ 2 + (center.im + value.im) ^ 2
      exact lower.trans ((show (center.re + value.re) ^ 2 = (center.re + value.re) ^ 2 + 0 by ring1).trans_le
        (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
          (Arithmetic.sq_nonneg_direct (center.im + value.im))))
  | bottom less =>
      rewrite [side] at margin
      change ((center.im - separation.radius) - 0) ^ 2 = separation.radius ^ 2 at margin
      rewrite [show center.im - separation.radius - 0 = center.im - separation.radius by ring1] at margin
      change (0 : Fraction.Rational) < center.im - separation.radius at less
      have gap := positive_square_eq less separation.positive margin
      have selected : center.im = 2 * separation.radius := by
        calc
          center.im = (center.im - separation.radius) + separation.radius := by ring1
          _ = separation.radius + separation.radius := congrArg (fun value => value + separation.radius) gap
          _ = _ := by ring1
      have lower := positive_sum_square separation.positive selected inside.2.2.1
      change _ ≤ (center.re + value.re) ^ 2 + (center.im + value.im) ^ 2
      exact lower.trans ((show (center.im + value.im) ^ 2 = 0 + (center.im + value.im) ^ 2 by ring1).trans_le
        (Arithmetic.add_le_add_direct
          (Arithmetic.sq_nonneg_direct (center.re + value.re)) (Fraction.Order.Basic.le_refl _)))
  | top less =>
      rewrite [side] at margin
      change (0 - (center.im + separation.radius)) ^ 2 = separation.radius ^ 2 at margin
      change center.im + separation.radius < (0 : Fraction.Rational) at less
      have gap := positive_square_eq (Arithmetic.sub_pos_direct less) separation.positive margin
      have selected : center.im = -(2 * separation.radius) := by
        calc
          center.im = -(0 - (center.im + separation.radius)) - separation.radius := by ring1
          _ = -separation.radius - separation.radius := congrArg (fun value => -value - separation.radius) gap
          _ = _ := by ring1
      have lower := negative_sum_square separation.positive selected inside.2.2.2
      change _ ≤ (center.re + value.re) ^ 2 + (center.im + value.im) ^ 2
      exact lower.trans ((show (center.im + value.im) ^ 2 = 0 + (center.im + value.im) ^ 2 by ring1).trans_le
        (Arithmetic.add_le_add_direct
          (Arithmetic.sq_nonneg_direct (center.re + value.re)) (Fraction.Order.Basic.le_refl _)))

/-- Every point of the same original signed square has squared norm at most twenty radius squares. -/
theorem candidate_normSq_upper {center value : Canonical} (separation : Centered.Separation center)
    (inside : (Affine.centeredSquare center separation.radius separation.positive.le).Contains value) :
    Norm.Basic.normSq value ≤ 20 * separation.radius ^ 2 := by
  have deviation := Centered.centeredSquare_normSq_sub_center_le center separation.positive.le inside
  have identity : value = center + (value - center) := by ring1
  calc
    _ = Norm.Basic.normSq (center + (value - center)) := congrArg Norm.Basic.normSq identity
    _ ≤ 2 * (Norm.Basic.normSq center + Norm.Basic.normSq (value - center)) :=
      Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * (8 * separation.radius ^ 2 + 2 * separation.radius ^ 2) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct separation.norm_le deviation) (by decide +kernel)
    _ = _ := by ring1

end Purelib.Geometry.Rational.Box.Square.Centered.Separation
