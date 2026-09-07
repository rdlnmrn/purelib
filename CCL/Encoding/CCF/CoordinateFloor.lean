import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import mathlib.CCL.Integral

/-!
# Constructive coordinate-floor complex continued fractions

The coordinate-floor return map and its digit cone, stated entirely in the
explicit finite rational and Gaussian representations used by CCL-1.
-/

namespace CCL.CoordinateFloor

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := CCL.Integral.GaussianInt

open RFAP.ConstructiveGaussian.Gaussian
open CCL.Integral.GaussianInt

/-- Coordinatewise Gaussian-integer floor. -/
def floor (z : Gaussian) : GaussianInt :=
  ⟨RFAP.ConstructiveFraction.floor z.re,
    RFAP.ConstructiveFraction.floor z.im⟩

@[simp] theorem floor_re (z : Gaussian) :
    (floor z).re = RFAP.ConstructiveFraction.floor z.re := rfl

@[simp] theorem floor_im (z : Gaussian) :
    (floor z).im = RFAP.ConstructiveFraction.floor z.im := rfl

/-- The half-open coordinate unit square. -/
def Sq (z : Gaussian) : Prop :=
  0 ≤ z.re ∧ z.re < 1 ∧ 0 ≤ z.im ∧ z.im < 1

/-- Coordinatewise fractional part. -/
def fract (z : Gaussian) : Gaussian := z - toGaussian (floor z)

private theorem intCast_floor_le (a : Coordinate) :
    ((RFAP.ConstructiveFraction.floor a : Int) : Coordinate) ≤ a :=
  (RFAP.ConstructiveFraction.intCast_le_iff_floor _ _).2 le_rfl

private theorem lt_intCast_floor_add_one (a : Coordinate) :
    a < ((RFAP.ConstructiveFraction.floor a + 1 : Int) : Coordinate) := by
  apply lt_of_not_ge
  intro reverse
  have impossible :=
    (RFAP.ConstructiveFraction.intCast_le_iff_floor
      (RFAP.ConstructiveFraction.floor a + 1) a).1 reverse
  exact (Int.not_le_of_gt
    (Int.lt_add_one_iff.mpr (Int.le_refl _)) impossible).elim

private theorem intCast_lt_intCast_iff_direct (m n : Int) :
    ((m : Int) : Coordinate) < (n : Coordinate) ↔ m < n := by
  constructor
  · intro less
    apply Int.lt_of_not_ge
    intro reverse
    have castReverse :=
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct n m).2 reverse
    exact (not_lt_of_ge castReverse) less
  · intro less
    apply lt_of_not_ge
    intro reverse
    have integerReverse :=
      (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct n m).1 reverse
    exact (Int.not_le_of_gt less) integerReverse

/-- Every coordinatewise fractional part lies in the half-open unit square. -/
theorem fract_sq (z : Gaussian) : Sq (fract z) := by
  have realLower := intCast_floor_le z.re
  have realUpper := lt_intCast_floor_add_one z.re
  have imagLower := intCast_floor_le z.im
  have imagUpper := lt_intCast_floor_add_one z.im
  constructor
  · change 0 ≤ z.re -
      ((RFAP.ConstructiveFraction.floor z.re : Int) : Coordinate)
    exact RFAP.ConstructiveFraction.sub_nonneg_direct realLower
  constructor
  · change z.re -
      ((RFAP.ConstructiveFraction.floor z.re : Int) : Coordinate) < 1
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      realUpper (-((RFAP.ConstructiveFraction.floor z.re : Int) : Coordinate))
    calc
      z.re - ((RFAP.ConstructiveFraction.floor z.re : Int) : Coordinate) =
          z.re + -((RFAP.ConstructiveFraction.floor z.re : Int) : Coordinate) :=
        sub_eq_add_neg _ _
      _ < ((RFAP.ConstructiveFraction.floor z.re : Int) : Coordinate) + 1 +
          -((RFAP.ConstructiveFraction.floor z.re : Int) : Coordinate) := by
        simpa only [Int.cast_add, Int.cast_one] using shifted
      _ = 1 := by ring1
  constructor
  · change 0 ≤ z.im -
      ((RFAP.ConstructiveFraction.floor z.im : Int) : Coordinate)
    exact RFAP.ConstructiveFraction.sub_nonneg_direct imagLower
  · change z.im -
      ((RFAP.ConstructiveFraction.floor z.im : Int) : Coordinate) < 1
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      imagUpper (-((RFAP.ConstructiveFraction.floor z.im : Int) : Coordinate))
    calc
      z.im - ((RFAP.ConstructiveFraction.floor z.im : Int) : Coordinate) =
          z.im + -((RFAP.ConstructiveFraction.floor z.im : Int) : Coordinate) :=
        sub_eq_add_neg _ _
      _ < ((RFAP.ConstructiveFraction.floor z.im : Int) : Coordinate) + 1 +
          -((RFAP.ConstructiveFraction.floor z.im : Int) : Coordinate) := by
        simpa only [Int.cast_add, Int.cast_one] using shifted
      _ = 1 := by ring1

/-- The square return map `F(u) = γ/u - ⌊γ/u⌋`. -/
def step (u : Gaussian) : Gaussian := fract (gamma * u⁻¹)

theorem step_sq (u : Gaussian) : Sq (step u) := fract_sq _

private theorem square_lt_one_of_unit {x : Coordinate}
    (nonnegative : 0 ≤ x) (small : x < 1) : x ^ 2 < 1 := by
  by_cases zero : x = 0
  · subst x
    decide
  · have positive : 0 < x := lt_of_le_of_ne nonnegative (Ne.symm zero)
    have first := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      positive small
    calc
      x ^ 2 = x * x := pow_two x
      _ < x * 1 := first
      _ = x := by ring1
      _ < 1 := small

theorem normSq_lt_two_of_sq {z : Gaussian} (inside : Sq z) :
    normSq z < 2 := by
  rcases inside with ⟨realNonnegative, realSmall,
    imagNonnegative, imagSmall⟩
  have realSquare := square_lt_one_of_unit realNonnegative realSmall
  have imagSquare := square_lt_one_of_unit imagNonnegative imagSmall
  have sum := RFAP.ConstructiveFraction.add_lt_add_direct
    realSquare imagSquare
  simpa only [normSq, one_add_one_eq_two] using sum

/-- Decomposition into the coordinate-floor digit and square remainder. -/
theorem floor_add_step (u : Gaussian) :
    toGaussian (floor (gamma * u⁻¹)) + step u = gamma * u⁻¹ := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [step, fract, RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im] <;>
    ring1

private theorem quotient_coordinates (u : Gaussian) :
    (gamma * u⁻¹).re = (u.re + u.im) / normSq u ∧
      (gamma * u⁻¹).im = (u.re - u.im) / normSq u := by
  constructor
  · simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re, gamma,
      inv_eq, inv, RFAP.ExplicitField.div_eq_mul_inv]
    calc
      1 * (u.re * (normSq u)⁻¹) -
          1 * (-u.im * (normSq u)⁻¹) =
          u.re * (normSq u)⁻¹ + u.im * (normSq u)⁻¹ := by
        simp only [_root_.one_mul, _root_.sub_eq_add_neg,
          _root_.neg_mul, _root_.neg_neg]
      _ = (u.re + u.im) * (normSq u)⁻¹ :=
        (add_mul _ _ _).symm
  · simp only [RFAP.ConstructiveGaussian.Gaussian.mul_im, gamma,
      inv_eq, inv, RFAP.ExplicitField.div_eq_mul_inv]
    calc
      1 * (-u.im * (normSq u)⁻¹) +
          1 * (u.re * (normSq u)⁻¹) =
          -u.im * (normSq u)⁻¹ + u.re * (normSq u)⁻¹ := by
        simp only [_root_.one_mul]
      _ = u.re * (normSq u)⁻¹ + -u.im * (normSq u)⁻¹ :=
        add_comm _ _
      _ = (u.re - u.im) * (normSq u)⁻¹ := by
        rw [_root_.sub_eq_add_neg, add_mul]

private theorem coordinate_product_nonnegative {x : Coordinate}
    (nonnegative : 0 ≤ x) (small : x < 1) : 0 ≤ x * (1 - x) :=
  RFAP.ConstructiveFraction.mul_nonneg_direct nonnegative
    (RFAP.ConstructiveFraction.sub_pos_direct small).le

private theorem coordinate_product_positive {x : Coordinate}
    (positive : 0 < x) (small : x < 1) : 0 < x * (1 - x) :=
  RFAP.ConstructiveFraction.mul_pos_direct positive
    (RFAP.ConstructiveFraction.sub_pos_direct small)

private theorem quotient_real_gt_one (u : Gaussian) (nonzero : u ≠ 0)
    (inside : Sq u) : 1 < (gamma * u⁻¹).re := by
  rcases inside with ⟨realNonnegative, realSmall,
    imagNonnegative, imagSmall⟩
  have normPositive : 0 < normSq u := normSq_pos nonzero
  have realProductNonnegative :=
    coordinate_product_nonnegative realNonnegative realSmall
  have imagProductNonnegative :=
    coordinate_product_nonnegative imagNonnegative imagSmall
  have productSumPositive :
      0 < u.re * (1 - u.re) + u.im * (1 - u.im) := by
    by_cases realZero : u.re = 0
    · have imagNonzero : u.im ≠ 0 := by
        intro imagZero
        apply nonzero
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;> assumption
      have imagPositive : 0 < u.im :=
        lt_of_le_of_ne imagNonnegative (Ne.symm imagNonzero)
      exact add_pos_of_nonneg_of_pos realProductNonnegative
        (coordinate_product_positive imagPositive imagSmall)
    · have realPositive : 0 < u.re :=
        lt_of_le_of_ne realNonnegative (Ne.symm realZero)
      exact add_pos_of_pos_of_nonneg
        (coordinate_product_positive realPositive realSmall)
        imagProductNonnegative
  have normLess : normSq u < u.re + u.im := by
    apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
    calc
      (u.re + u.im) - normSq u =
          u.re * (1 - u.re) + u.im * (1 - u.im) := by
        simp only [normSq]
        ring1
      _ > 0 := productSumPositive
  rw [(quotient_coordinates u).1]
  apply (RFAP.ConstructiveFraction.lt_div_iff_pos normPositive).2
  calc
    (1 : Coordinate) * normSq u = normSq u :=
      RFAP.ConstructiveFraction.one_mul _
    _ < u.re + u.im := normLess

private theorem neg_le_self_of_nonnegative {x : Coordinate}
    (nonnegative : 0 ≤ x) : -x ≤ x := by
  have negNonpositive := RFAP.ConstructiveFraction.neg_le_neg_direct nonnegative
  simpa only [neg_zero] using negNonpositive.trans nonnegative

private theorem quotient_abs_im_le_real (u : Gaussian)
    (inside : Sq u) :
    -(gamma * u⁻¹).re ≤ (gamma * u⁻¹).im ∧
      (gamma * u⁻¹).im ≤ (gamma * u⁻¹).re := by
  rcases inside with ⟨realNonnegative, _, imagNonnegative, _⟩
  rcases quotient_coordinates u with ⟨realFormula, imagFormula⟩
  have normNonnegative := normSq_nonneg u
  by_cases zero : u = 0
  · subst u
    decide
  · have normPositive := normSq_pos zero
    rw [realFormula, imagFormula]
    constructor
    · have negSum : -(u.re + u.im) = -u.re - u.im := by
        calc
          -(u.re + u.im) = -u.im + -u.re := neg_add_rev _ _
          _ = -u.re + -u.im := add_comm _ _
          _ = -u.re - u.im := (_root_.sub_eq_add_neg _ _).symm
      rw [show -((u.re + u.im) / normSq u) =
          (-u.re - u.im) / normSq u by
          simp only [RFAP.ExplicitField.div_eq_mul_inv]
          calc
            -((u.re + u.im) * (normSq u)⁻¹) =
                (-(u.re + u.im)) * (normSq u)⁻¹ :=
              (_root_.neg_mul _ _).symm
            _ = (-u.re - u.im) * (normSq u)⁻¹ :=
              congrArg (fun value => value * (normSq u)⁻¹) negSum]
      apply (RFAP.ConstructiveFraction.div_le_iff_pos normPositive).2
      calc
        -u.re - u.im ≤ u.re - u.im :=
          RFAP.ConstructiveFraction.add_le_add_right_direct
            (neg_le_self_of_nonnegative realNonnegative) (-u.im)
        _ = ((u.re - u.im) / normSq u) * normSq u :=
          (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
            normPositive.ne').symm
    · apply (RFAP.ConstructiveFraction.div_le_iff_pos normPositive).2
      calc
        u.re - u.im = -u.im + u.re := by ring1
        _ ≤ u.im + u.re :=
          RFAP.ConstructiveFraction.add_le_add_right_direct
            (neg_le_self_of_nonnegative imagNonnegative) u.re
        _ = u.re + u.im := by ring1
        _ = ((u.re + u.im) / normSq u) * normSq u :=
          (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
            normPositive.ne').symm

/-- Every nonzero square input produces a digit in the displayed integer
cone. -/
theorem digit_cone (u : Gaussian) (nonzero : u ≠ 0) (inside : Sq u) :
    let t := floor (gamma * u⁻¹)
    1 ≤ t.re ∧ -t.re - 1 ≤ t.im ∧ t.im ≤ t.re := by
  let z := gamma * u⁻¹
  let t := floor z
  change 1 ≤ t.re ∧ -t.re - 1 ≤ t.im ∧ t.im ≤ t.re
  have realGreater : 1 < z.re := quotient_real_gt_one u nonzero inside
  have absoluteBound := quotient_abs_im_le_real u inside
  have realDigit : (1 : Int) ≤ t.re := by
    apply (RFAP.ConstructiveFraction.intCast_le_iff_floor 1 z.re).1
    exact realGreater.le
  have imagUpper : t.im ≤ t.re := by
    apply (RFAP.ConstructiveFraction.intCast_le_iff_floor t.im z.re).1
    exact (intCast_floor_le z.im).trans absoluteBound.2
  have imagFloorUpper := lt_intCast_floor_add_one z.im
  have realFloorUpper := lt_intCast_floor_add_one z.re
  have negatedRealFloorUpper :=
    RFAP.ConstructiveFraction.neg_lt_neg_direct realFloorUpper
  have castCross :
      ((-t.re - 1 : Int) : Coordinate) <
        ((t.im + 1 : Int) : Coordinate) := by
    calc
      ((-t.re - 1 : Int) : Coordinate) =
          -(((t.re + 1 : Int) : Coordinate)) := by
        simp only [Int.cast_sub, Int.cast_neg, Int.cast_add, Int.cast_one]
        ring1
      _ < -z.re := negatedRealFloorUpper
      _ ≤ z.im := absoluteBound.1
      _ < ((t.im + 1 : Int) : Coordinate) := imagFloorUpper
  have integerCross : -t.re - 1 < t.im + 1 :=
    (intCast_lt_intCast_iff_direct _ _).1 castCross
  exact ⟨realDigit, by omega, imagUpper⟩

end CCL.CoordinateFloor
