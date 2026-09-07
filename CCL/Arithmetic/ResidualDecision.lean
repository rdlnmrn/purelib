import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Arithmetic.Bihomographic

/-!
# Finite residual-small-or-apart decisions

After a redundant sector is emitted, an arithmetic result may equal the
sector representative without that equality being decidable from opaque
input names.  The controller therefore never asks for equality.  At a fixed
positive residual threshold, a sufficiently fine rational ball either proves
that every realization is small enough to justify unary padding, or supplies
a positive norm lower bound making affine inversion sound.
-/

namespace CCL.ResidualDecision

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Ball := CCL.ArithmeticEnclosures.Ball

open RFAP.ConstructiveGaussian.Gaussian

/-- Finite upper-bound certificate for every realization of a ball. -/
def SmallBall (ball : Ball) (target : Coordinate) : Prop :=
  2 * (ball.radiusSq + normSq ball.center) < target

instance smallBallDecidable (ball : Ball) (target : Coordinate) :
    Decidable (SmallBall ball target) := by
  unfold SmallBall
  infer_instance

theorem normSq_lt_of_contains {ball : Ball} {target : Coordinate}
    (small : SmallBall ball target) {value : Gaussian}
    (inside : ball.Contains value) : normSq value < target := by
  have decomposition :
      value = (value - ball.center) + ball.center := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  rw [decomposition]
  exact (normSq_add_le_two (value - ball.center) ball.center).trans_lt
    (lt_of_le_of_lt
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add inside le_rfl) (by decide)) small)

/-- A centre separated from its own squared error yields an explicit lower
norm for every realization. -/
def apartOfCenter (ball : Ball)
    (separated : 2 * ball.radiusSq < normSq ball.center) :
    CCL.ArithmeticEnclosures.Ball.Apart ball := by
  let lowerSq := normSq ball.center / 2 - ball.radiusSq
  have lowerPositive : 0 < lowerSq := by
    apply RFAP.ConstructiveFraction.sub_pos_direct
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := (2 : Coordinate)) _ (by decide)
    calc
      ball.radiusSq * 2 = 2 * ball.radiusSq :=
        RFAP.ConstructiveFraction.mul_comm _ _
      _ < normSq ball.center := separated
      _ = (normSq ball.center / 2) * 2 :=
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne
          (normSq ball.center) 2 (by decide)).symm
  exact
    { lowerSq := lowerSq
      positive := lowerPositive
      lower := by
        intro value inside
        have errorNorm : normSq (ball.center - value) ≤ ball.radiusSq := by
          have negDifference :
              ball.center - value = -(value - ball.center) := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
          rw [negDifference, normSq_neg]
          exact inside
        have decomposition :
            ball.center = (ball.center - value) + value := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [sub_re, sub_im, add_re, add_im] <;> ring1
        have centerUpper : normSq ball.center ≤
            2 * (ball.radiusSq + normSq value) := by
          rw [decomposition]
          exact (normSq_add_le_two (ball.center - value) value).trans
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (add_le_add errorNorm le_rfl) (by decide))
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
          (c := (2 : Coordinate)) _ (by decide)
        calc
          lowerSq * 2 =
              (normSq ball.center / 2) * 2 - ball.radiusSq * 2 := by
            dsimp only [lowerSq]
            ring1
          _ = normSq ball.center - 2 * ball.radiusSq := by
            have cancelled :
                (normSq ball.center / 2) * 2 = normSq ball.center :=
              RFAP.ConstructiveFraction.div_mul_cancel_of_ne
                (normSq ball.center) 2 (by decide)
            calc
              (normSq ball.center / 2) * 2 - ball.radiusSq * 2 =
                  normSq ball.center - ball.radiusSq * 2 :=
                congrArg (fun coordinate =>
                  coordinate - ball.radiusSq * 2) cancelled
              _ = normSq ball.center - 2 * ball.radiusSq := by ring1
          _ ≤ 2 * normSq value := by
            apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
              (c := 2 * ball.radiusSq)
            calc
              normSq ball.center - 2 * ball.radiusSq +
                  2 * ball.radiusSq = normSq ball.center := by ring1
              _ ≤ 2 * (ball.radiusSq + normSq value) := centerUpper
              _ = 2 * normSq value + 2 * ball.radiusSq := by ring1
          _ = normSq value * 2 :=
            RFAP.ConstructiveFraction.mul_comm _ _ }

/-- The two finite residual outcomes. -/
inductive Decision (ball : Ball) (target : Coordinate) where
  | small (certificate : SmallBall ball target)
  | apart (certificate : CCL.ArithmeticEnclosures.Ball.Apart ball)

/-- Finite zero-or-apart cover.  No equality proposition is inspected. -/
def decide (ball : Ball) (target : Coordinate) (_targetPositive : 0 < target)
    (fine : ball.radiusSq < target / 6) : Decision ball target := by
  by_cases small : SmallBall ball target
  · exact .small small
  · apply Decision.apart
    apply apartOfCenter
    by_contra notSeparated
    have centerUpper : normSq ball.center ≤ 2 * ball.radiusSq :=
      le_of_not_gt notSeparated
    have certificateUpper :
        2 * (ball.radiusSq + normSq ball.center) ≤
          6 * ball.radiusSq := by
      calc
        2 * (ball.radiusSq + normSq ball.center) ≤
            2 * (ball.radiusSq + 2 * ball.radiusSq) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add le_rfl centerUpper) (by decide)
        _ = 6 * ball.radiusSq := by ring1
    have sixRadiusLt : 6 * ball.radiusSq < target := by
      have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (by decide : (0 : Coordinate) < 6) fine
      calc
        6 * ball.radiusSq < 6 * (target / 6) := scaled
        _ = target := by
          calc
            6 * (target / 6) = (target / 6) * 6 :=
              RFAP.ConstructiveFraction.mul_comm _ _
            _ = target :=
              RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 6
                (by decide)
    have wouldBeSmall : SmallBall ball target :=
      certificateUpper.trans_lt sixRadiusLt
    exact small wouldBeSmall

/-! ## Converting a small residual into finite unary padding -/

/-- Residual quadrance which justifies `count` further unary-one bits after
the sector inversion. -/
def paddingTarget (count : Nat) : Coordinate :=
  1 / (2 : Coordinate) ^ (count + 1)

theorem paddingTarget_pos (count : Nat) : 0 < paddingTarget count :=
  RFAP.ConstructiveFraction.div_pos_direct (by decide)
    (RFAP.ConstructiveFraction.pow_pos_direct (by decide) (count + 1))

/-- A nonzero residual below the displayed target has an inverse tail large
enough for the requested unary padding. -/
theorem inverseTail_large {count : Nat} {residual : Gaussian}
    (residualNonzero : residual ≠ 0)
    (small : normSq residual < paddingTarget count) :
    (2 : Coordinate) ^ count < normSq ((gamma * residual)⁻¹) := by
  have productNonzero : gamma * residual ≠ 0 :=
    mul_ne_zero_direct (by decide) residualNonzero
  have productNormPositive := normSq_pos productNonzero
  have powerPositive : 0 < (2 : Coordinate) ^ (count + 1) :=
    RFAP.ConstructiveFraction.pow_pos_direct (by decide) (count + 1)
  have residualProduct :
      normSq residual * (2 : Coordinate) ^ (count + 1) < 1 := by
    exact (RFAP.ConstructiveFraction.lt_div_iff_pos powerPositive).1 small
  have targetProduct :
      (2 : Coordinate) ^ count * normSq (gamma * residual) < 1 := by
    rw [normSq_mul, normSq_gamma]
    calc
      (2 : Coordinate) ^ count * (2 * normSq residual) =
          normSq residual * (2 : Coordinate) ^ (count + 1) := by
        rw [pow_succ]
        ring1
      _ < 1 := residualProduct
  rw [inv_eq, normSq_inv _ productNonzero]
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
    (c := normSq (gamma * residual)) _ productNormPositive
  calc
    (2 : Coordinate) ^ count * normSq (gamma * residual) < 1 :=
      targetProduct
    _ = (normSq (gamma * residual))⁻¹ *
          normSq (gamma * residual) :=
      (RFAP.ConstructiveFraction.inv_mul_cancel _
        productNormPositive.ne').symm

/-- Every rational realization of a small residual ball has the corresponding
finite loop-tail meaning: exact zero uses the projective `omega` constructor;
every nonzero realization uses the certified large affine inverse. -/
def loopTailOfSmall {count : Nat} {ball : Ball}
    (small : SmallBall ball (paddingTarget count))
    (residual : Gaussian) (inside : ball.Contains residual) :
    CCL.TerminalPadding.LoopTail count := by
  by_cases zero : residual = 0
  · exact .omega
  · exact .affine ((gamma * residual)⁻¹)
      (inverseTail_large zero (normSq_lt_of_contains small inside))

end CCL.ResidualDecision
