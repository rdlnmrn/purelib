import mathlib.Tactic.QuotientFreeRing
import CCL.Arithmetic.Enclosures
import CCL.Arithmetic.RedundantSectors

/-!
# A finite redundant output decision for CCL arithmetic

The canonical comparison at squared norm `2` is not stable under finite
enclosures.  This module gives the arithmetic transducer a separate finite
decision.  A sufficiently accurate ball whose centre has squared norm at
least one is either wholly in the next-unary region or wholly safe for one
of the eight sector representatives.

The constants are intentionally rational and square-root-free.  Safe-sector
coverage extends through squared norm `13/6`; the unary test starts below
that bound, at `32/15` plus the displayed error.  Their positive overlap is
the finite reason the controller cannot stall at squared norm `2`.
-/

namespace CCL.RedundantOutput

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Sector := CCL.Sectors.Sector
abbrev Ball := CCL.ArithmeticEnclosures.Ball

open RFAP.ConstructiveGaussian.Gaussian

/-- Square-root-free weighted triangle inequality.  It is the identity
`15 (RHS - LHS) = N(15u-v)` followed by positivity and cancellation. -/
theorem normSq_add_le_weighted (u v : Gaussian) :
    normSq (u + v) ≤ 16 * normSq u + (16 / 15) * normSq v := by
  let difference :=
    16 * normSq u + (16 / 15) * normSq v - normSq (u + v)
  have scaledIdentity :
      15 * difference =
        (15 * u.re - v.re) ^ 2 + (15 * u.im - v.im) ^ 2 := by
    have coefficient : (15 : Coordinate) * (16 / 15) = 16 := by
      calc
        (15 : Coordinate) * (16 / 15) = (16 / 15) * 15 :=
          RFAP.ConstructiveFraction.mul_comm _ _
        _ = 16 :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne 16 15 (by decide)
    calc
      15 * difference =
          (15 * 16) * normSq u +
            (15 * (16 / 15)) * normSq v -
            15 * normSq (u + v) := by
        dsimp only [difference]
        ring1
      _ = 240 * normSq u + 16 * normSq v -
            15 * normSq (u + v) := by
        rw [coefficient]
        ring1
      _ = (15 * u.re - v.re) ^ 2 +
            (15 * u.im - v.im) ^ 2 := by
        simp only [normSq, add_re, add_im]
        ring1
  have scaledNonnegative : 0 ≤ 15 * difference := by
    rw [scaledIdentity]
    exact add_nonneg
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)
  have differenceNonnegative : 0 ≤ difference := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := (15 : Coordinate)) _ (by decide)
    calc
      0 * 15 = 0 := by ring1
      _ ≤ 15 * difference := scaledNonnegative
      _ = difference * 15 := RFAP.ConstructiveFraction.mul_comm _ _
  apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
    (c := -normSq (u + v))
  calc
    normSq (u + v) + -normSq (u + v) = 0 := by ring1
    _ ≤ difference := differenceNonnegative
    _ = (16 * normSq u + (16 / 15) * normSq v) +
          -normSq (u + v) := by
      dsimp only [difference]
      ring1

/-- The common positive slack used by the two output branches. -/
def allowance : Coordinate :=
  13 / 6 - (16 / 15) * 2

private theorem scaledTwo : (16 / 15 : Coordinate) * 2 = 32 / 15 := by
  have twoDivOne : (2 / 1 : Coordinate) = 2 := by
    calc
      (2 / 1 : Coordinate) = (2 / 1) * 1 :=
        (RFAP.ConstructiveFraction.mul_one_direct _).symm
      _ = 2 :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne 2 1 (by decide)
  calc
    (16 / 15 : Coordinate) * 2 = (16 / 15) * (2 / 1) := by rw [twoDivOne]
    _ = (16 * 2) / (15 * 1) :=
      RFAP.ConstructiveFraction.div_mul_div_direct 16 15 2 1
    _ = 32 / 15 := by
      rw [show (16 : Coordinate) * 2 = 32 by decide,
        RFAP.ConstructiveFraction.mul_one_direct]

private theorem scaledSectorBound :
    (16 / 15 : Coordinate) * (7 / 16) = 7 / 15 := by
  calc
    (16 / 15 : Coordinate) * (7 / 16) =
        (16 * 7) / (15 * 16) :=
      RFAP.ConstructiveFraction.div_mul_div_direct 16 15 7 16
    _ = (16 * 7) / (16 * 15) := by
      rw [RFAP.ConstructiveFraction.mul_comm 15 16]
    _ = 7 / 15 :=
      RFAP.ConstructiveFraction.mul_div_mul_left_direct
        16 7 15 (by decide)

theorem allowance_pos : 0 < allowance := by
  unfold allowance
  rw [scaledTwo]
  decide

theorem allowance_sector_identity :
    allowance + (16 / 15) * (7 / 16) = (1 / 2 : Coordinate) := by
  unfold allowance
  rw [scaledTwo, scaledSectorBound]
  decide

theorem unaryThreshold_add_allowance :
    (16 / 15 : Coordinate) * 2 + allowance = 13 / 6 := by
  unfold allowance
  ring1

/-- A uniform squared-error request small enough for either branch. -/
def uniformRadiusSq : Coordinate := allowance / 16

theorem uniformRadiusSq_pos : 0 < uniformRadiusSq :=
  RFAP.ConstructiveFraction.div_pos_direct allowance_pos (by decide)

theorem scaled_radius_lt_allowance {radiusSq : Coordinate}
    (small : radiusSq < uniformRadiusSq) :
    16 * radiusSq < allowance := by
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
    (by decide : (0 : Coordinate) < 16) small
  calc
    16 * radiusSq < 16 * uniformRadiusSq := scaled
    _ = allowance := by
      unfold uniformRadiusSq
      calc
        16 * (allowance / 16) = (allowance / 16) * 16 :=
          RFAP.ConstructiveFraction.mul_comm _ _
        _ = allowance :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne allowance 16
            (by decide)

/-- A finite inequality certifying that the entire ball lies in one
overlapping safe sector. -/
def SafeBall (sector : Sector) (ball : Ball) : Prop :=
  16 * ball.radiusSq +
      (16 / 15) * normSq (ball.center - sector.rep) < 1 / 2

instance safeBallDecidable (sector : Sector) (ball : Ball) :
    Decidable (SafeBall sector ball) := by
  unfold SafeBall
  infer_instance

theorem safe_of_contains {sector : Sector} {ball : Ball} {value : Gaussian}
    (certificate : SafeBall sector ball) (inside : ball.Contains value) :
    CCL.RedundantSectors.Safe sector value := by
  have difference :
      value - sector.rep =
        (value - ball.center) + (ball.center - sector.rep) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  have weighted := normSq_add_le_weighted
    (value - ball.center) (ball.center - sector.rep)
  unfold CCL.RedundantSectors.Safe
  rw [difference]
  exact weighted.trans_lt
    (lt_of_le_of_lt
      (add_le_add
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          inside (by decide)) le_rfl)
      certificate)

/-- Every uniformly fine ball centred in the enlarged band has a finite safe
sector certificate, selected by the original eight-row table at its rational
centre. -/
theorem safeBall_of_extendedBand {ball : Ball}
    (band : CCL.RedundantSectors.ExtendedBand ball.center)
    (small : ball.radiusSq < uniformRadiusSq) :
    SafeBall (CCL.Sectors.Sector.select ball.center) ball := by
  have scaledRadius := scaled_radius_lt_allowance small
  have residual :=
    CCL.RedundantSectors.extendedBand_residual_le_seven_sixteenths
      band
  unfold SafeBall
  have scaledResidual :
      (16 / 15) *
          normSq (ball.center -
            (CCL.Sectors.Sector.select ball.center).rep) ≤
        (16 / 15) * (7 / 16) :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      residual (by decide)
  calc
    16 * ball.radiusSq +
        (16 / 15) *
          normSq (ball.center -
            (CCL.Sectors.Sector.select ball.center).rep) <
        allowance + (16 / 15) * (7 / 16) :=
      calc
        16 * ball.radiusSq +
            (16 / 15) *
              normSq (ball.center -
                (CCL.Sectors.Sector.select ball.center).rep) <
            allowance +
              (16 / 15) *
                normSq (ball.center -
                  (CCL.Sectors.Sector.select ball.center).rep) :=
          RFAP.ConstructiveFraction.add_lt_add_right_direct
            scaledRadius _
        _ ≤ allowance + (16 / 15) * (7 / 16) :=
          add_le_add_right scaledResidual allowance
    _ = 1 / 2 := allowance_sector_identity

/-- A finite sufficient test that the whole ball lies strictly above the
canonical radial boundary. -/
def UnaryBall (ball : Ball) : Prop :=
  (16 / 15) * 2 + 16 * ball.radiusSq < normSq ball.center

instance unaryBallDecidable (ball : Ball) : Decidable (UnaryBall ball) := by
  unfold UnaryBall
  infer_instance

theorem normSq_gt_two_of_contains {ball : Ball} {value : Gaussian}
    (certificate : UnaryBall ball) (inside : ball.Contains value) :
    2 < normSq value := by
  have centerDifference :
      ball.center = (ball.center - value) + value := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  have errorNorm : normSq (ball.center - value) ≤ ball.radiusSq := by
    have negDifference : ball.center - value = -(value - ball.center) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
    rw [negDifference, normSq_neg]
    exact inside
  have centerUpper : normSq ball.center ≤
      16 * ball.radiusSq + (16 / 15) * normSq value := by
    rw [centerDifference]
    exact (normSq_add_le_weighted (ball.center - value) value).trans
      (add_le_add
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          errorNorm (by decide)) le_rfl)
  have scaledStrict :
      (16 / 15) * 2 < (16 / 15) * normSq value := by
    apply RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct
      (c := 16 * ball.radiusSq)
    calc
      (16 / 15) * 2 + 16 * ball.radiusSq < normSq ball.center :=
        certificate
      _ ≤ 16 * ball.radiusSq + (16 / 15) * normSq value := centerUpper
      _ = (16 / 15) * normSq value + 16 * ball.radiusSq := by ring1
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
    (c := (16 / 15 : Coordinate)) _ (by decide)
  simpa only [RFAP.ConstructiveFraction.mul_comm] using scaledStrict

/-- The two finite exact outcomes of the redundant loop controller. -/
inductive Decision (ball : Ball) where
  | unary (certificate : UnaryBall ball)
  | sector (sector : Sector) (certificate : SafeBall sector ball)

/-- Explicit finite cover: once the radius request is met and the rational
centre has squared norm at least one, a bounded comparison returns either a
sound unary branch or one of the eight sound sector branches. -/
def decide (ball : Ball) (normLower : 1 ≤ normSq ball.center)
    (small : ball.radiusSq < uniformRadiusSq) : Decision ball := by
  by_cases upper : normSq ball.center ≤ 13 / 6
  · exact .sector (CCL.Sectors.Sector.select ball.center)
      (safeBall_of_extendedBand ⟨normLower, upper⟩ small)
  · apply Decision.unary
    unfold UnaryBall
    have scaledRadius := scaled_radius_lt_allowance small
    calc
      (16 / 15) * 2 + 16 * ball.radiusSq <
          (16 / 15) * 2 + allowance :=
        add_lt_add_right scaledRadius ((16 / 15) * 2)
      _ = 13 / 6 := unaryThreshold_add_allowance
      _ < normSq ball.center := lt_of_not_ge upper

end CCL.RedundantOutput
