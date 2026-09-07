import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.Decoder

/-!
# Choice-free completed-block chordal contraction

This file proves the affine two-tail part of the companion paper's completed
CCL block contraction.  The proof is entirely cross-multiplied over explicit
fractions; no square root, limit, supremum, or inherited ordered-field
division theorem is used.
-/

namespace CCL.BlockContraction

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Sector := CCL.Sectors.Sector
abbrev Proj := CCL.GaussianProjective.Proj
abbrev Mat2 := CCL.GaussianProjective.Mat2

open RFAP.ConstructiveGaussian.Gaussian
open CCL.Sectors
open CCL.Chordal

/-- The common completed-block matrix
`A_{λ,s} = S_λ T_s I_γ`. -/
def block (scale : Gaussian) (sector : Sector) : Mat2 :=
  ⟨scale * gamma * sector.rep, scale, gamma, 0⟩

/-- The rational contraction factor `q(L)=2L/(1+L)²`. -/
def factor (scale : Gaussian) : Coordinate :=
  2 * normSq scale / (1 + normSq scale) ^ 2

/-- A displayed tail equation for one compatible completed sector.  It is the
cross-multiplied form of `value = s + 1/(γ tail)`. -/
structure CompatibleTail (sector : Sector) (tail value : Gaussian) : Prop where
  equation : gamma * tail * value = gamma * tail * sector.rep + 1
  band : Sector.Band value
  holds : sector.Holds value

namespace CompatibleTail

theorem tail_nonzero {sector : Sector} {tail value : Gaussian}
    (compatible : CompatibleTail sector tail value) : tail ≠ 0 := by
  intro tailZero
  have equation := compatible.equation
  simp only [tailZero,
    RFAP.ConstructiveGaussian.Gaussian.mul_zero,
    RFAP.ConstructiveGaussian.Gaussian.zero_mul,
    RFAP.ConstructiveGaussian.Gaussian.zero_add] at equation
  exact one_ne_zero equation.symm

theorem residual_equation {sector : Sector} {tail value : Gaussian}
    (compatible : CompatibleTail sector tail value) :
    gamma * tail * (value - sector.rep) = 1 := by
  calc
    gamma * tail * (value - sector.rep) =
        gamma * tail * value - gamma * tail * sector.rep := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
    _ = 1 := by
      rw [compatible.equation]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, add_re, add_im, one_re, one_im] <;>
          ring1

theorem norm_equation {sector : Sector} {tail value : Gaussian}
    (compatible : CompatibleTail sector tail value) :
    (2 * normSq (value - sector.rep)) * normSq tail = 1 := by
  have normEquation := congrArg normSq compatible.residual_equation
  rw [normSq_mul, normSq_mul, normSq_gamma, normSq_one] at normEquation
  calc
    (2 * normSq (value - sector.rep)) * normSq tail =
        2 * normSq tail * normSq (value - sector.rep) := by ring1
    _ = 1 := normEquation

theorem tail_norm_gt_one {sector : Sector} {tail value : Gaussian}
    (compatible : CompatibleTail sector tail value) :
    1 < normSq tail := by
  have contraction := Sector.contraction compatible.band sector compatible.holds
  have factorLess : 2 * normSq (value - sector.rep) < (1 : Coordinate) := by
    calc
      2 * normSq (value - sector.rep) < 2 * (1 / 2 : Coordinate) :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          (by decide) contraction
      _ = 1 := by decide
  by_cases greater : 1 < normSq tail
  · exact greater
  · have tailLe : normSq tail ≤ 1 := le_of_not_gt greater
    have factorNonnegative :
        0 ≤ 2 * normSq (value - sector.rep) :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (normSq_nonneg _)
    have productLe :
        (2 * normSq (value - sector.rep)) * normSq tail ≤
          (2 * normSq (value - sector.rep)) * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct tailLe
        factorNonnegative
    have oneLtOne : (1 : Coordinate) < 1 := by
      calc
        1 = (2 * normSq (value - sector.rep)) * normSq tail :=
          compatible.norm_equation.symm
        _ ≤ (2 * normSq (value - sector.rep)) * 1 := productLe
        _ = 2 * normSq (value - sector.rep) := by ring1
        _ < 1 := factorLess
    exact (lt_irrefl 1 oneLtOne).elim

/-- Exact output weight of a compatible affine tail. -/
theorem act_weight {sector : Sector} {tail value scale : Gaussian}
    (compatible : CompatibleTail sector tail value) :
    Proj.weight (CCL.Mat2.act (block scale sector) (CCL.Proj.affine tail)) =
      2 * normSq tail * (1 + normSq scale * normSq value) := by
  have firstCoordinate :
      scale * gamma * sector.rep * tail + scale =
        scale * (gamma * tail * value) := by
    rw [compatible.equation]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [add_re, add_im, mul_re, mul_im, one_re, one_im] <;>
        ring1
  simp only [Proj.weight, CCL.Mat2.act, CCL.Proj.affine, block,
    RFAP.ConstructiveGaussian.Gaussian.mul_one,
    RFAP.ConstructiveGaussian.Gaussian.add_zero]
  rw [firstCoordinate, normSq_mul, normSq_mul, normSq_mul, normSq_gamma]
  ring1

/-- One compatible output weight strictly dominates the factor needed for
the relative chordal estimate. -/
theorem factor_weight_lt {sector : Sector} {tail value scale : Gaussian}
    (scaleNonzero : scale ≠ 0)
    (compatible : CompatibleTail sector tail value) :
    (1 + normSq scale) * (1 + normSq tail) <
      Proj.weight (CCL.Mat2.act (block scale sector)
        (CCL.Proj.affine tail)) := by
  have tailGreater := compatible.tail_norm_gt_one
  have tailPositive := (by decide : (0 : Coordinate) < 1).trans tailGreater
  have scaleNormNonnegative := normSq_nonneg scale
  have scaleNormPositive := normSq_pos scaleNonzero
  have valueNormLower := compatible.band.1
  have onePlusTailLt :
      1 + normSq tail < 2 * normSq tail := by
    calc
      1 + normSq tail < normSq tail + normSq tail :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct tailGreater
          (normSq tail)
      _ = 2 * normSq tail := by ring1
  have scalePartLe :
      1 + normSq scale ≤ 1 + normSq scale * normSq value := by
    apply add_le_add le_rfl
    calc
      normSq scale = normSq scale * 1 := by ring1
      _ ≤ normSq scale * normSq value :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          valueNormLower scaleNormNonnegative
  calc
    (1 + normSq scale) * (1 + normSq tail) <
        (1 + normSq scale) * (2 * normSq tail) :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (by exact add_pos_of_pos_of_nonneg (by decide) scaleNormNonnegative)
        onePlusTailLt
    _ ≤ (1 + normSq scale * normSq value) * (2 * normSq tail) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct scalePartLe
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          tailPositive.le)
    _ = Proj.weight (CCL.Mat2.act (block scale sector)
        (CCL.Proj.affine tail)) := by
      rw [compatible.act_weight]
      ring1

end CompatibleTail

theorem block_det (scale : Gaussian) (sector : Sector) :
    CCL.Chordal.Mat2.det (block scale sector) =
      -(scale * gamma) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.Chordal.Mat2.det, block, sub_re, sub_im,
      mul_re, mul_im, neg_re, neg_im, zero_re, zero_im, gamma] <;>
    ring1

/-- The contraction factor is positive for a nonzero scale. -/
theorem factor_pos {scale : Gaussian} (scaleNonzero : scale ≠ 0) :
    0 < factor scale := by
  have scalePositive := normSq_pos scaleNonzero
  have numeratorPositive : 0 < 2 * normSq scale :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) scalePositive
  have sumPositive : 0 < 1 + normSq scale :=
    add_pos_of_pos_of_nonneg (by decide) (normSq_nonneg scale)
  have denominatorPositive : 0 < (1 + normSq scale) ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct sumPositive 2
  exact RFAP.ConstructiveFraction.div_pos_direct numeratorPositive
    denominatorPositive

/-- The elementary bound `q(L) ≤ 1/2`. -/
theorem factor_le_half (scale : Gaussian) : factor scale ≤ 1 / 2 := by
  let length := normSq scale
  have lengthNonnegative : 0 ≤ length := normSq_nonneg scale
  have sumPositive : 0 < 1 + length :=
    add_pos_of_pos_of_nonneg (by decide) lengthNonnegative
  have denominatorPositive : 0 < (1 + length) ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct sumPositive 2
  rw [factor]
  apply (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).2
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := (2 : Coordinate)) _ (by decide)
  have squareNonnegative :=
    RFAP.ConstructiveFraction.sq_nonneg_direct (1 - length)
  calc
    (2 * length) * 2 = 4 * length := by ring1
    _ ≤ 4 * length + (1 - length) ^ 2 :=
      le_add_of_nonneg_right squareNonnegative
    _ = (1 + length) ^ 2 := by ring1
    _ = ((1 / 2 : Coordinate) * (1 + length) ^ 2) * 2 := by
      calc
        (1 + length) ^ 2 = 1 * (1 + length) ^ 2 := by ring1
        _ = ((1 / 2 : Coordinate) * 2) * (1 + length) ^ 2 := by
          rw [show (1 / 2 : Coordinate) * 2 = 1 by decide]
        _ = ((1 / 2 : Coordinate) * (1 + length) ^ 2) * 2 := by ring1

/-- A completed compatible block contracts affine two-tail squared chordal
quadrance by `q(N(λ))`. -/
theorem affine_contraction {sector : Sector}
    {leftTail rightTail leftValue rightValue scale : Gaussian}
    (scaleNonzero : scale ≠ 0)
    (leftCompatible : CompatibleTail sector leftTail leftValue)
    (rightCompatible : CompatibleTail sector rightTail rightValue) :
    chordalSq
        (CCL.Mat2.act (block scale sector) (CCL.Proj.affine leftTail))
        (CCL.Mat2.act (block scale sector) (CCL.Proj.affine rightTail)) ≤
      factor scale *
        chordalSq (CCL.Proj.affine leftTail) (CCL.Proj.affine rightTail) := by
  let length := normSq scale
  let leftNorm := normSq leftTail
  let rightNorm := normSq rightTail
  let numerator := 2 * length * normSq (leftTail - rightTail)
  let outputDenominator :=
    Proj.weight (CCL.Mat2.act (block scale sector)
      (CCL.Proj.affine leftTail)) *
    Proj.weight (CCL.Mat2.act (block scale sector)
      (CCL.Proj.affine rightTail))
  let comparisonDenominator :=
    (1 + length) ^ 2 * ((1 + leftNorm) * (1 + rightNorm))
  have leftWeightLower := leftCompatible.factor_weight_lt scaleNonzero
  have rightWeightLower := rightCompatible.factor_weight_lt scaleNonzero
  have leftFactorPositive :
      0 < (1 + length) * (1 + leftNorm) :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (add_pos_of_pos_of_nonneg (by decide) (normSq_nonneg scale))
      (add_pos_of_pos_of_nonneg (by decide) (normSq_nonneg leftTail))
  have rightFactorPositive :
      0 < (1 + length) * (1 + rightNorm) :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (add_pos_of_pos_of_nonneg (by decide) (normSq_nonneg scale))
      (add_pos_of_pos_of_nonneg (by decide) (normSq_nonneg rightTail))
  have leftWeightPositive := leftFactorPositive.trans leftWeightLower
  have denominatorOrder : comparisonDenominator ≤ outputDenominator := by
    have strictProduct :
        ((1 + length) * (1 + leftNorm)) *
            ((1 + length) * (1 + rightNorm)) < outputDenominator := by
      calc
        ((1 + length) * (1 + leftNorm)) *
            ((1 + length) * (1 + rightNorm)) <
            Proj.weight (CCL.Mat2.act (block scale sector)
              (CCL.Proj.affine leftTail)) *
              ((1 + length) * (1 + rightNorm)) :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
            leftWeightLower rightFactorPositive
        _ < outputDenominator :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            leftWeightPositive rightWeightLower
    exact (by
      calc
        comparisonDenominator =
            ((1 + length) * (1 + leftNorm)) *
              ((1 + length) * (1 + rightNorm)) := by
          dsimp only [comparisonDenominator]
          ring1
        _ ≤ outputDenominator := strictProduct.le)
  have comparisonPositive : 0 < comparisonDenominator := by
    dsimp only [comparisonDenominator]
    exact RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.pow_pos_direct
        (add_pos_of_pos_of_nonneg (by decide) (normSq_nonneg scale)) 2)
      (RFAP.ConstructiveFraction.mul_pos_direct
        (add_pos_of_pos_of_nonneg (by decide) (normSq_nonneg leftTail))
        (add_pos_of_pos_of_nonneg (by decide) (normSq_nonneg rightTail)))
  have numeratorNonnegative : 0 ≤ numerator := by
    dsimp only [numerator, length]
    exact RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (normSq_nonneg scale))
      (normSq_nonneg _)
  rw [CCL.Chordal.Mat2.chordalSq_act_affine,
    block_det, normSq_neg, normSq_mul, normSq_gamma,
    chordalSq_affine, factor]
  rw [show normSq scale * 2 = 2 * normSq scale by ring1]
  change numerator / outputDenominator ≤
    (2 * length / (1 + length) ^ 2) *
      (normSq (leftTail - rightTail) /
        ((1 + leftNorm) * (1 + rightNorm)))
  calc
    numerator / outputDenominator ≤ numerator / comparisonDenominator :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        numeratorNonnegative comparisonPositive denominatorOrder
    _ = (2 * length / (1 + length) ^ 2) *
        (normSq (leftTail - rightTail) /
          ((1 + leftNorm) * (1 + rightNorm))) :=
      (RFAP.ConstructiveFraction.div_mul_div_direct
        (2 * length) ((1 + length) ^ 2)
        (normSq (leftTail - rightTail))
        ((1 + leftNorm) * (1 + rightNorm))).symm

/-- Uniform half-contraction corollary. -/
theorem affine_contraction_half {sector : Sector}
    {leftTail rightTail leftValue rightValue scale : Gaussian}
    (scaleNonzero : scale ≠ 0)
    (leftCompatible : CompatibleTail sector leftTail leftValue)
    (rightCompatible : CompatibleTail sector rightTail rightValue) :
    chordalSq
        (CCL.Mat2.act (block scale sector) (CCL.Proj.affine leftTail))
        (CCL.Mat2.act (block scale sector) (CCL.Proj.affine rightTail)) ≤
      (1 / 2 : Coordinate) *
        chordalSq (CCL.Proj.affine leftTail) (CCL.Proj.affine rightTail) := by
  calc
    chordalSq
        (CCL.Mat2.act (block scale sector) (CCL.Proj.affine leftTail))
        (CCL.Mat2.act (block scale sector) (CCL.Proj.affine rightTail)) ≤
        factor scale * chordalSq (CCL.Proj.affine leftTail)
          (CCL.Proj.affine rightTail) :=
      affine_contraction scaleNonzero leftCompatible rightCompatible
    _ ≤ (1 / 2 : Coordinate) *
        chordalSq (CCL.Proj.affine leftTail) (CCL.Proj.affine rightTail) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (factor_le_half scale)
        (chordalSq_nonneg _ _)

/-- Every sector representative has norm at least one. -/
theorem rep_norm_lower (sector : Sector) :
    (1 : Coordinate) ≤ normSq sector.rep := by
  cases sector <;> decide

/-- Exact weight of the image of the formal projective tail `ω`. -/
theorem act_omega_weight (scale : Gaussian) (sector : Sector) :
    Proj.weight (CCL.Mat2.act (block scale sector) CCL.Proj.omega) =
      2 * (1 + normSq scale * normSq sector.rep) := by
  simp only [Proj.weight, CCL.Mat2.act, CCL.Proj.omega, block,
    RFAP.ConstructiveGaussian.Gaussian.mul_one,
    RFAP.ConstructiveGaussian.Gaussian.mul_zero,
    RFAP.ConstructiveGaussian.Gaussian.add_zero, normSq_mul, normSq_gamma]
  ring1

theorem scale_factor_le_omega_weight (scale : Gaussian) (sector : Sector) :
    1 + normSq scale ≤
      Proj.weight (CCL.Mat2.act (block scale sector) CCL.Proj.omega) := by
  have scaleNonnegative := normSq_nonneg scale
  have productOrder : normSq scale ≤ normSq scale * normSq sector.rep := by
    calc
      normSq scale = normSq scale * 1 := by ring1
      _ ≤ normSq scale * normSq sector.rep :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (rep_norm_lower sector) scaleNonnegative
  have sumNonnegative :
      0 ≤ 1 + normSq scale * normSq sector.rep :=
    add_nonneg (by decide)
      (RFAP.ConstructiveFraction.mul_nonneg_direct scaleNonnegative
        (normSq_nonneg sector.rep))
  calc
    1 + normSq scale ≤ 1 + normSq scale * normSq sector.rep :=
      add_le_add le_rfl productOrder
    _ ≤ 2 * (1 + normSq scale * normSq sector.rep) := by
      calc
        1 + normSq scale * normSq sector.rep =
            1 * (1 + normSq scale * normSq sector.rep) := by ring1
        _ ≤ 2 * (1 + normSq scale * normSq sector.rep) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (by decide) sumNonnegative
    _ = Proj.weight (CCL.Mat2.act (block scale sector) CCL.Proj.omega) :=
      (act_omega_weight scale sector).symm

/-- Completed-block contraction between one compatible affine tail and the
formal terminal tail `ω`. -/
theorem affine_omega_contraction {sector : Sector} {tail value scale : Gaussian}
    (scaleNonzero : scale ≠ 0)
    (compatible : CompatibleTail sector tail value) :
    chordalSq
        (CCL.Mat2.act (block scale sector) (CCL.Proj.affine tail))
        (CCL.Mat2.act (block scale sector) CCL.Proj.omega) ≤
      factor scale * chordalSq (CCL.Proj.affine tail) CCL.Proj.omega := by
  let length := normSq scale
  let tailNorm := normSq tail
  let numerator := 2 * length
  let outputDenominator :=
    Proj.weight (CCL.Mat2.act (block scale sector) CCL.Proj.omega) *
    Proj.weight (CCL.Mat2.act (block scale sector) (CCL.Proj.affine tail))
  let comparisonDenominator := (1 + length) ^ 2 * (1 + tailNorm)
  have truncationDenominator :
      (normSq (block scale sector).a + normSq (block scale sector).c) *
          (normSq ((block scale sector).a * tail + (block scale sector).b) +
            normSq ((block scale sector).c * tail + (block scale sector).d)) =
        outputDenominator := by
    dsimp only [outputDenominator, Proj.weight, CCL.Mat2.act,
      CCL.Proj.omega, CCL.Proj.affine]
    simp only [RFAP.ConstructiveGaussian.Gaussian.mul_one,
      RFAP.ConstructiveGaussian.Gaussian.mul_zero,
      RFAP.ConstructiveGaussian.Gaussian.add_zero]
  have affineLower := compatible.factor_weight_lt scaleNonzero
  have omegaLower := scale_factor_le_omega_weight scale sector
  have scaleFactorPositive : 0 < 1 + length :=
    add_pos_of_pos_of_nonneg (by decide) (normSq_nonneg scale)
  have tailFactorPositive : 0 < 1 + tailNorm :=
    add_pos_of_pos_of_nonneg (by decide) (normSq_nonneg tail)
  have omegaWeightPositive :
      0 < Proj.weight (CCL.Mat2.act (block scale sector) CCL.Proj.omega) :=
    scaleFactorPositive.trans_le omegaLower
  have denominatorOrder : comparisonDenominator ≤ outputDenominator := by
    calc
      comparisonDenominator =
          (1 + length) * ((1 + length) * (1 + tailNorm)) := by
        dsimp only [comparisonDenominator]
        ring1
      _ ≤ Proj.weight (CCL.Mat2.act (block scale sector) CCL.Proj.omega) *
          ((1 + length) * (1 + tailNorm)) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct omegaLower
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            scaleFactorPositive.le tailFactorPositive.le)
      _ ≤ outputDenominator :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          affineLower.le omegaWeightPositive.le
  have comparisonPositive : 0 < comparisonDenominator := by
    dsimp only [comparisonDenominator]
    exact RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.pow_pos_direct scaleFactorPositive 2)
      tailFactorPositive
  have numeratorNonnegative : 0 ≤ numerator := by
    dsimp only [numerator, length]
    exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (normSq_nonneg scale)
  rw [CCL.Chordal.Mat2.chordalSq_truncation,
    block_det, normSq_neg, normSq_mul, normSq_gamma,
    chordalSq_omega, factor]
  rw [show normSq scale * 2 = 2 * normSq scale by ring1]
  rw [truncationDenominator]
  change numerator / outputDenominator ≤
    (2 * length / (1 + length) ^ 2) * (1 / (1 + tailNorm))
  calc
    numerator / outputDenominator ≤ numerator / comparisonDenominator :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        numeratorNonnegative comparisonPositive denominatorOrder
    _ = ((2 * length) * 1) /
        ((1 + length) ^ 2 * (1 + tailNorm)) := by
      dsimp only [numerator, comparisonDenominator]
      rw [RFAP.ConstructiveFraction.mul_one_direct]
    _ = (2 * length / (1 + length) ^ 2) * (1 / (1 + tailNorm)) :=
      (RFAP.ConstructiveFraction.div_mul_div_direct
        (2 * length) ((1 + length) ^ 2) 1 (1 + tailNorm)).symm

/-- A finite compatible tail is either an affine continuation with its exact
branch certificate or the formal terminal coordinate. -/
inductive Tail (sector : Sector) where
  | omega
  | affine (tail value : Gaussian) (compatible : CompatibleTail sector tail value)

namespace Tail

def point {sector : Sector} : Tail sector → Proj
  | .omega => CCL.Proj.omega
  | .affine tail _ _ => CCL.Proj.affine tail

/-- Full completed-block contraction, including affine/terminal pairs. -/
theorem contraction {sector : Sector} (scale : Gaussian) (scaleNonzero : scale ≠ 0)
    (left right : Tail sector) :
    chordalSq (CCL.Mat2.act (block scale sector) left.point)
        (CCL.Mat2.act (block scale sector) right.point) ≤
      factor scale * chordalSq left.point right.point := by
  cases left with
  | omega =>
      cases right with
      | omega =>
          change chordalSq
              (CCL.Mat2.act (block scale sector) (CCL.Proj.omega : Proj))
              (CCL.Mat2.act (block scale sector) CCL.Proj.omega) ≤
            factor scale * chordalSq (CCL.Proj.omega : Proj) CCL.Proj.omega
          have outputZero : chordalSq
              (CCL.Mat2.act (block scale sector) (CCL.Proj.omega : Proj))
              (CCL.Mat2.act (block scale sector) CCL.Proj.omega) = 0 :=
            chordalSq_eq_zero_of_equivalent rfl
          have inputZero : chordalSq (CCL.Proj.omega : Proj) CCL.Proj.omega = 0 :=
            chordalSq_eq_zero_of_equivalent rfl
          rw [outputZero, inputZero]
          rw [RFAP.ConstructiveFraction.mul_zero_direct]
      | affine tail value compatible =>
          change chordalSq
              (CCL.Mat2.act (block scale sector) (CCL.Proj.omega : Proj))
              (CCL.Mat2.act (block scale sector) (CCL.Proj.affine tail)) ≤
            factor scale * chordalSq (CCL.Proj.omega : Proj)
              (CCL.Proj.affine tail)
          rw [chordalSq_comm
            (CCL.Mat2.act (block scale sector) (CCL.Proj.omega : Proj))
            (CCL.Mat2.act (block scale sector) (CCL.Proj.affine tail)),
            chordalSq_comm (CCL.Proj.omega : Proj) (CCL.Proj.affine tail)]
          exact affine_omega_contraction scaleNonzero compatible
  | affine leftTail leftValue leftCompatible =>
      cases right with
      | omega =>
          change chordalSq
              (CCL.Mat2.act (block scale sector) (CCL.Proj.affine leftTail))
              (CCL.Mat2.act (block scale sector) (CCL.Proj.omega : Proj)) ≤
            factor scale * chordalSq (CCL.Proj.affine leftTail)
              (CCL.Proj.omega : Proj)
          exact affine_omega_contraction scaleNonzero leftCompatible
      | affine rightTail rightValue rightCompatible =>
          change chordalSq
              (CCL.Mat2.act (block scale sector) (CCL.Proj.affine leftTail))
              (CCL.Mat2.act (block scale sector) (CCL.Proj.affine rightTail)) ≤
            factor scale * chordalSq (CCL.Proj.affine leftTail)
              (CCL.Proj.affine rightTail)
          exact affine_contraction scaleNonzero leftCompatible rightCompatible

end Tail

/-- Multiply every entry of a decoder matrix by one Gaussian scalar. -/
def scaleMatrix (scalar : Gaussian) (matrix : Mat2) : Mat2 :=
  ⟨scalar * matrix.a, scalar * matrix.b,
    scalar * matrix.c, scalar * matrix.d⟩

theorem act_scaleMatrix (scalar : Gaussian) (matrix : Mat2) (point : Proj) :
    CCL.Mat2.act (scaleMatrix scalar matrix) point =
      Proj.scale scalar (CCL.Mat2.act matrix point) := by
  apply CCL.Proj.ext <;> apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.Mat2.act, scaleMatrix, Proj.scale, add_re, add_im,
      mul_re, mul_im] <;>
    ring1

theorem chordalSq_act_scaleMatrix (scalar : Gaussian)
    (scalarNonzero : scalar ≠ 0) (matrix : Mat2) (left right : Proj) :
    chordalSq (CCL.Mat2.act (scaleMatrix scalar matrix) left)
        (CCL.Mat2.act (scaleMatrix scalar matrix) right) =
      chordalSq (CCL.Mat2.act matrix left) (CCL.Mat2.act matrix right) := by
  rw [act_scaleMatrix, act_scaleMatrix,
    chordalSq_scale_left scalar scalarNonzero,
    chordalSq_scale_right scalar scalarNonzero]

theorem regularBlock_eq_block (exponent : Nat) (sector : Sector) :
    CCL.Decoder.regularBlock exponent sector =
      block (natPow gamma exponent) sector := by
  apply CCL.Mat2.ext
  · rw [CCL.Decoder.regularBlock, block, natPow_succ]
  · rfl
  · rfl
  · rfl

/-- A completed regular block contracts every compatible pair by one half. -/
theorem regularBlock_contraction_half {sector : Sector} (exponent : Nat)
    (left right : Tail sector) :
    chordalSq
        (CCL.Mat2.act (CCL.Decoder.regularBlock exponent sector)
          left.point)
        (CCL.Mat2.act (CCL.Decoder.regularBlock exponent sector)
          right.point) ≤
      (1 / 2 : Coordinate) * chordalSq left.point right.point := by
  rw [regularBlock_eq_block]
  calc
    chordalSq (CCL.Mat2.act (block (natPow gamma exponent) sector) left.point)
        (CCL.Mat2.act (block (natPow gamma exponent) sector) right.point) ≤
        factor (natPow gamma exponent) * chordalSq left.point right.point :=
      Tail.contraction (natPow gamma exponent)
        (natPow_ne_zero_direct gamma (by decide) exponent) left right
    _ ≤ (1 / 2 : Coordinate) * chordalSq left.point right.point :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (factor_le_half _) (chordalSq_nonneg _ _)

theorem lowBlock_eq_scaledBlock (exponent : Nat) (sector : Sector) :
    CCL.Decoder.lowBlock exponent sector =
      scaleMatrix (natPow gamma exponent)
        (block (natPow gamma exponent)⁻¹ sector) := by
  let power := natPow gamma exponent
  have powerNonzero : power ≠ 0 :=
    natPow_ne_zero_direct gamma (by decide) exponent
  have cancel : power * power⁻¹ = 1 :=
    RFAP.CanonicalGaussian.Gaussian.mul_inv_cancel power powerNonzero
  apply CCL.Mat2.ext
  · change gamma * sector.rep = power * (power⁻¹ * gamma * sector.rep)
    calc
      gamma * sector.rep = 1 * (gamma * sector.rep) :=
        (RFAP.ConstructiveGaussian.Gaussian.one_mul _).symm
      _ = (power * power⁻¹) * (gamma * sector.rep) := by rw [cancel]
      _ = power * (power⁻¹ * gamma * sector.rep) := by
        rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
          RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
  · change (1 : Gaussian) = power * power⁻¹
    exact cancel.symm
  · change natPow gamma (exponent + 1) = power * gamma
    rfl
  · change (0 : Gaussian) = power * 0
    exact (RFAP.ConstructiveGaussian.Gaussian.mul_zero power).symm

/-- A completed initial-low block has the same half-contraction after its
nonzero common projective rescaling is removed. -/
theorem lowBlock_contraction_half {sector : Sector} (exponent : Nat)
    (left right : Tail sector) :
    chordalSq
        (CCL.Mat2.act (CCL.Decoder.lowBlock exponent sector)
          left.point)
        (CCL.Mat2.act (CCL.Decoder.lowBlock exponent sector)
          right.point) ≤
      (1 / 2 : Coordinate) * chordalSq left.point right.point := by
  let power := natPow gamma exponent
  have powerNonzero : power ≠ 0 :=
    natPow_ne_zero_direct gamma (by decide) exponent
  have inverseNonzero : power⁻¹ ≠ 0 := inv_ne_zero_direct powerNonzero
  rw [lowBlock_eq_scaledBlock]
  rw [chordalSq_act_scaleMatrix power powerNonzero]
  calc
    chordalSq (CCL.Mat2.act (block power⁻¹ sector) left.point)
        (CCL.Mat2.act (block power⁻¹ sector) right.point) ≤
        factor power⁻¹ * chordalSq left.point right.point :=
      Tail.contraction power⁻¹ inverseNonzero left right
    _ ≤ (1 / 2 : Coordinate) * chordalSq left.point right.point :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (factor_le_half _) (chordalSq_nonneg _ _)

end CCL.BlockContraction
