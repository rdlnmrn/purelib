import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.BlockContraction
import CCL.Arithmetic.RedundantSectors

/-!
# Completed-block contraction for redundant CCL choices

The canonical contraction theorem stores annulus and disjoint-sector proofs.
For arithmetic output those hypotheses are unnecessarily strong.  A block is
sound and has the same contraction factor whenever its displayed value has
norm at least one and its chosen representative has residual quadrance below
one half.

This parallel structure deliberately leaves the canonical theorem and parser
unchanged.  `ofCanonical` embeds every old compatible block into this wider
arithmetic layer.
-/

namespace CCL.RedundantBlockContraction

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Sector := CCL.Sectors.Sector
abbrev Proj := CCL.GaussianProjective.Proj

open RFAP.ConstructiveGaussian.Gaussian
open CCL.Sectors
open CCL.Chordal

abbrev block := CCL.BlockContraction.block
abbrev factor := CCL.BlockContraction.factor

/-- The exact hypotheses consumed by the block-contraction calculation. -/
structure CompatibleTail (sector : Sector) (tail value : Gaussian) : Prop where
  equation : gamma * tail * value = gamma * tail * sector.rep + 1
  normLower : 1 ≤ normSq value
  safe : CCL.RedundantSectors.Safe sector value

namespace CompatibleTail

/-- Every canonical compatible tail is accepted by the redundant layer. -/
theorem ofCanonical {sector : Sector} {tail value : Gaussian}
    (compatible :
      CCL.BlockContraction.CompatibleTail sector tail value) :
    CompatibleTail sector tail value :=
  { equation := compatible.equation
    normLower := compatible.band.1
    safe := CCL.RedundantSectors.safe_of_canonical
      compatible.band compatible.holds }

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
  have factorLess : 2 * normSq (value - sector.rep) < (1 : Coordinate) := by
    calc
      2 * normSq (value - sector.rep) < 2 * (1 / 2 : Coordinate) :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          (by decide) compatible.safe
      _ = 1 := by decide
  by_cases greater : 1 < normSq tail
  · exact greater
  · have tailLe : normSq tail ≤ 1 := le_of_not_gt greater
    have factorNonnegative : 0 ≤ 2 * normSq (value - sector.rep) :=
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

theorem act_weight {sector : Sector} {tail value scale : Gaussian}
    (compatible : CompatibleTail sector tail value) :
    Proj.weight
        (CCL.Mat2.act (block scale sector) (CCL.Proj.affine tail)) =
      2 * normSq tail * (1 + normSq scale * normSq value) := by
  have firstCoordinate :
      scale * gamma * sector.rep * tail + scale =
        scale * (gamma * tail * value) := by
    rw [compatible.equation]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [add_re, add_im, mul_re, mul_im, one_re, one_im] <;>
        ring1
  simp only [Proj.weight, CCL.Mat2.act, CCL.Proj.affine,
    CCL.BlockContraction.block,
    RFAP.ConstructiveGaussian.Gaussian.mul_one,
    RFAP.ConstructiveGaussian.Gaussian.add_zero]
  rw [firstCoordinate, normSq_mul, normSq_mul, normSq_mul, normSq_gamma]
  ring1

theorem factor_weight_lt {sector : Sector} {tail value scale : Gaussian}
    (compatible : CompatibleTail sector tail value) :
    (1 + normSq scale) * (1 + normSq tail) <
      Proj.weight
        (CCL.Mat2.act (block scale sector) (CCL.Proj.affine tail)) := by
  have tailGreater := compatible.tail_norm_gt_one
  have tailPositive := (by decide : (0 : Coordinate) < 1).trans tailGreater
  have scaleNormNonnegative := normSq_nonneg scale
  have onePlusTailLt : 1 + normSq tail < 2 * normSq tail := by
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
          compatible.normLower scaleNormNonnegative
  calc
    (1 + normSq scale) * (1 + normSq tail) <
        (1 + normSq scale) * (2 * normSq tail) :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (add_pos_of_pos_of_nonneg (by decide) scaleNormNonnegative)
        onePlusTailLt
    _ ≤ (1 + normSq scale * normSq value) * (2 * normSq tail) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct scalePartLe
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          tailPositive.le)
    _ = Proj.weight
        (CCL.Mat2.act (block scale sector) (CCL.Proj.affine tail)) := by
      rw [compatible.act_weight]
      ring1

end CompatibleTail

/-- The completed-block proof with exactly the weakened local hypotheses. -/
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
    Proj.weight
        (CCL.Mat2.act (block scale sector) (CCL.Proj.affine leftTail)) *
      Proj.weight
        (CCL.Mat2.act (block scale sector) (CCL.Proj.affine rightTail))
  let comparisonDenominator :=
    (1 + length) ^ 2 * ((1 + leftNorm) * (1 + rightNorm))
  have scaleNormPositive := normSq_pos scaleNonzero
  have scaleFactorPositive : 0 < 1 + length :=
    add_pos_of_pos_of_nonneg (by decide) scaleNormPositive.le
  have leftWeightLower := leftCompatible.factor_weight_lt (scale := scale)
  have rightWeightLower := rightCompatible.factor_weight_lt (scale := scale)
  have leftFactorPositive : 0 < (1 + length) * (1 + leftNorm) :=
    RFAP.ConstructiveFraction.mul_pos_direct
      scaleFactorPositive
      (add_pos_of_pos_of_nonneg (by decide) (normSq_nonneg leftTail))
  have rightFactorPositive : 0 < (1 + length) * (1 + rightNorm) :=
    RFAP.ConstructiveFraction.mul_pos_direct
      scaleFactorPositive
      (add_pos_of_pos_of_nonneg (by decide) (normSq_nonneg rightTail))
  have leftWeightPositive := leftFactorPositive.trans leftWeightLower
  have denominatorOrder : comparisonDenominator ≤ outputDenominator := by
    have strictProduct :
        ((1 + length) * (1 + leftNorm)) *
            ((1 + length) * (1 + rightNorm)) < outputDenominator := by
      calc
        ((1 + length) * (1 + leftNorm)) *
            ((1 + length) * (1 + rightNorm)) <
            Proj.weight
                (CCL.Mat2.act (block scale sector)
                  (CCL.Proj.affine leftTail)) *
              ((1 + length) * (1 + rightNorm)) :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
            leftWeightLower rightFactorPositive
        _ < outputDenominator :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            leftWeightPositive rightWeightLower
    calc
      comparisonDenominator =
          ((1 + length) * (1 + leftNorm)) *
            ((1 + length) * (1 + rightNorm)) := by
        dsimp only [comparisonDenominator]
        ring1
      _ ≤ outputDenominator := strictProduct.le
  have comparisonPositive : 0 < comparisonDenominator := by
    dsimp only [comparisonDenominator]
    exact RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.pow_pos_direct
        scaleFactorPositive 2)
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
    CCL.BlockContraction.block_det, normSq_neg, normSq_mul,
    normSq_gamma, chordalSq_affine]
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

/-- Redundant completed blocks retain the canonical uniform half contraction. -/
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
        factor scale *
          chordalSq (CCL.Proj.affine leftTail)
            (CCL.Proj.affine rightTail) :=
      affine_contraction scaleNonzero leftCompatible rightCompatible
    _ ≤ (1 / 2 : Coordinate) *
        chordalSq (CCL.Proj.affine leftTail) (CCL.Proj.affine rightTail) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (CCL.BlockContraction.factor_le_half scale)
        (chordalSq_nonneg _ _)

/-! ## Projective terminal tails -/

/-- Every displayed sector representative has squared norm at least one. -/
theorem rep_norm_lower (sector : Sector) :
    (1 : Coordinate) ≤ normSq sector.rep := by
  cases sector <;> decide

/-- Exact output weight of the formal projective tail `ω`. -/
theorem act_omega_weight (scale : Gaussian) (sector : Sector) :
    Proj.weight (CCL.Mat2.act (block scale sector) CCL.Proj.omega) =
      2 * (1 + normSq scale * normSq sector.rep) := by
  simp only [Proj.weight, CCL.Mat2.act, CCL.Proj.omega,
    CCL.BlockContraction.block,
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

/-- Redundant contraction between one compatible affine continuation and
the exact projective no-return tail. -/
theorem affine_omega_contraction {sector : Sector} {tail value scale : Gaussian}
    (_scaleNonzero : scale ≠ 0)
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
  have affineLower := compatible.factor_weight_lt (scale := scale)
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
    CCL.BlockContraction.block_det, normSq_neg, normSq_mul,
    normSq_gamma, chordalSq_omega]
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

/-- A redundant compatible tail is either affine or the formal projective
terminal.  The latter is the finite semantics of an indefinitely padded
exact residual. -/
inductive Tail (sector : Sector) where
  | omega
  | affine (tail value : Gaussian) (compatible : CompatibleTail sector tail value)

namespace Tail

def point {sector : Sector} : Tail sector → Proj
  | .omega => CCL.Proj.omega
  | .affine tail _ _ => CCL.Proj.affine tail

/-- A redundant safe value has a total projective continuation: exact sector
representatives use `ω`, while every nonzero residual uses its displayed
affine reciprocal.  The branch is a rational equality test on the supplied
finite value, not an equality test on a completed name. -/
def ofSafe (sector : Sector) (value : Gaussian)
    (normLower : 1 ≤ normSq value)
    (safe : CCL.RedundantSectors.Safe sector value) : Tail sector := by
  let residual := value - sector.rep
  if residualZero : residual = 0 then
    exact .omega
  else
    let tail := (gamma * residual)⁻¹
    have productNonzero : gamma * residual ≠ 0 :=
      mul_ne_zero_direct (by decide) residualZero
    have cancellation : gamma * tail * residual = 1 := by
      calc
        gamma * tail * residual = (gamma * residual) * (gamma * residual)⁻¹ := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [tail, mul_re, mul_im] <;> ring1
        _ = 1 :=
          RFAP.CanonicalGaussian.Gaussian.mul_inv_cancel _ productNonzero
    exact .affine tail value
      { equation := by
          have decomposition : value = sector.rep + residual := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [residual, sub_re, sub_im, add_re, add_im] <;> ring1
          calc
            gamma * tail * value =
                gamma * tail * (sector.rep + residual) := by rw [decomposition]
            _ = gamma * tail * sector.rep + gamma * tail * residual := by
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                simp only [add_re, add_im, mul_re, mul_im] <;> ring1
            _ = gamma * tail * sector.rep + 1 := by rw [cancellation]
        normLower := normLower
        safe := safe }

/-- The projective continuation models exactly the displayed normalized
value in both its affine and terminal branches. -/
def ModelsValue {sector : Sector} (tail : Tail sector)
    (value : Gaussian) : Prop :=
  match tail with
  | .omega => value = sector.rep
  | .affine _ storedValue _ => storedValue = value

theorem ofSafe_models (sector : Sector) (value : Gaussian)
    (normLower : 1 ≤ normSq value)
    (safe : CCL.RedundantSectors.Safe sector value) :
    (ofSafe sector value normLower safe).ModelsValue value := by
  unfold ofSafe
  dsimp only
  split
  · rename_i residualZero
    simpa only [ModelsValue] using sub_eq_zero.mp residualZero
  · simp only [ModelsValue]

/-- The total tail has the single homogeneous formula
`[1 : γ(value-s)]`.  This avoids branching on residual equality when a
progressive cursor carries the projective tail through unary padding. -/
theorem ofSafe_point_equivalent_homogeneous
    (sector : Sector) (value : Gaussian)
    (normLower : 1 ≤ normSq value)
    (safe : CCL.RedundantSectors.Safe sector value) :
    (ofSafe sector value normLower safe).point.Equivalent
      ⟨1, gamma * (value - sector.rep)⟩ := by
  unfold ofSafe
  dsimp only
  split
  · rename_i residualZero
    simp only [point, CCL.Proj.Equivalent, CCL.Proj.omega]
    rw [residualZero, RFAP.ConstructiveGaussian.Gaussian.mul_zero]
  · rename_i residualNonzero
    let residual := value - sector.rep
    let product := gamma * residual
    have productNonzero : product ≠ 0 :=
      mul_ne_zero_direct (by decide) residualNonzero
    change product⁻¹ * product = 1 * 1
    rw [RFAP.ConstructiveGaussian.Gaussian.mul_one]
    exact RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel
      product productNonzero

/-- Exact reconstruction by an ordinary regular block needs only the
redundant tail equation; canonical annulus membership is irrelevant. -/
theorem regularBlock_act_equivalent {sector : Sector} (exponent : Nat)
    (tail : Tail sector) (value target : Gaussian)
    (models : tail.ModelsValue value)
    (targetIdentity : natPow gamma exponent * value = target) :
    (CCL.Mat2.act (CCL.Decoder.regularBlock exponent sector)
      tail.point).Equivalent (CCL.Proj.affine target) := by
  cases tail with
  | omega =>
      rw [targetIdentity.symm, models]
      dsimp only [CCL.Proj.Equivalent, point, CCL.Mat2.act,
        CCL.Decoder.regularBlock, CCL.Proj.omega,
        CCL.Proj.affine]
      rw [natPow_succ]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, mul_re, mul_im, zero_re, zero_im,
          one_re, one_im] <;> ring1
  | affine tail storedValue compatible =>
      rw [models] at compatible
      rw [targetIdentity.symm]
      dsimp only [CCL.Proj.Equivalent, point, CCL.Mat2.act,
        CCL.Decoder.regularBlock, CCL.Proj.affine]
      simp only [RFAP.ConstructiveGaussian.Gaussian.mul_one,
        RFAP.ConstructiveGaussian.Gaussian.add_zero]
      change
        natPow gamma (exponent + 1) * sector.rep * tail +
            natPow gamma exponent =
          (natPow gamma exponent * value) * (gamma * tail)
      rw [natPow_succ]
      calc
        natPow gamma exponent * gamma * sector.rep * tail +
            natPow gamma exponent =
            natPow gamma exponent * (gamma * tail * sector.rep + 1) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [add_re, add_im, mul_re, mul_im, one_re, one_im] <;>
            ring1
        _ = natPow gamma exponent * (gamma * tail * value) := by
          rw [compatible.equation]
        _ = (natPow gamma exponent * value) * (gamma * tail) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [mul_re, mul_im] <;> ring1

/-- Exact reconstruction by the distinguished initial-low block under the
same redundant tail predicate. -/
theorem lowBlock_act_equivalent {sector : Sector} (exponent : Nat)
    (tail : Tail sector) (value target : Gaussian)
    (models : tail.ModelsValue value)
    (sourceIdentity : value = natPow gamma exponent * target) :
    (CCL.Mat2.act (CCL.Decoder.lowBlock exponent sector)
      tail.point).Equivalent (CCL.Proj.affine target) := by
  cases tail with
  | omega =>
      rw [models] at sourceIdentity
      dsimp only [CCL.Proj.Equivalent, point, CCL.Mat2.act,
        CCL.Decoder.lowBlock, CCL.Proj.omega, CCL.Proj.affine]
      rw [sourceIdentity, natPow_succ]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, mul_re, mul_im, zero_re, zero_im,
          one_re, one_im] <;> ring1
  | affine tail storedValue compatible =>
      rw [models] at compatible
      dsimp only [CCL.Proj.Equivalent, point, CCL.Mat2.act,
        CCL.Decoder.lowBlock, CCL.Proj.affine]
      simp only [RFAP.ConstructiveGaussian.Gaussian.mul_one,
        RFAP.ConstructiveGaussian.Gaussian.add_zero]
      change gamma * sector.rep * tail + 1 =
        target * (natPow gamma (exponent + 1) * tail)
      rw [natPow_succ]
      calc
        gamma * sector.rep * tail + 1 =
            gamma * tail * sector.rep + 1 := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [add_re, add_im, mul_re, mul_im, one_re, one_im] <;>
            ring1
        _ = gamma * tail * value := compatible.equation.symm
        _ = target * (natPow gamma exponent * gamma * tail) := by
          rw [sourceIdentity]
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [mul_re, mul_im] <;> ring1

theorem point_valid {sector : Sector} (tail : Tail sector) :
    CCL.Chordal.Proj.HasNonzeroCoordinate tail.point := by
  cases tail with
  | omega => exact CCL.Chordal.Proj.omega_hasNonzeroCoordinate
  | affine value source compatible =>
      exact CCL.Chordal.Proj.affine_hasNonzeroCoordinate value

/-- Full redundant contraction, including all affine/projective terminal
pairs. -/
theorem contraction {sector : Sector} (scale : Gaussian) (scaleNonzero : scale ≠ 0)
    (left right : Tail sector) :
    chordalSq (CCL.Mat2.act (block scale sector) left.point)
        (CCL.Mat2.act (block scale sector) right.point) ≤
      factor scale * chordalSq left.point right.point := by
  cases left with
  | omega =>
      cases right with
      | omega =>
          simp only [point]
          rw [CCL.Chordal.chordalSq_eq_zero_of_equivalent rfl,
            CCL.Chordal.chordalSq_eq_zero_of_equivalent rfl,
            RFAP.ConstructiveFraction.mul_zero_direct]
      | affine tail value compatible =>
          simp only [point]
          rw [chordalSq_comm
            (CCL.Mat2.act (block scale sector) CCL.Proj.omega)
            (CCL.Mat2.act (block scale sector) (CCL.Proj.affine tail)),
            chordalSq_comm CCL.Proj.omega (CCL.Proj.affine tail)]
          exact affine_omega_contraction scaleNonzero compatible
  | affine tail value compatible =>
      cases right with
      | omega =>
          simp only [point]
          exact affine_omega_contraction scaleNonzero compatible
      | affine rightTail rightValue rightCompatible =>
          simp only [point]
          exact affine_contraction scaleNonzero compatible rightCompatible

theorem contraction_half {sector : Sector} (scale : Gaussian)
    (scaleNonzero : scale ≠ 0) (left right : Tail sector) :
    chordalSq (CCL.Mat2.act (block scale sector) left.point)
        (CCL.Mat2.act (block scale sector) right.point) ≤
      (1 / 2 : Coordinate) * chordalSq left.point right.point := by
  exact (contraction scale scaleNonzero left right).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      (CCL.BlockContraction.factor_le_half scale)
      (chordalSq_nonneg _ _))

end Tail

/-! ## Finite redundant cylinders -/

inductive BlockKind where
  | regular
  | initialLow
deriving DecidableEq, Repr

/-- A completed raw block interpreted with the redundant safe-sector
predicate.  Its word and matrix are still the ordinary CCL ones. -/
structure Block where
  kind : BlockKind
  exponent : Nat
  sector : Sector
deriving DecidableEq, Repr

namespace Block

def word (entry : Block) : List Bool :=
  match entry.kind with
  | .regular => CCL.Decoder.regularWord entry.exponent entry.sector
  | .initialLow => CCL.Decoder.lowWord entry.exponent entry.sector

def matrix (entry : Block) : CCL.GaussianProjective.Mat2 :=
  match entry.kind with
  | .regular => CCL.Decoder.regularBlock entry.exponent entry.sector
  | .initialLow => CCL.Decoder.lowBlock entry.exponent entry.sector

/-- Every redundant block uses an ordinary invertible CCL decoder matrix. -/
theorem matrix_det_ne (entry : Block) :
    CCL.Chordal.Mat2.det entry.matrix ≠ 0 := by
  cases entry with
  | mk kind exponent sector =>
      cases kind with
      | regular =>
          rw [matrix, CCL.Decoder.regularBlock_det]
          exact neg_ne_zero_direct
            (natPow_ne_zero_direct gamma (by decide) (exponent + 1))
      | initialLow =>
          rw [matrix, CCL.Decoder.lowBlock_det]
          exact neg_ne_zero_direct
            (natPow_ne_zero_direct gamma (by decide) (exponent + 1))

/-- Both ordinary block matrices retain the same half contraction under the
weakened redundant compatibility predicate. -/
theorem contraction_half (entry : Block)
    (left right : Tail entry.sector) :
    chordalSq (CCL.Mat2.act entry.matrix left.point)
        (CCL.Mat2.act entry.matrix right.point) ≤
      (1 / 2 : Coordinate) * chordalSq left.point right.point := by
  cases entry with
  | mk kind exponent sector =>
      cases kind with
      | regular =>
          rw [matrix, CCL.BlockContraction.regularBlock_eq_block]
          exact Tail.contraction_half (natPow gamma exponent)
            (natPow_ne_zero_direct gamma (by decide) exponent) left right
      | initialLow =>
          rw [matrix,
            CCL.BlockContraction.lowBlock_eq_scaledBlock,
            CCL.BlockContraction.chordalSq_act_scaleMatrix
              (natPow gamma exponent)
              (natPow_ne_zero_direct gamma (by decide) exponent)]
          exact Tail.contraction_half (natPow gamma exponent)⁻¹
            (inv_ne_zero_direct
              (natPow_ne_zero_direct gamma (by decide) exponent)) left right

end Block

def rawWord : List Block → List Bool
  | [] => []
  | entry :: remaining => entry.word ++ rawWord remaining

/-- A finite projective realization of all displayed redundant blocks. -/
inductive Realizes : (blocks : List Block) → Proj → Type where
  | done (point : Proj)
      (valid : CCL.Chordal.Proj.HasNonzeroCoordinate point) :
      Realizes [] point
  | step {remaining : List Block} (entry : Block)
      (tail : Tail entry.sector)
      (rest : Realizes remaining tail.point) :
      Realizes (entry :: remaining) (CCL.Mat2.act entry.matrix tail.point)

namespace Realizes

/-- Every finite redundant cylinder realization is a valid homogeneous
point. -/
theorem valid {blocks : List Block} {point : Proj}
    (realizes : Realizes blocks point) :
    CCL.Chordal.Proj.HasNonzeroCoordinate point := by
  cases realizes with
  | done point pointValid => exact pointValid
  | step entry tail rest =>
      exact CCL.Chordal.Mat2.act_hasNonzeroCoordinate
        entry.matrix_det_ne tail.point_valid

/-- Redundant completed blocks shrink pairwise squared-chordal diameter by
the same dyadic factor as canonical blocks, including no-return terminals. -/
theorem chordalSq_le_half_pow
    {blocks : List Block} {left right : Proj}
    (leftRealizes : Realizes blocks left)
    (rightRealizes : Realizes blocks right) :
    chordalSq left right ≤ (1 / 2 : Coordinate) ^ blocks.length := by
  induction leftRealizes generalizing right with
  | done left leftValid =>
      cases rightRealizes with
      | done right rightValid =>
          rw [List.length_nil, pow_zero]
          exact CCL.Chordal.chordalSq_le_one leftValid rightValid
  | @step remaining entry leftTail leftRest inductionHypothesis =>
      cases rightRealizes with
      | step _ rightTail rightRest =>
          calc
            chordalSq (CCL.Mat2.act entry.matrix leftTail.point)
                (CCL.Mat2.act entry.matrix rightTail.point) ≤
                (1 / 2 : Coordinate) *
                  chordalSq leftTail.point rightTail.point :=
              entry.contraction_half leftTail rightTail
            _ ≤ (1 / 2 : Coordinate) *
                (1 / 2 : Coordinate) ^ remaining.length :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                (inductionHypothesis rightRest) (by decide)
            _ = (1 / 2 : Coordinate) ^ (entry :: remaining).length := by
              rw [List.length_cons, pow_succ]
              ring1

end Realizes

/-! ## Projectively coherent redundant realizations

Progressive arithmetic carries homogeneous residual tails, while the local
contraction proof chooses either an affine reciprocal or `omega`.  The two
are projectively equivalent but generally not definitionally equal.  The
following relation records those finite equivalences explicitly; it is the
trace-friendly counterpart of `Realizes`, not a change to the bitstream. -/

/-- A finite redundant cylinder realization allowing an explicit projective
change of representative between successive ordinary blocks. -/
inductive ProjectiveRealizes : (blocks : List Block) → Proj → Prop where
  | done (point : Proj)
      (valid : CCL.Chordal.Proj.HasNonzeroCoordinate point) :
      ProjectiveRealizes [] point
  | step {remaining : List Block} {point inner : Proj} (entry : Block)
      (tail : Tail entry.sector)
      (pointValid : CCL.Chordal.Proj.HasNonzeroCoordinate point)
      (outputEquivalent : point.Equivalent
        (CCL.Mat2.act entry.matrix tail.point))
      (tailEquivalent : tail.point.Equivalent inner)
      (rest : ProjectiveRealizes remaining inner) :
      ProjectiveRealizes (entry :: remaining) point

namespace ProjectiveRealizes

theorem valid {blocks : List Block} {point : Proj}
    (realizes : ProjectiveRealizes blocks point) :
    CCL.Chordal.Proj.HasNonzeroCoordinate point := by
  cases realizes with
  | done point pointValid => exact pointValid
  | step entry tail pointValid outputEquivalent tailEquivalent rest =>
      exact pointValid

/-- Change only the displayed homogeneous representative at the outside of
a certified redundant realization. -/
theorem ofEquivalent {blocks : List Block} {left right : Proj}
    (leftValid : CCL.Chordal.Proj.HasNonzeroCoordinate left)
    (equivalent : left.Equivalent right)
    (realizes : ProjectiveRealizes blocks right) :
    ProjectiveRealizes blocks left := by
  cases realizes with
  | done point pointValid => exact .done left leftValid
  | @step remaining point inner entry tail pointValid outputEquivalent
      tailEquivalent rest =>
      have imageValid :=
        CCL.Chordal.Mat2.act_hasNonzeroCoordinate
          entry.matrix_det_ne tail.point_valid
      exact .step entry tail leftValid
        (CCL.Chordal.Proj.equivalent_trans
          equivalent outputEquivalent pointValid imageValid)
        tailEquivalent rest

/-- Projectively coherent redundant cylinders retain the same dyadic
diameter bound as the definitionally aligned form. -/
theorem chordalSq_le_half_pow
    {blocks : List Block} {left right : Proj}
    (leftRealizes : ProjectiveRealizes blocks left)
    (rightRealizes : ProjectiveRealizes blocks right) :
    chordalSq left right ≤ (1 / 2 : Coordinate) ^ blocks.length := by
  induction leftRealizes generalizing right with
  | done left leftValid =>
      cases rightRealizes with
      | done right rightValid =>
          rw [List.length_nil, pow_zero]
          exact CCL.Chordal.chordalSq_le_one
            leftValid rightValid
  | @step remaining left inner entry leftTail leftValid leftOutputEquivalent
      leftTailEquivalent leftRest inductionHypothesis =>
      cases rightRealizes with
      | @step _ right rightInner _ rightTail rightValid
          rightOutputEquivalent rightTailEquivalent rightRest =>
          have leftTailValid := leftTail.point_valid
          have rightTailValid := rightTail.point_valid
          have leftImageValid :=
            CCL.Chordal.Mat2.act_hasNonzeroCoordinate
              entry.matrix_det_ne leftTailValid
          have rightImageValid :=
            CCL.Chordal.Mat2.act_hasNonzeroCoordinate
              entry.matrix_det_ne rightTailValid
          have inputIdentity :
              chordalSq leftTail.point rightTail.point =
                chordalSq inner rightInner := by
            calc
              chordalSq leftTail.point rightTail.point =
                  chordalSq inner rightTail.point :=
                CCL.Chordal.chordalSq_eq_of_equivalent_left
                  leftTailValid leftRest.valid leftTailEquivalent
                    rightTail.point
              _ = chordalSq inner rightInner :=
                CCL.Chordal.chordalSq_eq_of_equivalent_right
                  rightTailValid rightRest.valid rightTailEquivalent inner
          have outputIdentity :
              chordalSq left right =
                chordalSq
                  (CCL.Mat2.act entry.matrix leftTail.point)
                  (CCL.Mat2.act entry.matrix rightTail.point) := by
            calc
              chordalSq left right =
                  chordalSq
                    (CCL.Mat2.act entry.matrix leftTail.point) right :=
                CCL.Chordal.chordalSq_eq_of_equivalent_left
                  leftValid leftImageValid leftOutputEquivalent right
              _ = chordalSq
                  (CCL.Mat2.act entry.matrix leftTail.point)
                  (CCL.Mat2.act entry.matrix rightTail.point) :=
                CCL.Chordal.chordalSq_eq_of_equivalent_right
                  rightValid rightImageValid rightOutputEquivalent _
          calc
            chordalSq left right =
                chordalSq
                  (CCL.Mat2.act entry.matrix leftTail.point)
                  (CCL.Mat2.act entry.matrix rightTail.point) := outputIdentity
            _ ≤ (1 / 2 : Coordinate) *
                chordalSq leftTail.point rightTail.point :=
              entry.contraction_half leftTail rightTail
            _ = (1 / 2 : Coordinate) *
                chordalSq inner rightInner := by rw [inputIdentity]
            _ ≤ (1 / 2 : Coordinate) *
                (1 / 2 : Coordinate) ^ remaining.length :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                (inductionHypothesis rightRest) (by decide)
            _ = (1 / 2 : Coordinate) ^
                (entry :: remaining).length := by
              rw [List.length_cons, pow_succ]
              ring1

end ProjectiveRealizes

end CCL.RedundantBlockContraction
