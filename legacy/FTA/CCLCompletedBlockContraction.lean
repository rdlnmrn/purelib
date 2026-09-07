import CCL.EncoderParserBridge
import FTA.CCLHomographicCylinder

/-!
# Uniform contraction across completed CCL decoder blocks

Each completed block maps its new outside-unit affine tail back into the
previous annulus sector.  The exact determinant/weight formula for squared
chordal distance shows that this inverse branch is `1/2`-Lipschitz in squared
chordal distance.  Iterating the parser history therefore gives a universal
geometric diameter bound for every completed raw prefix.
-/

namespace FTA
namespace CCLCompletedBlockContraction

open CCL
open CCL.GaussianRat
open FTA.CCLRawCylinderEnvelope

abbrev QI := CCL.GaussianRat

theorem normSq_blockMatrix_det (kind : RawParser.BlockKind)
    (exponent : ℕ) (sector : Sector) :
    normSq (RawParser.blockMatrix kind exponent sector).det =
      (2 : ℚ) ^ (exponent + 1) := by
  cases kind with
  | initialLow =>
      rw [RawParser.blockMatrix, CCLDecoder.lowBlock_det, normSq_neg,
        normSq_natPow, normSq_gamma]
  | initialHigh =>
      rw [RawParser.blockMatrix, CCLDecoder.regularBlock_det, normSq_neg,
        normSq_natPow, normSq_gamma]
  | loop =>
      rw [RawParser.blockMatrix, CCLDecoder.regularBlock_det, normSq_neg,
        normSq_natPow, normSq_gamma]

/-- Every completed block has enough first-column weight to dominate twice
the radial factor used in the output-growth estimate. -/
theorem two_mul_blockFactor_le_firstColumnWeight
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector) :
    2 * ((2 : ℚ) ^ exponent + 1) ≤
      CCLHomographicCylinder.firstColumnWeight
        (RawParser.blockMatrix kind exponent sector) := by
  have representativeLower : 1 ≤ normSq sector.rep := by
    cases sector <;> norm_num [Sector.rep, GaussianRat.normSq]
  have powerNonnegative : 0 ≤ (2 : ℚ) ^ exponent := by positivity
  cases kind with
  | initialLow =>
      simp only [RawParser.blockMatrix, CCLDecoder.lowBlock,
        CCLHomographicCylinder.firstColumnWeight]
      rw [normSq_mul, normSq_gamma, normSq_natPow, normSq_gamma, pow_succ]
      nlinarith
  | initialHigh =>
      simp only [RawParser.blockMatrix, CCLDecoder.regularBlock,
        CCLHomographicCylinder.firstColumnWeight]
      rw [normSq_mul, normSq_natPow, normSq_gamma, pow_succ]
      nlinarith
  | loop =>
      simp only [RawParser.blockMatrix, CCLDecoder.regularBlock,
        CCLHomographicCylinder.firstColumnWeight]
      rw [normSq_mul, normSq_natPow, normSq_gamma, pow_succ]
      nlinarith

/-- The squared determinant is uniformly dominated by the square of the
same radial factor. -/
theorem two_normSq_blockMatrix_det_le_blockFactor_sq
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector) :
    2 * normSq (RawParser.blockMatrix kind exponent sector).det ≤
      ((2 : ℚ) ^ exponent + 1) ^ 2 := by
  rw [normSq_blockMatrix_det, pow_succ]
  nlinarith [sq_nonneg ((2 : ℚ) ^ exponent - 1)]

/-- The homogeneous output weight of a completed block dominates its input
weight by the exact factor `2^k+1`. -/
theorem block_output_weight_gt
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (tail : QI)
    (denominator : RawParserSemantics.denominator
      (RawParser.blockMatrix kind exponent sector) tail ≠ 0)
    (full : RawParser.fullBlockHolds kind exponent sector
      (RatBox.homographic
        (RawParser.blockMatrix kind exponent sector) tail))
    (outside : 1 < normSq tail) :
    ((2 : ℚ) ^ exponent + 1) * (1 + normSq tail) <
      (Mat2.act (RawParser.blockMatrix kind exponent sector)
        (Proj.affine tail)).weight := by
  let previous := RatBox.homographic
    (RawParser.blockMatrix kind exponent sector) tail
  let normalized := RawParser.normalizedValue kind exponent previous
  have normalizedBand : Sector.Band normalized := by
    exact EncoderParserBridge.normalizedValue_band_of_fullBlock
      kind exponent sector previous full
  have normalizedLower : 1 ≤ normSq normalized := normalizedBand.1
  have tailNe := EncoderParserBridge.tail_ne_of_block_denominator
    kind exponent sector tail denominator
  have gammaNe : gamma ≠ 0 := by decide
  have gammaTailNe : gamma * tail ≠ 0 := mul_ne_zero gammaNe tailNe
  have gammaTailCancel : gamma * tail * inv (gamma * tail) = 1 :=
    mul_inv _ gammaTailNe
  have normalizedEq : normalized = sector.rep + inv (gamma * tail) := by
    exact EncoderParserBridge.normalizedValue_block_homographic
      kind exponent sector tail denominator
  have affineFactor :
      gamma * sector.rep * tail + 1 = gamma * tail * normalized := by
    rw [normalizedEq]
    calc
      gamma * sector.rep * tail + 1 =
          gamma * tail * sector.rep + 1 := by ring
      _ = gamma * tail * sector.rep +
          gamma * tail * inv (gamma * tail) := by rw [gammaTailCancel]
      _ = gamma * tail * (sector.rep + inv (gamma * tail)) := by ring
  let power := natPow gamma exponent
  have regularFirst :
      power * gamma * sector.rep * tail + power =
        power * (gamma * tail * normalized) := by
    rw [← affineFactor]
    ring
  have lowFirst :
      gamma * sector.rep * tail + 1 = gamma * tail * normalized :=
    affineFactor
  have tailNonnegative : 0 ≤ normSq tail := normSq_nonneg tail
  have powerNonnegative : 0 ≤ (2 : ℚ) ^ exponent := by positivity
  have inputGrowth :
      ((2 : ℚ) ^ exponent + 1) * (1 + normSq tail) <
        2 * normSq tail * ((2 : ℚ) ^ exponent + 1) := by
    have baseGrowth : 1 + normSq tail < 2 * normSq tail := by
      linarith
    have scaled := mul_lt_mul_of_pos_left baseGrowth
      (show 0 < (2 : ℚ) ^ exponent + 1 by positivity)
    nlinarith
  have normalizedScale :
      2 * normSq tail ≤ 2 * normSq tail * normSq normalized := by
    calc
      2 * normSq tail = 2 * normSq tail * 1 := by ring
      _ ≤ 2 * normSq tail * normSq normalized :=
        mul_le_mul_of_nonneg_left normalizedLower (by positivity)
  cases kind with
  | initialHigh =>
      simp only [RawParser.blockMatrix, CCLDecoder.regularBlock, Mat2.act,
        Proj.affine, natPow_succ, GaussianRat.mul_one,
        GaussianRat.add_zero, Proj.weight]
      change ((2 : ℚ) ^ exponent + 1) * (1 + normSq tail) <
        normSq (power * gamma * sector.rep * tail + power) +
          normSq (gamma * tail)
      rw [regularFirst, normSq_mul, normSq_mul, normSq_mul,
        normSq_natPow, normSq_gamma]
      apply inputGrowth.trans_le
      have scaled :=
        mul_le_mul_of_nonneg_left normalizedScale powerNonnegative
      nlinarith
  | initialLow =>
      simp only [RawParser.blockMatrix, CCLDecoder.lowBlock, Mat2.act,
        Proj.affine, GaussianRat.mul_one, GaussianRat.add_zero, Proj.weight]
      rw [lowFirst, normSq_mul, normSq_mul, normSq_mul,
        normSq_natPow, normSq_gamma, pow_succ]
      apply inputGrowth.trans_le
      nlinarith
  | loop =>
      simp only [RawParser.blockMatrix, CCLDecoder.regularBlock, Mat2.act,
        Proj.affine, natPow_succ, GaussianRat.mul_one,
        GaussianRat.add_zero, Proj.weight]
      change ((2 : ℚ) ^ exponent + 1) * (1 + normSq tail) <
        normSq (power * gamma * sector.rep * tail + power) +
          normSq (gamma * tail)
      rw [regularFirst, normSq_mul, normSq_mul, normSq_mul,
        normSq_natPow, normSq_gamma]
      apply inputGrowth.trans_le
      have scaled :=
        mul_le_mul_of_nonneg_left normalizedScale powerNonnegative
      nlinarith

private theorem scaled_fraction_le_half
    {determinant difference inputWeight outputWeight : ℚ}
    (differenceNonnegative : 0 ≤ difference)
    (inputPositive : 0 < inputWeight)
    (outputPositive : 0 < outputWeight)
    (denominatorGrowth :
      2 * determinant * inputWeight ≤ outputWeight) :
    determinant * difference / outputWeight ≤
      (1 / 2 : ℚ) * (difference / inputWeight) := by
  have core : determinant / outputWeight ≤
      (1 / 2 : ℚ) / inputWeight := by
    apply (div_le_div_iff₀ outputPositive inputPositive).2
    nlinarith
  have scaled := mul_le_mul_of_nonneg_left core differenceNonnegative
  calc
    determinant * difference / outputWeight =
        difference * (determinant / outputWeight) := by ring
    _ ≤ difference * ((1 / 2 : ℚ) / inputWeight) := scaled
    _ = (1 / 2 : ℚ) * (difference / inputWeight) := by ring

/-- One completed inverse branch contracts squared chordal distance by a
uniform factor `1/2`, independently of its exponent and sector. -/
theorem block_chordalSq_act_le_half
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (left right : QI)
    (leftDenominator : RawParserSemantics.denominator
      (RawParser.blockMatrix kind exponent sector) left ≠ 0)
    (rightDenominator : RawParserSemantics.denominator
      (RawParser.blockMatrix kind exponent sector) right ≠ 0)
    (leftFull : RawParser.fullBlockHolds kind exponent sector
      (RatBox.homographic
        (RawParser.blockMatrix kind exponent sector) left))
    (rightFull : RawParser.fullBlockHolds kind exponent sector
      (RatBox.homographic
        (RawParser.blockMatrix kind exponent sector) right))
    (leftOutside : 1 < normSq left) (rightOutside : 1 < normSq right) :
    chordalSq
        (Mat2.act (RawParser.blockMatrix kind exponent sector)
          (Proj.affine left))
        (Mat2.act (RawParser.blockMatrix kind exponent sector)
          (Proj.affine right)) ≤
      (1 / 2 : ℚ) * chordalSq (Proj.affine left) (Proj.affine right) := by
  let block := RawParser.blockMatrix kind exponent sector
  let factor : ℚ := (2 : ℚ) ^ exponent + 1
  let leftInputWeight : ℚ := 1 + normSq left
  let rightInputWeight : ℚ := 1 + normSq right
  let leftOutputWeight : ℚ :=
    (Mat2.act block (Proj.affine left)).weight
  let rightOutputWeight : ℚ :=
    (Mat2.act block (Proj.affine right)).weight
  have factorPositive : 0 < factor := by
    dsimp [factor]
    positivity
  have leftInputPositive : 0 < leftInputWeight := by
    dsimp [leftInputWeight]
    positivity
  have rightInputPositive : 0 < rightInputWeight := by
    dsimp [rightInputWeight]
    positivity
  have leftWeight : factor * leftInputWeight < leftOutputWeight := by
    exact block_output_weight_gt kind exponent sector left leftDenominator
      leftFull leftOutside
  have rightWeight : factor * rightInputWeight < rightOutputWeight := by
    exact block_output_weight_gt kind exponent sector right rightDenominator
      rightFull rightOutside
  have leftOutputPositive : 0 < leftOutputWeight :=
    (mul_pos factorPositive leftInputPositive).trans leftWeight
  have rightOutputPositive : 0 < rightOutputWeight :=
    (mul_pos factorPositive rightInputPositive).trans rightWeight
  have outputProductGrowth :
      factor ^ 2 * (leftInputWeight * rightInputWeight) ≤
        leftOutputWeight * rightOutputWeight := by
    have productStrict :
        (factor * leftInputWeight) * (factor * rightInputWeight) <
          leftOutputWeight * rightOutputWeight :=
      mul_lt_mul leftWeight rightWeight.le
        (mul_pos factorPositive rightInputPositive)
        leftOutputPositive.le
    calc
      factor ^ 2 * (leftInputWeight * rightInputWeight) =
          (factor * leftInputWeight) *
            (factor * rightInputWeight) := by ring
      _ ≤ leftOutputWeight * rightOutputWeight := productStrict.le
  have determinantFactor :
      2 * normSq block.det ≤ factor ^ 2 := by
    dsimp [block, factor]
    exact two_normSq_blockMatrix_det_le_blockFactor_sq kind exponent sector
  have denominatorGrowth :
      2 * normSq block.det *
          (leftInputWeight * rightInputWeight) ≤
        leftOutputWeight * rightOutputWeight := by
    exact (mul_le_mul_of_nonneg_right determinantFactor
      (mul_nonneg leftInputPositive.le rightInputPositive.le)).trans
        outputProductGrowth
  rw [Mat2.chordalSq_act_affine, chordalSq_affine]
  change normSq block.det * normSq (left - right) /
      (leftOutputWeight * rightOutputWeight) ≤
    (1 / 2 : ℚ) *
      (normSq (left - right) /
        (leftInputWeight * rightInputWeight))
  exact scaled_fraction_le_half (normSq_nonneg (left - right))
    (mul_pos leftInputPositive rightInputPositive)
    (mul_pos leftOutputPositive rightOutputPositive) denominatorGrowth

/-- A completed inverse branch also contracts an admissible affine tail
towards the formal projective tail `ω`.  This is the boundary case needed for
tagged truncations: `ω` itself need not satisfy the open affine block
predicate. -/
theorem block_chordalSq_act_omega_le_half
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (tail : QI)
    (denominator : RawParserSemantics.denominator
      (RawParser.blockMatrix kind exponent sector) tail ≠ 0)
    (full : RawParser.fullBlockHolds kind exponent sector
      (RatBox.homographic
        (RawParser.blockMatrix kind exponent sector) tail))
    (outside : 1 < normSq tail) :
    chordalSq
        (Mat2.act (RawParser.blockMatrix kind exponent sector)
          (Proj.affine tail))
        (Mat2.act (RawParser.blockMatrix kind exponent sector)
          (Proj.omega : Proj QI)) ≤
      (1 / 2 : ℚ) * chordalSq (Proj.affine tail) Proj.omega := by
  let block := RawParser.blockMatrix kind exponent sector
  let factor : ℚ := (2 : ℚ) ^ exponent + 1
  let inputWeight : ℚ := 1 + normSq tail
  let firstWeight : ℚ := CCLHomographicCylinder.firstColumnWeight block
  let outputWeight : ℚ :=
    (Mat2.act block (Proj.affine tail)).weight
  have factorPositive : 0 < factor := by
    dsimp [factor]
    positivity
  have inputPositive : 0 < inputWeight := by
    dsimp [inputWeight]
    positivity
  have firstPositive : 0 < firstWeight := by
    dsimp [firstWeight, block]
    exact CCLHomographicCylinder.firstColumnWeight_pos
      (RawParser.blockMatrix_det_ne kind exponent sector)
  have outputGrowth : factor * inputWeight < outputWeight := by
    exact block_output_weight_gt kind exponent sector tail denominator full
      outside
  have outputPositive : 0 < outputWeight :=
    (mul_pos factorPositive inputPositive).trans outputGrowth
  have factorLeFirst : factor ≤ firstWeight := by
    have bound := two_mul_blockFactor_le_firstColumnWeight
      kind exponent sector
    dsimp [factor, firstWeight, block]
    nlinarith [show 0 ≤ (2 : ℚ) ^ exponent by positivity]
  have factorProductGrowth :
      factor ^ 2 * inputWeight ≤ firstWeight * outputWeight := by
    calc
      factor ^ 2 * inputWeight = factor * (factor * inputWeight) := by ring
      _ ≤ firstWeight * outputWeight :=
        mul_le_mul factorLeFirst outputGrowth.le
          (mul_pos factorPositive inputPositive).le firstPositive.le
  have determinantFactor :
      2 * normSq block.det ≤ factor ^ 2 := by
    dsimp [block, factor]
    exact two_normSq_blockMatrix_det_le_blockFactor_sq kind exponent sector
  have denominatorGrowth :
      2 * normSq block.det * inputWeight ≤ firstWeight * outputWeight := by
    exact (mul_le_mul_of_nonneg_right determinantFactor inputPositive.le).trans
      factorProductGrowth
  rw [Mat2.chordalSq_truncation, chordalSq_omega]
  simpa only [block, inputWeight, firstWeight, outputWeight,
    CCLHomographicCylinder.firstColumnWeight, Proj.weight, Mat2.act,
    Proj.affine, _root_.mul_one] using
    (scaled_fraction_le_half (determinant := normSq block.det)
      (difference := (1 : ℚ)) (inputWeight := inputWeight)
      (outputWeight := firstWeight * outputWeight) (by norm_num)
      inputPositive (mul_pos firstPositive outputPositive) denominatorGrowth)

/-- Symmetric projective-tail form of
`block_chordalSq_act_omega_le_half`. -/
theorem block_chordalSq_omega_act_le_half
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (tail : QI)
    (denominator : RawParserSemantics.denominator
      (RawParser.blockMatrix kind exponent sector) tail ≠ 0)
    (full : RawParser.fullBlockHolds kind exponent sector
      (RatBox.homographic
        (RawParser.blockMatrix kind exponent sector) tail))
    (outside : 1 < normSq tail) :
    chordalSq
        (Mat2.act (RawParser.blockMatrix kind exponent sector)
          (Proj.omega : Proj QI))
        (Mat2.act (RawParser.blockMatrix kind exponent sector)
          (Proj.affine tail)) ≤
      (1 / 2 : ℚ) * chordalSq Proj.omega (Proj.affine tail) := by
  simpa only [chordalSq_comm] using
    block_chordalSq_act_omega_le_half kind exponent sector tail denominator
      full outside

/-- Affine homographic form of completed-block contraction towards the
block's canonical projective truncation. -/
theorem block_chordalSq_homographic_truncation_le_half
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (tail : QI)
    (denominator : RawParserSemantics.denominator
      (RawParser.blockMatrix kind exponent sector) tail ≠ 0)
    (full : RawParser.fullBlockHolds kind exponent sector
      (RatBox.homographic
        (RawParser.blockMatrix kind exponent sector) tail))
    (outside : 1 < normSq tail) :
    chordalSq
        (Proj.affine (RatBox.homographic
          (RawParser.blockMatrix kind exponent sector) tail))
        (Mat2.act (RawParser.blockMatrix kind exponent sector)
          (Proj.omega : Proj QI)) ≤
      (1 / 2 : ℚ) * chordalSq (Proj.affine tail) Proj.omega := by
  have contracted := block_chordalSq_act_omega_le_half kind exponent sector
    tail denominator full outside
  rw [CCLHomographicCylinder.act_affine_eq_scale_homographic _ _ denominator,
    chordalSq_scale_left _ denominator] at contracted
  exact contracted

/-- The two finite residual forms admitted by the completed-block theorem.
The projective constructor carries no artificial affine representative, while
the affine constructor records exactly the decidable parser facts consumed by
the contraction proof. -/
inductive CompatibleTail
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector) where
  | omega : CompatibleTail kind exponent sector
  | affine (tail : QI)
      (denominator : RawParserSemantics.denominator
        (RawParser.blockMatrix kind exponent sector) tail ≠ 0)
      (full : RawParser.fullBlockHolds kind exponent sector
        (RatBox.homographic
          (RawParser.blockMatrix kind exponent sector) tail))
      (outside : 1 < normSq tail) : CompatibleTail kind exponent sector

namespace CompatibleTail

/-- Homogeneous coordinate represented by a compatible residual. -/
def point
    {kind : RawParser.BlockKind} {exponent : ℕ} {sector : Sector} :
    CompatibleTail kind exponent sector → Proj QI
  | .omega => Proj.omega
  | .affine tail _ _ _ => Proj.affine tail

theorem point_hasNonzeroCoordinate
    {kind : RawParser.BlockKind} {exponent : ℕ} {sector : Sector}
    (tail : CompatibleTail kind exponent sector) :
    tail.point.HasNonzeroCoordinate := by
  cases tail with
  | omega => exact Proj.omega_hasNonzeroCoordinate
  | affine value _ _ _ => exact Proj.affine_hasNonzeroCoordinate value

end CompatibleTail

/-- Complete one-block projective contraction theorem.  Either residual may
be the formal terminal tail `ω`; all four cases are finite and constructive. -/
theorem block_chordalSq_compatibleTail_le_half
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (left right : CompatibleTail kind exponent sector) :
    chordalSq
        (Mat2.act (RawParser.blockMatrix kind exponent sector) left.point)
        (Mat2.act (RawParser.blockMatrix kind exponent sector) right.point) ≤
      (1 / 2 : ℚ) * chordalSq left.point right.point := by
  cases left with
  | omega =>
      cases right with
      | omega =>
          simp only [CompatibleTail.point]
          rw [chordalSq_eq_zero_of_equivalent
              (Proj.Equivalent.refl
                (Mat2.act (RawParser.blockMatrix kind exponent sector)
                  (Proj.omega : Proj QI))),
            chordalSq_eq_zero_of_equivalent
              (Proj.Equivalent.refl (Proj.omega : Proj QI))]
          norm_num
      | affine tail denominator full outside =>
          simpa only [CompatibleTail.point] using
            block_chordalSq_omega_act_le_half kind exponent sector tail
              denominator full outside
  | affine tail denominator full outside =>
      cases right with
      | omega =>
          simpa only [CompatibleTail.point] using
            block_chordalSq_act_omega_le_half kind exponent sector tail
              denominator full outside
      | affine other otherDenominator otherFull otherOutside =>
          simpa only [CompatibleTail.point] using
            block_chordalSq_act_le_half kind exponent sector tail other
              denominator otherDenominator full otherFull outside otherOutside

/-- Finite data of one completed decoder block, independent of its spelling
as raw unary and sector bits. -/
structure DecoderBlock where
  kind : RawParser.BlockKind
  exponent : ℕ
  sector : Sector
deriving DecidableEq, Repr

namespace DecoderBlock

def matrix (block : DecoderBlock) : Mat2 QI :=
  RawParser.blockMatrix block.kind block.exponent block.sector

/-- Apply a finite outer-to-inner block list to one residual projective
coordinate. -/
def decode : List DecoderBlock → Proj QI → Proj QI
  | [], tail => tail
  | block :: blocks, tail => Mat2.act block.matrix (decode blocks tail)

theorem act_scale (matrix : Mat2 QI) (scale : QI) (point : Proj QI) :
    Mat2.act matrix (point.scale scale) =
      (Mat2.act matrix point).scale scale := by
  ext <;>
    simp only [Mat2.act, Proj.scale] <;>
    ring_nf

theorem decode_scale (blocks : List DecoderBlock) (scale : QI)
    (tail : Proj QI) :
    decode blocks (tail.scale scale) = (decode blocks tail).scale scale := by
  induction blocks with
  | nil => rfl
  | cons block blocks inductionHypothesis =>
      simp only [decode]
      rw [inductionHypothesis, act_scale]

theorem decode_append (outer inner : List DecoderBlock) (tail : Proj QI) :
    decode (outer ++ inner) tail = decode outer (decode inner tail) := by
  induction outer with
  | nil => rfl
  | cons block blocks inductionHypothesis =>
      simp only [List.cons_append, decode]
      rw [inductionHypothesis]

/-- Forget the accumulated homography in a retained parser constraint while
keeping the block syntax which introduced it. -/
def ofConstraint (constraint : RawParser.Constraint) : DecoderBlock :=
  ⟨constraint.kind, constraint.exponent, constraint.sector⟩

@[simp] theorem ofConstraint_precompose
    (constraint : RawParser.Constraint) (matrix : Mat2 QI) :
    ofConstraint (constraint.precompose matrix) = ofConstraint constraint :=
  rfl

end DecoderBlock

/-- Completed blocks retained by one parser state, restored to decoder order.
The parser stores the newest historical constraint first. -/
def stateBlocks (state : RawParser.State) : List DecoderBlock :=
  state.history.reverse.map DecoderBlock.ofConstraint

theorem stateBlocks_completeSector
    (state : RawParser.State) (kind : RawParser.BlockKind) (exponent : ℕ)
    (first second third : Bool) :
    stateBlocks
        (RawParser.completeSector state kind exponent first second third) =
      stateBlocks state ++
        [⟨kind, exponent, RawParser.sectorOfBits first second third⟩] := by
  rcases state with ⟨phase, matrix, history⟩
  simp [stateBlocks, RawParser.completeSector, DecoderBlock.ofConstraint,
    RawParser.Constraint.precompose]

/-- A raw bit outside the third sector position leaves the completed decoder
block list unchanged. -/
theorem stateBlocks_step_eq_of_not_completed
    (state : RawParser.State) (bit : Bool)
    (notCompleted : ¬∃ kind exponent first second,
      state.phase = .sector kind exponent (.two first second)) :
    stateBlocks (RawParser.step state bit) = stateBlocks state := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial => cases bit <;> rfl
  | highUnary count => cases bit <;> rfl
  | lowUnary count => cases bit <;> rfl
  | loopUnary count => cases bit <;> rfl
  | sector kind exponent bits =>
      cases bits with
      | zero => rfl
      | one first => rfl
      | two first second =>
          exact (notCompleted ⟨kind, exponent, first, second, rfl⟩).elim

/-- Completed parser blocks in decoder order. -/
def parserBlocks (word : Prefix.Word) : List DecoderBlock :=
  stateBlocks (RawParser.parse word)

theorem parserBlocks_append_singleton_eq_of_not_completed
    (word : Prefix.Word) (bit : Bool)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse word).phase =
        .sector kind exponent (.two first second)) :
    parserBlocks (word ++ [bit]) = parserBlocks word := by
  rw [parserBlocks, show RawParser.parse (word ++ [bit]) =
      RawParser.step (RawParser.parse word) bit by
        simp [RawParser.parse, List.foldl_append]]
  exact stateBlocks_step_eq_of_not_completed (RawParser.parse word) bit
    notCompleted

theorem parserBlocks_append_completedSector
    (word : Prefix.Word) (bit : Bool)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse word).phase =
      .sector kind exponent (.two first second)) :
    parserBlocks (word ++ [bit]) = parserBlocks word ++
      [⟨kind, exponent, RawParser.sectorOfBits first second bit⟩] := by
  rw [parserBlocks, show RawParser.parse (word ++ [bit]) =
      RawParser.step (RawParser.parse word) bit by
        simp [RawParser.parse, List.foldl_append],
    RawParserSemantics.step_eq_completeSector (RawParser.parse word) kind
      exponent first second bit phase,
    stateBlocks_completeSector]
  rfl

@[simp] theorem parserBlocks_length (word : Prefix.Word) :
    (parserBlocks word).length =
      (RawParser.parse word).history.length := by
  simp [parserBlocks, stateBlocks]

/-- One raw transition preserves the equality between the syntax-only block
fold and the parser's accumulated matrix.  Completing a sector is precisely
the case which appends one decoder block. -/
theorem decoderBlocks_step_eq_act
    (state : RawParser.State)
    (stateCorrect : ∀ tail : Proj QI,
      DecoderBlock.decode (stateBlocks state) tail =
        Mat2.act state.matrix tail)
    (bit : Bool) :
    ∀ tail : Proj QI,
      DecoderBlock.decode (stateBlocks (RawParser.step state bit)) tail =
        Mat2.act (RawParser.step state bit).matrix tail := by
  intro tail
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bit <;>
        simpa [stateBlocks, RawParser.step] using stateCorrect tail
  | highUnary count =>
      cases bit <;>
        simpa [stateBlocks, RawParser.step] using stateCorrect tail
  | lowUnary count =>
      cases bit <;>
        simpa [stateBlocks, RawParser.step] using stateCorrect tail
  | loopUnary count =>
      cases bit <;>
        simpa [stateBlocks, RawParser.step] using stateCorrect tail
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simpa [stateBlocks, RawParser.step] using stateCorrect tail
      | one first =>
          simpa [stateBlocks, RawParser.step] using stateCorrect tail
      | two first second =>
          let sector := RawParser.sectorOfBits first second bit
          let block : DecoderBlock := ⟨kind, exponent, sector⟩
          have outer := stateCorrect (Mat2.act block.matrix tail)
          rw [show RawParser.step
              ⟨RawParser.Phase.sector kind exponent
                (.two first second), matrix, history⟩ bit =
              RawParser.completeSector
                ⟨RawParser.Phase.sector kind exponent
                  (.two first second), matrix, history⟩
                kind exponent first second bit by rfl]
          rw [stateBlocks_completeSector, DecoderBlock.decode_append]
          change DecoderBlock.decode
              (stateBlocks
                ⟨RawParser.Phase.sector kind exponent
                  (.two first second), matrix, history⟩)
              (Mat2.act block.matrix tail) =
            Mat2.act (Mat2.mul matrix block.matrix) tail
          rw [outer, Mat2.act_mul]

/-- Folding any finite raw suffix preserves the syntax/matrix identity. -/
theorem decoderBlocks_foldl_eq_act (bits : Prefix.Word) :
    ∀ (state : RawParser.State),
      (∀ tail : Proj QI,
        DecoderBlock.decode (stateBlocks state) tail =
          Mat2.act state.matrix tail) →
      ∀ tail : Proj QI,
        DecoderBlock.decode (stateBlocks (bits.foldl RawParser.step state))
            tail =
          Mat2.act (bits.foldl RawParser.step state).matrix tail := by
  induction bits with
  | nil =>
      intro state stateCorrect tail
      exact stateCorrect tail
  | cons bit rest inductionHypothesis =>
      intro state stateCorrect tail
      simp only [List.foldl_cons]
      exact inductionHypothesis (RawParser.step state bit)
        (decoderBlocks_step_eq_act state stateCorrect bit) tail

/-- The syntax-only completed block fold is exactly the matrix accumulated by
the raw parser, on every projective residual coordinate. -/
theorem decoderBlocks_parse_eq_act (word : Prefix.Word) (tail : Proj QI) :
    DecoderBlock.decode (parserBlocks word) tail =
      Mat2.act (RawParser.parse word).matrix tail := by
  apply decoderBlocks_foldl_eq_act word RawParser.initialState
  intro initialTail
  ext <;>
    simp [stateBlocks, RawParser.initialState, RawParser.identityMatrix,
      DecoderBlock.decode, Mat2.act]

/-- Affine parser semantics and the syntax-only decoder agree as homogeneous
coordinates with the parser denominator recorded as their nonzero scale. -/
theorem decoderBlocks_eq_scale_input_of_represents
    (word : Prefix.Word) (input tail : QI)
    (represents : RawParserSemantics.Represents
      (RawParser.parse word) input tail) :
    DecoderBlock.decode (parserBlocks word) (Proj.affine tail) =
      (Proj.affine input).scale
        (RawParserSemantics.denominator
          (RawParser.parse word).matrix tail) := by
  calc
    DecoderBlock.decode (parserBlocks word) (Proj.affine tail) =
        Mat2.act (RawParser.parse word).matrix (Proj.affine tail) :=
      decoderBlocks_parse_eq_act word (Proj.affine tail)
    _ = (Proj.affine
          (RatBox.homographic (RawParser.parse word).matrix tail)).scale
        (RawParserSemantics.denominator
          (RawParser.parse word).matrix tail) :=
      CCLHomographicCylinder.act_affine_eq_scale_homographic
        (RawParser.parse word).matrix tail represents.1
    _ = (Proj.affine input).scale
        (RawParserSemantics.denominator
          (RawParser.parse word).matrix tail) := by
      rw [represents.2.1]

/-- One intermediate projective coordinate is compatible with a displayed
block when it is a nonzero homogeneous rescaling of either `ω` or an affine
residual carrying the exact block predicate.  Recording the scale explicitly
avoids quotienting projective coordinates or choosing a normalized pair. -/
def BlockCompatible (block : DecoderBlock) (point : Proj QI) : Prop :=
  ∃ tail : CompatibleTail block.kind block.exponent block.sector,
    ∃ scale : QI, scale ≠ 0 ∧ tail.point.scale scale = point

/-- Compatibility evidence at every level of a finite outer-to-inner block
list.  This is the finite hypothesis needed for iteration; it names no
infinite cylinder or completed value. -/
inductive CompatibleThrough :
    (blocks : List DecoderBlock) → (tail : Proj QI) → Prop where
  | nil (tail : Proj QI) : CompatibleThrough [] tail
  | cons {block : DecoderBlock} {blocks : List DecoderBlock}
      {tail : Proj QI}
      (inner : CompatibleThrough blocks tail)
      (outer : BlockCompatible block (DecoderBlock.decode blocks tail)) :
      CompatibleThrough (block :: blocks) tail

namespace CompatibleThrough

/-- A nonzero rescaling of the unresolved terminal coordinate rescales every
intermediate decoder coordinate and therefore preserves the whole finite
compatibility trace. -/
theorem scale
    {blocks : List DecoderBlock} {tail : Proj QI}
    (compatible : CompatibleThrough blocks tail)
    (factor : QI) (factorNonzero : factor ≠ 0) :
    CompatibleThrough blocks (tail.scale factor) := by
  induction compatible with
  | nil tail => exact .nil (tail.scale factor)
  | @cons block blocks tail inner outer inductionHypothesis =>
      refine .cons inductionHypothesis ?_
      rcases outer with
        ⟨blockTail, blockScale, blockScaleNonzero, blockScaleEq⟩
      refine ⟨blockTail, blockScale * factor,
        mul_ne_zero blockScaleNonzero factorNonzero, ?_⟩
      rw [DecoderBlock.decode_scale, ← blockScaleEq]
      ext <;>
        simp only [Proj.scale] <;>
        ring_nf

/-- Compatible outer and inner traces splice without normalizing their common
projective coordinate. -/
theorem append
    {outer inner : List DecoderBlock} {tail : Proj QI}
    (outerCompatible :
      CompatibleThrough outer (DecoderBlock.decode inner tail))
    (innerCompatible : CompatibleThrough inner tail) :
    CompatibleThrough (outer ++ inner) tail := by
  induction outer with
  | nil => exact innerCompatible
  | cons block blocks inductionHypothesis =>
      cases outerCompatible with
      | cons compatible blockCompatible =>
          refine .cons (inductionHypothesis compatible) ?_
          exact Eq.mp
            (congrArg (BlockCompatible block)
              (DecoderBlock.decode_append blocks inner tail).symm)
            blockCompatible

end CompatibleThrough

/-- Reverse one raw transition at the level of finite projective traces.
Ordinary bits leave the completed block list unchanged.  A third sector bit
contributes one affine compatible tail, while the older trace is transported
through the block denominator as an explicit nonzero homogeneous scale. -/
theorem compatibleThrough_step_of_represents
    (state : RawParser.State) (bit : Bool) (input tail : QI)
    (represents : RawParserSemantics.Represents
      (RawParser.step state bit) input tail)
    (beforeCompatible : CompatibleThrough (stateBlocks state)
      (Proj.affine (RawParserSemantics.previousTail state bit tail))) :
    CompatibleThrough (stateBlocks (RawParser.step state bit))
      (Proj.affine tail) := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bit <;>
        simpa [stateBlocks, RawParser.step,
          RawParserSemantics.previousTail] using beforeCompatible
  | highUnary count =>
      cases bit <;>
        simpa [stateBlocks, RawParser.step,
          RawParserSemantics.previousTail] using beforeCompatible
  | lowUnary count =>
      cases bit <;>
        simpa [stateBlocks, RawParser.step,
          RawParserSemantics.previousTail] using beforeCompatible
  | loopUnary count =>
      cases bit <;>
        simpa [stateBlocks, RawParser.step,
          RawParserSemantics.previousTail] using beforeCompatible
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simpa [stateBlocks, RawParser.step,
            RawParserSemantics.previousTail] using beforeCompatible
      | one first =>
          simpa [stateBlocks, RawParser.step,
            RawParserSemantics.previousTail] using beforeCompatible
      | two first second =>
          let sector := RawParser.sectorOfBits first second bit
          let block : DecoderBlock := ⟨kind, exponent, sector⟩
          let blockMatrix := RawParser.blockMatrix kind exponent sector
          have newest :
              (RawParser.Constraint.mk blockMatrix kind exponent sector).Holds
                tail := by
            apply represents.2.2.1
            simp [RawParser.step, RawParser.completeSector, sector,
              blockMatrix]
          have outside : 1 < normSq tail := by
            simpa [RawParser.step, RawParser.completeSector,
              RawParser.activeHolds] using represents.2.2.2
          let compatibleTail : CompatibleTail kind exponent sector :=
            .affine tail newest.1 newest.2 outside
          have innerCompatible : CompatibleThrough [block]
              (Proj.affine tail) := by
            refine .cons (.nil (Proj.affine tail)) ?_
            refine ⟨compatibleTail, 1, one_ne_zero, ?_⟩
            ext <;>
              simp [DecoderBlock.decode, compatibleTail,
                CompatibleTail.point, Proj.scale]
          have outerScaled := beforeCompatible.scale
            (RawParserSemantics.denominator blockMatrix tail) newest.1
          have decodedBlock :
              DecoderBlock.decode [block] (Proj.affine tail) =
                (Proj.affine
                  (RawParserSemantics.previousTail
                    ⟨RawParser.Phase.sector kind exponent
                      (.two first second), matrix, history⟩ bit tail)).scale
                  (RawParserSemantics.denominator blockMatrix tail) := by
            simpa [DecoderBlock.decode, DecoderBlock.matrix, block,
              blockMatrix, sector, RawParserSemantics.previousTail] using
              CCLHomographicCylinder.act_affine_eq_scale_homographic
                blockMatrix tail newest.1
          have outerCompatible : CompatibleThrough
              (stateBlocks
                ⟨RawParser.Phase.sector kind exponent
                  (.two first second), matrix, history⟩)
              (DecoderBlock.decode [block] (Proj.affine tail)) := by
            rw [decodedBlock]
            exact outerScaled
          have appended := CompatibleThrough.append outerCompatible
            innerCompatible
          rw [show RawParser.step
              ⟨RawParser.Phase.sector kind exponent
                (.two first second), matrix, history⟩ bit =
              RawParser.completeSector
                ⟨RawParser.Phase.sector kind exponent
                  (.two first second), matrix, history⟩
                kind exponent first second bit by rfl,
            stateBlocks_completeSector]
          exact appended

/-- Every ordinary affine realization of a raw parser word yields the finite
projective compatibility trace consumed by the iterated block theorem. -/
theorem compatibleThrough_parse_of_represents
    (word : Prefix.Word) (input tail : QI)
    (represents : RawParserSemantics.Represents
      (RawParser.parse word) input tail) :
    CompatibleThrough (parserBlocks word) (Proj.affine tail) := by
  induction word using List.reverseRecOn generalizing input tail with
  | nil =>
      simpa [parserBlocks, RawParser.parse, RawParser.initialState,
        stateBlocks] using
        (CompatibleThrough.nil (Proj.affine tail))
  | append_singleton base bit inductionHypothesis =>
      let state := RawParser.parse base
      have parsedAppend : RawParser.parse (base ++ [bit]) =
          RawParser.step state bit := by
        simp [state, RawParser.parse, List.foldl_append]
      have after : RawParserSemantics.Represents
          (RawParser.step state bit) input tail := by
        rw [← parsedAppend]
        exact represents
      have before := RawParserSemantics.step_represents_previous
        state bit input tail after
      have beforeCompatible := inductionHypothesis input
        (RawParserSemantics.previousTail state bit tail) before
      rw [parserBlocks, parsedAppend]
      exact compatibleThrough_step_of_represents state bit input tail after
        beforeCompatible

/-- Iterating the four-case projective block theorem gives the universal
`2⁻ⁿ` squared-chordal contraction for every finite compatible block trace. -/
theorem decoderBlocks_chordalSq_le_half_pow
    (blocks : List DecoderBlock) (left right : Proj QI)
    (leftCompatible : CompatibleThrough blocks left)
    (rightCompatible : CompatibleThrough blocks right) :
    chordalSq (DecoderBlock.decode blocks left)
        (DecoderBlock.decode blocks right) ≤
      (1 / 2 : ℚ) ^ blocks.length * chordalSq left right := by
  induction blocks with
  | nil =>
      simp [DecoderBlock.decode]
  | cons block blocks inductionHypothesis =>
      cases leftCompatible with
      | cons leftInner leftOuter =>
          cases rightCompatible with
          | cons rightInner rightOuter =>
              rcases leftOuter with
                ⟨leftTail, leftScale, leftScaleNonzero, leftTailEq⟩
              rcases rightOuter with
                ⟨rightTail, rightScale, rightScaleNonzero, rightTailEq⟩
              have blockBound := block_chordalSq_compatibleTail_le_half
                block.kind block.exponent block.sector leftTail rightTail
              have scaledBlockBound :
                  chordalSq
                      (Mat2.act block.matrix
                        (leftTail.point.scale leftScale))
                      (Mat2.act block.matrix
                        (rightTail.point.scale rightScale)) ≤
                    (1 / 2 : ℚ) *
                      chordalSq (leftTail.point.scale leftScale)
                        (rightTail.point.scale rightScale) := by
                rw [DecoderBlock.act_scale, DecoderBlock.act_scale,
                  chordalSq_scale_left leftScale leftScaleNonzero,
                  chordalSq_scale_right rightScale rightScaleNonzero,
                  chordalSq_scale_left leftScale leftScaleNonzero,
                  chordalSq_scale_right rightScale rightScaleNonzero]
                exact blockBound
              rw [leftTailEq, rightTailEq] at scaledBlockBound
              have innerBound := inductionHypothesis leftInner rightInner
              have scaledInner := mul_le_mul_of_nonneg_left innerBound
                (by norm_num : (0 : ℚ) ≤ 1 / 2)
              calc
                chordalSq
                    (DecoderBlock.decode (block :: blocks) left)
                    (DecoderBlock.decode (block :: blocks) right) =
                    chordalSq
                      (Mat2.act block.matrix
                        (DecoderBlock.decode blocks left))
                      (Mat2.act block.matrix
                        (DecoderBlock.decode blocks right)) := rfl
                _ ≤ (1 / 2 : ℚ) *
                    chordalSq (DecoderBlock.decode blocks left)
                      (DecoderBlock.decode blocks right) := scaledBlockBound
                _ ≤ (1 / 2 : ℚ) *
                    ((1 / 2 : ℚ) ^ blocks.length *
                      chordalSq left right) := scaledInner
                _ = (1 / 2 : ℚ) ^ (block :: blocks).length *
                    chordalSq left right := by
                      simp only [List.length_cons, pow_succ]
                      ring

/-- The unresolved projective residual pair has diameter at most one, so a
compatible `n`-block trace has the standalone radius `2⁻ⁿ`. -/
theorem decoderBlocks_chordalSq_le_half_pow_of_valid
    (blocks : List DecoderBlock) (left right : Proj QI)
    (leftCompatible : CompatibleThrough blocks left)
    (rightCompatible : CompatibleThrough blocks right)
    (leftValid : left.HasNonzeroCoordinate)
    (rightValid : right.HasNonzeroCoordinate) :
    chordalSq (DecoderBlock.decode blocks left)
        (DecoderBlock.decode blocks right) ≤
      (1 / 2 : ℚ) ^ blocks.length := by
  have contraction := decoderBlocks_chordalSq_le_half_pow blocks left right
    leftCompatible rightCompatible
  have tailBound := chordalSq_le_one leftValid rightValid
  have scaledTailBound := mul_le_mul_of_nonneg_left tailBound
    (pow_nonneg (by norm_num : (0 : ℚ) ≤ 1 / 2) blocks.length)
  calc
    chordalSq (DecoderBlock.decode blocks left)
        (DecoderBlock.decode blocks right) ≤
      (1 / 2 : ℚ) ^ blocks.length * chordalSq left right := contraction
    _ ≤ (1 / 2 : ℚ) ^ blocks.length * 1 := scaledTailBound
    _ = (1 / 2 : ℚ) ^ blocks.length := by ring

/-- The projective trace package recovers the accumulated affine parser
contraction directly.  This theorem is intentionally kept beside the trace
API: it verifies that explicit homogeneous scaling loses no strength relative
to the older word-by-word affine induction below. -/
theorem parse_represents_chordalSq_le_via_trace
    (word : Prefix.Word) {leftInput rightInput leftTail rightTail : QI}
    (leftRepresents : RawParserSemantics.Represents
      (RawParser.parse word) leftInput leftTail)
    (rightRepresents : RawParserSemantics.Represents
      (RawParser.parse word) rightInput rightTail) :
    chordalSq (Proj.affine leftInput) (Proj.affine rightInput) ≤
      (1 / 2 : ℚ) ^ (RawParser.parse word).history.length *
        chordalSq (Proj.affine leftTail) (Proj.affine rightTail) := by
  have leftCompatible := compatibleThrough_parse_of_represents word
    leftInput leftTail leftRepresents
  have rightCompatible := compatibleThrough_parse_of_represents word
    rightInput rightTail rightRepresents
  have contraction := decoderBlocks_chordalSq_le_half_pow
    (parserBlocks word) (Proj.affine leftTail) (Proj.affine rightTail)
    leftCompatible rightCompatible
  have leftDecode := decoderBlocks_eq_scale_input_of_represents word
    leftInput leftTail leftRepresents
  have rightDecode := decoderBlocks_eq_scale_input_of_represents word
    rightInput rightTail rightRepresents
  calc
    chordalSq (Proj.affine leftInput) (Proj.affine rightInput) =
        chordalSq
          (DecoderBlock.decode (parserBlocks word) (Proj.affine leftTail))
          (DecoderBlock.decode (parserBlocks word)
            (Proj.affine rightTail)) := by
      rw [leftDecode, rightDecode,
        chordalSq_scale_left _ leftRepresents.1,
        chordalSq_scale_right _ rightRepresents.1]
    _ ≤ (1 / 2 : ℚ) ^ (parserBlocks word).length *
        chordalSq (Proj.affine leftTail) (Proj.affine rightTail) := contraction
    _ = (1 / 2 : ℚ) ^ (RawParser.parse word).history.length *
        chordalSq (Proj.affine leftTail) (Proj.affine rightTail) := by
      rw [parserBlocks_length]

/-- Affine homographic form consumed by parser-tail induction. -/
theorem block_chordalSq_homographic_le_half
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (left right : QI)
    (leftDenominator : RawParserSemantics.denominator
      (RawParser.blockMatrix kind exponent sector) left ≠ 0)
    (rightDenominator : RawParserSemantics.denominator
      (RawParser.blockMatrix kind exponent sector) right ≠ 0)
    (leftFull : RawParser.fullBlockHolds kind exponent sector
      (RatBox.homographic
        (RawParser.blockMatrix kind exponent sector) left))
    (rightFull : RawParser.fullBlockHolds kind exponent sector
      (RatBox.homographic
        (RawParser.blockMatrix kind exponent sector) right))
    (leftOutside : 1 < normSq left) (rightOutside : 1 < normSq right) :
    chordalSq
        (Proj.affine (RatBox.homographic
          (RawParser.blockMatrix kind exponent sector) left))
        (Proj.affine (RatBox.homographic
          (RawParser.blockMatrix kind exponent sector) right)) ≤
      (1 / 2 : ℚ) * chordalSq (Proj.affine left) (Proj.affine right) := by
  rw [CCLHomographicCylinder.chordalSq_homographic_eq_act _
    leftDenominator rightDenominator]
  exact block_chordalSq_act_le_half kind exponent sector left right
    leftDenominator rightDenominator leftFull rightFull leftOutside rightOutside

/-- The accumulated parser matrix is geometrically Lipschitz in its current
affine tail, with one factor `1/2` for every completed historical block. -/
theorem parse_represents_chordalSq_le
    (word : Prefix.Word) {leftInput rightInput leftTail rightTail : QI}
    (leftRepresents : RawParserSemantics.Represents
      (RawParser.parse word) leftInput leftTail)
    (rightRepresents : RawParserSemantics.Represents
      (RawParser.parse word) rightInput rightTail) :
    chordalSq (Proj.affine leftInput) (Proj.affine rightInput) ≤
      (1 / 2 : ℚ) ^ (RawParser.parse word).history.length *
        chordalSq (Proj.affine leftTail) (Proj.affine rightTail) := by
  induction word using List.reverseRecOn generalizing
      leftInput rightInput leftTail rightTail with
  | nil =>
      have leftEq := leftRepresents.2.1
      have rightEq := rightRepresents.2.1
      simp only [RawParser.parse, List.foldl_nil] at leftEq rightEq ⊢
      change leftInput = RatBox.homographic RawParser.identityMatrix leftTail
        at leftEq
      change rightInput = RatBox.homographic RawParser.identityMatrix rightTail
        at rightEq
      rw [CCLUnaryCylinder.identity_homographic] at leftEq rightEq
      subst leftInput
      subst rightInput
      simp [RawParser.initialState]
  | append_singleton base bit inductionHypothesis =>
      generalize stateEq : RawParser.parse base = state
      have parsedAppend :
          RawParser.parse (base ++ [bit]) = RawParser.step state bit := by
        calc
          RawParser.parse (base ++ [bit]) =
              RawParser.step (RawParser.parse base) bit := by
            simp [RawParser.parse, List.foldl_append]
          _ = RawParser.step state bit := by rw [stateEq]
      have leftStep : RawParserSemantics.Represents
          (RawParser.step state bit) leftInput leftTail := by
        rw [← parsedAppend]
        exact leftRepresents
      have rightStep : RawParserSemantics.Represents
          (RawParser.step state bit) rightInput rightTail := by
        rw [← parsedAppend]
        exact rightRepresents
      have leftPrevious := RawParserSemantics.step_represents_previous
        state bit leftInput leftTail leftStep
      have rightPrevious := RawParserSemantics.step_represents_previous
        state bit rightInput rightTail rightStep
      have leftPreviousBase : RawParserSemantics.Represents
          (RawParser.parse base) leftInput
            (RawParserSemantics.previousTail state bit leftTail) := by
        rw [stateEq]
        exact leftPrevious
      have rightPreviousBase : RawParserSemantics.Represents
          (RawParser.parse base) rightInput
            (RawParserSemantics.previousTail state bit rightTail) := by
        rw [stateEq]
        exact rightPrevious
      have previousBound := inductionHypothesis leftPreviousBase
        rightPreviousBase
      rcases state with ⟨phase, matrix, history⟩
      cases phase with
      | initial =>
          cases bit <;>
            simpa [parsedAppend, stateEq,
              RawParser.step, RawParserSemantics.previousTail] using
              previousBound
      | highUnary count =>
          cases bit <;>
            simpa [parsedAppend, stateEq,
              RawParser.step, RawParserSemantics.previousTail] using
              previousBound
      | lowUnary count =>
          cases bit <;>
            simpa [parsedAppend, stateEq,
              RawParser.step, RawParserSemantics.previousTail] using
              previousBound
      | loopUnary count =>
          cases bit <;>
            simpa [parsedAppend, stateEq,
              RawParser.step, RawParserSemantics.previousTail] using
              previousBound
      | sector kind exponent bits =>
          cases bits with
          | zero =>
              simpa [parsedAppend, stateEq,
                RawParser.step, RawParserSemantics.previousTail] using
                previousBound
          | one first =>
              simpa [parsedAppend, stateEq,
                RawParser.step, RawParserSemantics.previousTail] using
                previousBound
          | two first second =>
              let sector := RawParser.sectorOfBits first second bit
              let block := RawParser.blockMatrix kind exponent sector
              have leftAfter : RawParserSemantics.Represents
                  (RawParser.completeSector
                    ⟨RawParser.Phase.sector kind exponent (.two first second),
                      matrix, history⟩ kind exponent first second bit)
                  leftInput leftTail := by
                simpa [RawParser.step] using leftStep
              have rightAfter : RawParserSemantics.Represents
                  (RawParser.completeSector
                    ⟨RawParser.Phase.sector kind exponent (.two first second),
                      matrix, history⟩ kind exponent first second bit)
                  rightInput rightTail := by
                simpa [RawParser.step] using rightStep
              have leftNewest :
                  (RawParser.Constraint.mk block kind exponent sector).Holds
                    leftTail := by
                apply leftAfter.2.2.1
                simp [RawParser.completeSector, sector, block]
              have rightNewest :
                  (RawParser.Constraint.mk block kind exponent sector).Holds
                    rightTail := by
                apply rightAfter.2.2.1
                simp [RawParser.completeSector, sector, block]
              have leftOutside : 1 < normSq leftTail := by
                simpa [RawParser.completeSector, RawParser.activeHolds] using
                  leftAfter.2.2.2
              have rightOutside : 1 < normSq rightTail := by
                simpa [RawParser.completeSector, RawParser.activeHolds] using
                  rightAfter.2.2.2
              have blockBound := block_chordalSq_homographic_le_half
                kind exponent sector leftTail rightTail leftNewest.1
                rightNewest.1 leftNewest.2 rightNewest.2 leftOutside
                rightOutside
              have scaledBlock := mul_le_mul_of_nonneg_left blockBound
                (pow_nonneg (by norm_num : (0 : ℚ) ≤ 1 / 2) history.length)
              calc
                chordalSq (Proj.affine leftInput) (Proj.affine rightInput) ≤
                    (1 / 2 : ℚ) ^ history.length *
                      chordalSq
                        (Proj.affine (RatBox.homographic block leftTail))
                        (Proj.affine (RatBox.homographic block rightTail)) := by
                  simpa [stateEq, RawParserSemantics.previousTail,
                    sector, block] using previousBound
                _ ≤ (1 / 2 : ℚ) ^ history.length *
                    ((1 / 2 : ℚ) *
                      chordalSq (Proj.affine leftTail)
                        (Proj.affine rightTail)) := scaledBlock
                _ = (1 / 2 : ℚ) ^
                      (RawParser.parse (base ++ [bit])).history.length *
                    chordalSq (Proj.affine leftTail)
                      (Proj.affine rightTail) := by
                  simp [parsedAppend,
                    RawParser.step, RawParser.completeSector]
                  ring_nf

/-- Reading the third sector bit completes exactly one decoder block. -/
theorem completedSector_append_history_length
    (word : Prefix.Word) (bit : Bool)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse word).phase =
      .sector kind exponent (.two first second)) :
    (RawParser.parse (word ++ [bit])).history.length =
      (RawParser.parse word).history.length + 1 := by
  rw [show RawParser.parse (word ++ [bit]) =
      RawParser.step (RawParser.parse word) bit by
        simp [RawParser.parse, List.foldl_append],
    RawParserSemantics.step_eq_completeSector (RawParser.parse word) kind
      exponent first second bit phase]
  simp [RawParser.completeSector]

/-- A slightly padded geometric radius, chosen to reuse the existing
`binaryDepth` ceiling theorem verbatim. -/
def historyRadiusSq (word : Prefix.Word) : ℚ :=
  4 / (2 : ℚ) ^ (RawParser.parse word).history.length

/-- Consequently the universal completed-history squared-chordal radius is
halved by that raw bit. -/
theorem historyRadiusSq_append_completedSector
    (word : Prefix.Word) (bit : Bool)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse word).phase =
      .sector kind exponent (.two first second)) :
    historyRadiusSq (word ++ [bit]) =
      (1 / 2 : ℚ) * historyRadiusSq word := by
  unfold historyRadiusSq
  rw [completedSector_append_history_length word bit phase, pow_succ]
  ring

theorem historyRadiusSq_nonneg (word : Prefix.Word) :
    0 ≤ historyRadiusSq word := by
  dsimp [historyRadiusSq]
  positivity

private theorem half_pow_le_historyRadius (count : ℕ) :
    (1 / 2 : ℚ) ^ count ≤ 4 / (2 : ℚ) ^ count := by
  rw [div_pow]
  norm_num only [one_pow]
  exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- Completed-history length alone gives a universal raw-cylinder diameter,
including all retained historical constraints and the current active phase. -/
theorem represented_chordalSq_le_historyRadius
    (word : Prefix.Word) {left right : QI}
    (leftRepresented : RawParserSemantics.Represented word left)
    (rightRepresented : RawParserSemantics.Represented word right) :
    chordalSq (Proj.affine left) (Proj.affine right) ≤
      historyRadiusSq word := by
  rcases leftRepresented with ⟨leftTail, leftRepresents⟩
  rcases rightRepresented with ⟨rightTail, rightRepresents⟩
  have lipschitz := parse_represents_chordalSq_le word
    leftRepresents rightRepresents
  have tailUnit := chordalSq_le_one
    (Proj.affine_hasNonzeroCoordinate leftTail)
    (Proj.affine_hasNonzeroCoordinate rightTail)
  have scaledUnit := mul_le_mul_of_nonneg_left tailUnit
    (pow_nonneg (by norm_num : (0 : ℚ) ≤ 1 / 2)
      (RawParser.parse word).history.length)
  calc
    chordalSq (Proj.affine left) (Proj.affine right) ≤
        (1 / 2 : ℚ) ^ (RawParser.parse word).history.length *
          chordalSq (Proj.affine leftTail) (Proj.affine rightTail) := lipschitz
    _ ≤ (1 / 2 : ℚ) ^ (RawParser.parse word).history.length * 1 :=
      scaledUnit
    _ ≤ historyRadiusSq word := by
      simpa only [_root_.mul_one, historyRadiusSq] using
        half_pow_le_historyRadius (RawParser.parse word).history.length

/-- Universal completed-block envelope for any raw word. -/
def historyEnvelope (word : Prefix.Word) : RawCylinderEnvelope where
  truncation := ⟨word⟩
  radiusSq := historyRadiusSq word
  radiusSq_nonneg := historyRadiusSq_nonneg word
  diameter := represented_chordalSq_le_historyRadius word

theorem historyRadiusSq_le_of_history_le
    {earlier later : Prefix.Word}
    (historyLe : (RawParser.parse earlier).history.length ≤
      (RawParser.parse later).history.length) :
    historyRadiusSq later ≤ historyRadiusSq earlier := by
  apply div_le_div_of_nonneg_left (by norm_num)
  · positivity
  · exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) historyLe

/-- The existing rational-ceiling binary depth is also sufficient for the
completed-block history radius. -/
theorem historyRadiusSq_le_epsilon
    (word : Prefix.Word) {epsilon : ℚ} (epsilonPositive : 0 < epsilon)
    (enoughHistory : CCLUnaryCylinder.binaryDepth epsilon ≤
      (RawParser.parse word).history.length) :
    historyRadiusSq word ≤ epsilon := by
  calc
    historyRadiusSq word ≤
        4 / (2 : ℚ) ^ CCLUnaryCylinder.binaryDepth epsilon := by
      apply div_le_div_of_nonneg_left (by norm_num)
      · positivity
      · exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ))
          enoughHistory
    _ ≤ epsilon := CCLUnaryCylinder.binaryDepth_sufficient epsilonPositive

end CCLCompletedBlockContraction
end FTA
