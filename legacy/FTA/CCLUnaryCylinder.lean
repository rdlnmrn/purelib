import CCL.Encoding.Normalization
import FTA.CCLRawCylinderEnvelope
import Mathlib.Data.Rat.Floor

/-!
# Explicit chordal contraction inside raw unary fragments

These are the two partial-block cases in which the parser matrix, and hence
its canonical truncation pair, does not move at all.  Nevertheless the raw
predicate forces affine realizations either towards `ω` or towards zero, so
their squared chordal diameter has an explicit geometric rational bound.
-/

namespace FTA
namespace CCLUnaryCylinder

open CCL
open CCL.GaussianRat
open FTA.CCLChordalEnvelope
open FTA.CCLRawCylinderEnvelope

abbrev QI := CCL.GaussianRat

/-- Initial-high raw word after `count + 1` consecutive one bits. -/
def highUnaryWord : ℕ → Prefix.Word
  | 0 => [true]
  | count + 1 => highUnaryWord count ++ [true]

/-- Initial-low raw word after the leading zero and `count` one bits. -/
def lowUnaryWord : ℕ → Prefix.Word
  | 0 => [false]
  | count + 1 => lowUnaryWord count ++ [true]

theorem parse_highUnaryWord (count : ℕ) :
    RawParser.parse (highUnaryWord count) =
      ⟨.highUnary (count + 1), RawParser.identityMatrix, []⟩ := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [highUnaryWord, RawParser.parse, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      rw [show List.foldl RawParser.step RawParser.initialState
          (highUnaryWord count) = RawParser.parse (highUnaryWord count) by rfl,
        inductionHypothesis]
      rfl

theorem parse_lowUnaryWord (count : ℕ) :
    RawParser.parse (lowUnaryWord count) =
      ⟨.lowUnary count, RawParser.identityMatrix, []⟩ := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [lowUnaryWord, RawParser.parse, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      rw [show List.foldl RawParser.step RawParser.initialState
          (lowUnaryWord count) = RawParser.parse (lowUnaryWord count) by rfl,
        inductionHypothesis]
      rfl

theorem identity_homographic (tail : QI) :
    RatBox.homographic RawParser.identityMatrix tail = tail := by
  have inverseOne : inv (1 : QI) = 1 := by
    rw [← inv_eq]
    exact inv_one
  simp [RatBox.homographic, RawParser.identityMatrix, inverseOne]

/-- A rational realization of a high unary fragment has the displayed large
norm, even though the parser matrix is still the identity. -/
theorem highUnary_norm_lower {count : ℕ} {input : QI}
    (represented : RawParserSemantics.Represented (highUnaryWord count) input) :
    (2 : ℚ) ^ (count + 1) ≤ normSq input := by
  rcases represented with ⟨tail, _denominator, inputEq, holds⟩
  rw [parse_highUnaryWord] at inputEq holds
  rw [identity_homographic] at inputEq
  subst input
  exact holds.2

/-- After at least one low-run one bit, every rational realization has the
displayed small norm. -/
theorem lowUnary_norm_upper {count : ℕ} {input : QI}
    (represented :
      RawParserSemantics.Represented (lowUnaryWord (count + 1)) input) :
    (2 : ℚ) ^ count * normSq input < 1 := by
  rcases represented with ⟨tail, _denominator, inputEq, holds⟩
  rw [parse_lowUnaryWord] at inputEq holds
  rw [identity_homographic] at inputEq
  subst input
  exact holds.2

/-- Explicit squared chordal diameter of an initial-high unary cylinder. -/
def highRadiusSq (count : ℕ) : ℚ :=
  4 / (1 + (2 : ℚ) ^ (count + 1))

/-- Explicit squared chordal diameter after one or more initial-low run bits. -/
def lowRadiusSq (count : ℕ) : ℚ :=
  4 / (2 : ℚ) ^ count

theorem highRadiusSq_nonneg (count : ℕ) : 0 ≤ highRadiusSq count := by
  dsimp [highRadiusSq]
  positivity

theorem lowRadiusSq_nonneg (count : ℕ) : 0 ≤ lowRadiusSq count := by
  dsimp [lowRadiusSq]
  positivity

/-- High unary fragments contract chordally around the formal point `ω`. -/
theorem highUnary_chordalSq_le {count : ℕ} {left right : QI}
    (leftRepresented :
      RawParserSemantics.Represented (highUnaryWord count) left)
    (rightRepresented :
      RawParserSemantics.Represented (highUnaryWord count) right) :
    chordalSq (Proj.affine left) (Proj.affine right) ≤ highRadiusSq count := by
  let threshold : ℚ := (2 : ℚ) ^ (count + 1)
  have thresholdPositive : 0 < threshold := by
    dsimp [threshold]
    positivity
  have leftLower : threshold ≤ normSq left := by
    simpa only [threshold] using highUnary_norm_lower leftRepresented
  have rightLower : threshold ≤ normSq right := by
    simpa only [threshold] using highUnary_norm_lower rightRepresented
  have leftOmega :
      chordalSq (Proj.affine left) (Proj.omega : Proj QI) ≤
        1 / (1 + threshold) := by
    rw [chordalSq_omega]
    exact div_le_div_of_nonneg_left (by norm_num)
      (by linarith) (by linarith)
  have omegaRight :
      chordalSq (Proj.omega : Proj QI) (Proj.affine right) ≤
        1 / (1 + threshold) := by
    rw [chordalSq_comm, chordalSq_omega]
    exact div_le_div_of_nonneg_left (by norm_num)
      (by linarith) (by linarith)
  have triangle := chordalSq_triangle_two
    (Proj.affine_hasNonzeroCoordinate left)
    Proj.omega_hasNonzeroCoordinate
    (Proj.affine_hasNonzeroCoordinate right)
  calc
    chordalSq (Proj.affine left) (Proj.affine right) ≤
        2 * (chordalSq (Proj.affine left) (Proj.omega : Proj QI) +
          chordalSq (Proj.omega : Proj QI) (Proj.affine right)) := triangle
    _ ≤ 2 * (1 / (1 + threshold) + 1 / (1 + threshold)) := by
      linarith
    _ = highRadiusSq count := by
      dsimp [highRadiusSq, threshold]
      ring

/-- Low unary fragments contract chordally around affine zero while their
canonical parser truncation remains the formal point `ω`. -/
theorem lowUnary_chordalSq_le {count : ℕ} {left right : QI}
    (leftRepresented :
      RawParserSemantics.Represented (lowUnaryWord (count + 1)) left)
    (rightRepresented :
      RawParserSemantics.Represented (lowUnaryWord (count + 1)) right) :
    chordalSq (Proj.affine left) (Proj.affine right) ≤ lowRadiusSq count := by
  let threshold : ℚ := (2 : ℚ) ^ count
  have thresholdPositive : 0 < threshold := by
    dsimp [threshold]
    positivity
  have leftSmall : normSq left < 1 / threshold := by
    apply (lt_div_iff₀ thresholdPositive).2
    simpa only [threshold, _root_.mul_comm] using
      lowUnary_norm_upper leftRepresented
  have rightSmall : normSq right < 1 / threshold := by
    apply (lt_div_iff₀ thresholdPositive).2
    simpa only [threshold, _root_.mul_comm] using
      lowUnary_norm_upper rightRepresented
  have difference := normSq_sub_le_two left right
  have affineBound := CCLChordalEnvelope.chordalSq_affine_le_normSq left right
  have differenceBound : normSq (left - right) ≤ 4 / threshold := by
    have radiusIdentity :
        4 / threshold = 2 * (1 / threshold + 1 / threshold) := by ring
    rw [radiusIdentity]
    linarith
  exact affineBound.trans (by
    simpa only [lowRadiusSq, threshold] using differenceBound)

/-- Concrete diameter certificate for every initial-high unary fragment. -/
def highEnvelope (count : ℕ) : RawCylinderEnvelope where
  truncation := ⟨highUnaryWord count⟩
  radiusSq := highRadiusSq count
  radiusSq_nonneg := highRadiusSq_nonneg count
  diameter := highUnary_chordalSq_le

/-- Concrete diameter certificate after one or more initial-low run bits. -/
def lowEnvelope (count : ℕ) : RawCylinderEnvelope where
  truncation := ⟨lowUnaryWord (count + 1)⟩
  radiusSq := lowRadiusSq count
  radiusSq_nonneg := lowRadiusSq_nonneg count
  diameter := lowUnary_chordalSq_le

/-- Every displayed high-unary tagged truncation is still exactly `ω`. -/
theorem highEnvelope_point_eq_omega (count : ℕ) :
    (highEnvelope count).truncation.point = (Proj.omega : Proj QI) := by
  change (RawParser.parse (highUnaryWord count)).truncation = _
  rw [parse_highUnaryWord]
  ext <;>
    norm_num [RawParser.State.truncation, RawParser.identityMatrix,
      Mat2.act, Proj.omega]

/-- Every displayed low-unary tagged truncation is also still exactly `ω`,
although its cylinder diameter contracts towards affine zero. -/
theorem lowEnvelope_point_eq_omega (count : ℕ) :
    (lowEnvelope count).truncation.point = (Proj.omega : Proj QI) := by
  change (RawParser.parse (lowUnaryWord (count + 1))).truncation = _
  rw [parse_lowUnaryWord]
  ext <;>
    norm_num [RawParser.State.truncation, RawParser.identityMatrix,
      Mat2.act, Proj.omega]

theorem highUnaryWord_prefix_succ (count : ℕ) :
    highUnaryWord count <+: highUnaryWord (count + 1) := by
  exact ⟨[true], rfl⟩

theorem lowUnaryWord_prefix_succ (count : ℕ) :
    lowUnaryWord count <+: lowUnaryWord (count + 1) := by
  exact ⟨[true], rfl⟩

theorem highRadiusSq_succ_le (count : ℕ) :
    highRadiusSq (count + 1) ≤ highRadiusSq count := by
  apply div_le_div_of_nonneg_left (by norm_num)
  · positivity
  · have powerStep :
        (2 : ℚ) ^ (count + 1) ≤ (2 : ℚ) ^ (count + 1 + 1) := by
      calc
        (2 : ℚ) ^ (count + 1) ≤ 2 * (2 : ℚ) ^ (count + 1) := by
          nlinarith [show 0 ≤ (2 : ℚ) ^ (count + 1) by positivity]
        _ = (2 : ℚ) ^ (count + 1 + 1) := by
          conv_rhs => rw [pow_succ]
          ring
    linarith

theorem lowRadiusSq_succ_le (count : ℕ) :
    lowRadiusSq (count + 1) ≤ lowRadiusSq count := by
  apply div_le_div_of_nonneg_left (by norm_num)
  · positivity
  · have powerStep : (2 : ℚ) ^ count ≤ (2 : ℚ) ^ (count + 1) := by
      rw [pow_succ]
      nlinarith [show 0 ≤ (2 : ℚ) ^ count by positivity]
    exact powerStep

/-- The initial-low unary radius is antitone in its run exponent. -/
theorem lowRadiusSq_le_of_le {smaller larger : ℕ}
    (ordered : smaller ≤ larger) :
    lowRadiusSq larger ≤ lowRadiusSq smaller := by
  apply div_le_div_of_nonneg_left (by norm_num)
  · positivity
  · exact_mod_cast
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) ordered

theorem highEnvelope_succ_refines (count : ℕ) :
    (highEnvelope (count + 1)).Refines (highEnvelope count) := by
  exact ⟨highUnaryWord_prefix_succ count, highRadiusSq_succ_le count⟩

theorem lowEnvelope_succ_refines (count : ℕ) :
    (lowEnvelope (count + 1)).Refines (lowEnvelope count) := by
  exact ⟨lowUnaryWord_prefix_succ (count + 1), lowRadiusSq_succ_le count⟩

/-- Conservative executable depth at which the binary geometric radius is
below a requested positive rational error. -/
def binaryDepth (epsilon : ℚ) : ℕ :=
  ⌈4 / epsilon⌉₊

theorem binaryDepth_sufficient {epsilon : ℚ} (epsilonPositive : 0 < epsilon) :
    4 / (2 : ℚ) ^ binaryDepth epsilon ≤ epsilon := by
  let depth := binaryDepth epsilon
  have ceiling : 4 / epsilon ≤ (depth : ℚ) := by
    exact Nat.le_ceil (4 / epsilon)
  have naturalPower : depth + 1 ≤ 2 ^ depth :=
    CCL.BinaryNormalization.succ_le_two_pow depth
  have castPower : (depth : ℚ) ≤ (2 : ℚ) ^ depth := by
    exact_mod_cast (show depth ≤ 2 ^ depth by omega)
  have ratioPower : 4 / epsilon ≤ (2 : ℚ) ^ depth :=
    ceiling.trans castPower
  have fourBound : 4 ≤ epsilon * (2 : ℚ) ^ depth := by
    rw [div_le_iff₀ epsilonPositive] at ratioPower
    nlinarith
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℚ) ^ depth)).2
  simpa only [depth] using fourBound

theorem lowRadiusSq_binaryDepth_le {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) :
    lowRadiusSq (binaryDepth epsilon) ≤ epsilon :=
  binaryDepth_sufficient epsilonPositive

theorem highRadiusSq_binaryDepth_le {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) :
    highRadiusSq (binaryDepth epsilon) ≤ epsilon := by
  apply (show highRadiusSq (binaryDepth epsilon) ≤
      4 / (2 : ℚ) ^ binaryDepth epsilon by
    apply div_le_div_of_nonneg_left (by norm_num)
    · positivity
    · have powerNonnegative :
          0 ≤ (2 : ℚ) ^ binaryDepth epsilon := by positivity
      have nextPower : (2 : ℚ) ^ (binaryDepth epsilon + 1) =
          (2 : ℚ) ^ binaryDepth epsilon * 2 := by
        rw [pow_succ]
      linarith).trans
  exact binaryDepth_sufficient epsilonPositive

end CCLUnaryCylinder
end FTA
