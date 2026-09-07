import FTA.CCLUnaryCylinder
import CCL.RawParserProgress

/-!
# Transporting tail contraction through decoder homographies

Large-tail raw fragments occur after every completed CCL block.  This module
turns a lower bound for the parser tail norm into a rational chordal-diameter
certificate for the corresponding original-input cylinder.  All bounds are
computed from the two decoder columns, its determinant, and the raw unary
threshold.
-/

namespace FTA
namespace CCLHomographicCylinder

open CCL
open CCL.GaussianRat
open FTA.CCLChordalEnvelope
open FTA.CCLRawCylinderEnvelope

abbrev QI := CCL.GaussianRat

/-- Squared weight of the first decoder column. -/
def firstColumnWeight (matrix : Mat2 QI) : ℚ :=
  normSq matrix.a + normSq matrix.c

/-- Squared weight of the second decoder column. -/
def secondColumnWeight (matrix : Mat2 QI) : ℚ :=
  normSq matrix.b + normSq matrix.d

/-- Rational lower bound for the homogeneous output weight when `N(t) ≥ R`. -/
def outputWeightLower (matrix : Mat2 QI) (R : ℚ) : ℚ :=
  firstColumnWeight matrix * R / 2 - secondColumnWeight matrix

theorem firstColumnWeight_nonneg (matrix : Mat2 QI) :
    0 ≤ firstColumnWeight matrix := by
  exact add_nonneg (normSq_nonneg matrix.a) (normSq_nonneg matrix.c)

theorem secondColumnWeight_nonneg (matrix : Mat2 QI) :
    0 ≤ secondColumnWeight matrix := by
  exact add_nonneg (normSq_nonneg matrix.b) (normSq_nonneg matrix.d)

/-- An invertible matrix has a nonzero first column. -/
theorem firstColumn_hasNonzeroCoordinate {matrix : Mat2 QI}
    (determinant : matrix.det ≠ 0) :
    (Mat2.act matrix (Proj.omega : Proj QI)).HasNonzeroCoordinate := by
  rw [Mat2.act_omega]
  change matrix.a ≠ 0 ∨ matrix.c ≠ 0
  by_cases ha : matrix.a = 0
  · right
    intro hc
    exact determinant (by simp [Mat2.det, ha, hc])
  · exact Or.inl ha

theorem firstColumnWeight_pos {matrix : Mat2 QI}
    (determinant : matrix.det ≠ 0) : 0 < firstColumnWeight matrix := by
  simpa only [firstColumnWeight, Proj.weight, Mat2.act_omega] using
    Proj.weight_pos (firstColumn_hasNonzeroCoordinate determinant)

/-- An invertible matrix sends every affine input to a valid homogeneous pair. -/
theorem act_affine_hasNonzeroCoordinate {matrix : Mat2 QI}
    (determinant : matrix.det ≠ 0) (tail : QI) :
    (Mat2.act matrix (Proj.affine tail)).HasNonzeroCoordinate := by
  simp only [Proj.HasNonzeroCoordinate, Mat2.act, Proj.affine, mul_one]
  by_cases upper : matrix.a * tail + matrix.b = 0
  · right
    intro lower
    apply determinant
    calc
      matrix.det = matrix.a * (matrix.c * tail + matrix.d) -
          matrix.c * (matrix.a * tail + matrix.b) := by
        ext <;>
          simp only [Mat2.det, GaussianRat.add_re, GaussianRat.add_im,
            GaussianRat.sub_re, GaussianRat.sub_im, GaussianRat.mul_re,
            GaussianRat.mul_im] <;>
          ring
      _ = 0 := by rw [upper, lower]; simp
  · exact Or.inl upper

/-- The two elementary reverse-norm inequalities give a lower bound for the
weight of a decoder output without square roots or spectral estimates. -/
theorem outputWeightLower_le (matrix : Mat2 QI) (tail : QI) :
    outputWeightLower matrix (normSq tail) ≤
      (Mat2.act matrix (Proj.affine tail)).weight := by
  have upperPart := half_normSq_sub_le_normSq_sub
    (matrix.a * tail) (-matrix.b)
  have lowerPart := half_normSq_sub_le_normSq_sub
    (matrix.c * tail) (-matrix.d)
  have upperDifference : matrix.a * tail - -matrix.b =
      matrix.a * tail + matrix.b := by
    ext <;> simp
  have lowerDifference : matrix.c * tail - -matrix.d =
      matrix.c * tail + matrix.d := by
    ext <;> simp
  rw [normSq_mul, normSq_neg, upperDifference] at upperPart
  rw [normSq_mul, normSq_neg, lowerDifference] at lowerPart
  calc
    outputWeightLower matrix (normSq tail) =
        (normSq matrix.a * normSq tail / 2 - normSq matrix.b) +
          (normSq matrix.c * normSq tail / 2 - normSq matrix.d) := by
      dsimp [outputWeightLower, firstColumnWeight, secondColumnWeight]
      ring
    _ ≤ normSq (matrix.a * tail + matrix.b) +
        normSq (matrix.c * tail + matrix.d) := add_le_add upperPart lowerPart
    _ = (Mat2.act matrix (Proj.affine tail)).weight := by
      simp only [Proj.weight, Mat2.act, Proj.affine, mul_one]

theorem outputWeightLower_mono {matrix : Mat2 QI} {R : ℚ} {tail : QI}
    (tailLower : R ≤ normSq tail) :
    outputWeightLower matrix R ≤
      (Mat2.act matrix (Proj.affine tail)).weight := by
  apply le_trans _ (outputWeightLower_le matrix tail)
  have scaled := mul_le_mul_of_nonneg_left tailLower
    (firstColumnWeight_nonneg matrix)
  dsimp [outputWeightLower]
  linarith

/-- Exact rational truncation-error bound obtained from determinant and
column growth.  Positivity is supplied as a finite rational comparison. -/
def truncationRadiusSq (matrix : Mat2 QI) (R : ℚ) : ℚ :=
  normSq matrix.det /
    (firstColumnWeight matrix * outputWeightLower matrix R)

theorem truncationRadiusSq_nonneg (matrix : Mat2 QI) {R : ℚ}
    (lowerPositive : 0 < outputWeightLower matrix R) :
    0 ≤ truncationRadiusSq matrix R := by
  exact div_nonneg (normSq_nonneg matrix.det)
    (mul_nonneg (firstColumnWeight_nonneg matrix) lowerPositive.le)

theorem chordalSq_act_truncation_le
    {matrix : Mat2 QI} (determinant : matrix.det ≠ 0)
    {R : ℚ} (lowerPositive : 0 < outputWeightLower matrix R)
    {tail : QI} (tailLower : R ≤ normSq tail) :
    chordalSq (Mat2.act matrix (Proj.affine tail))
      (Mat2.act matrix (Proj.omega : Proj QI)) ≤
        truncationRadiusSq matrix R := by
  rw [Mat2.chordalSq_truncation]
  unfold truncationRadiusSq
  have outputBound :
      outputWeightLower matrix R ≤
        normSq (matrix.a * tail + matrix.b) +
          normSq (matrix.c * tail + matrix.d) := by
    have bound := outputWeightLower_mono
      (matrix := matrix) (R := R) (tail := tail) tailLower
    simpa only [Proj.weight, Mat2.act, Proj.affine, mul_one] using bound
  apply div_le_div_of_nonneg_left (normSq_nonneg matrix.det)
  · exact mul_pos (firstColumnWeight_pos determinant) lowerPositive
  · exact mul_le_mul_of_nonneg_left
      outputBound (firstColumnWeight_nonneg matrix)

/-- Diameter bound for two large-tail homogeneous images. -/
def cylinderRadiusSq (matrix : Mat2 QI) (R : ℚ) : ℚ :=
  4 * truncationRadiusSq matrix R

theorem cylinderRadiusSq_nonneg (matrix : Mat2 QI) {R : ℚ}
    (lowerPositive : 0 < outputWeightLower matrix R) :
    0 ≤ cylinderRadiusSq matrix R := by
  exact mul_nonneg (by norm_num)
    (truncationRadiusSq_nonneg matrix lowerPositive)

theorem chordalSq_act_le_cylinderRadiusSq
    {matrix : Mat2 QI} (determinant : matrix.det ≠ 0)
    {R : ℚ} (lowerPositive : 0 < outputWeightLower matrix R)
    {left right : QI} (leftLower : R ≤ normSq left)
    (rightLower : R ≤ normSq right) :
    chordalSq (Mat2.act matrix (Proj.affine left))
      (Mat2.act matrix (Proj.affine right)) ≤
        cylinderRadiusSq matrix R := by
  have triangle := chordalSq_triangle_two
    (act_affine_hasNonzeroCoordinate determinant left)
    (firstColumn_hasNonzeroCoordinate determinant)
    (act_affine_hasNonzeroCoordinate determinant right)
  have leftBound := chordalSq_act_truncation_le determinant lowerPositive
    leftLower
  have rightBound := chordalSq_act_truncation_le determinant lowerPositive
    rightLower
  rw [chordalSq_comm] at rightBound
  dsimp [cylinderRadiusSq]
  linarith

/-- A conservative output-weight target that makes the transported cylinder
radius no larger than `epsilon`.  The extra unit keeps the target strictly
positive without a separate determinant-norm cancellation argument. -/
def targetOutputWeight (matrix : Mat2 QI) (epsilon : ℚ) : ℚ :=
  4 * normSq matrix.det / (firstColumnWeight matrix * epsilon) + 1

/-- Tail norm sufficient to reach `targetOutputWeight` under the elementary
reverse-norm estimate. -/
def requiredTailWeight (matrix : Mat2 QI) (epsilon : ℚ) : ℚ :=
  2 * (secondColumnWeight matrix + targetOutputWeight matrix epsilon) /
    firstColumnWeight matrix

/-- Executable unary exponent sufficient for the decoder and requested
rational squared diameter. -/
def decoderUnaryDepth (matrix : Mat2 QI) (epsilon : ℚ) : ℕ :=
  ⌈requiredTailWeight matrix epsilon⌉₊

theorem targetOutputWeight_pos (matrix : Mat2 QI) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) :
    0 < targetOutputWeight matrix epsilon := by
  have quotientNonnegative :
      0 ≤ 4 * normSq matrix.det /
        (firstColumnWeight matrix * epsilon) := by
    exact div_nonneg
      (mul_nonneg (by norm_num) (normSq_nonneg matrix.det))
      (mul_nonneg (firstColumnWeight_nonneg matrix) epsilonPositive.le)
  dsimp only [targetOutputWeight]
  linarith

theorem requiredTailWeight_pos {matrix : Mat2 QI}
    (determinant : matrix.det ≠ 0) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) :
    0 < requiredTailWeight matrix epsilon := by
  apply div_pos
  · exact mul_pos (by norm_num)
      (add_pos_of_nonneg_of_pos (secondColumnWeight_nonneg matrix)
        (targetOutputWeight_pos matrix epsilonPositive))
  · exact firstColumnWeight_pos determinant

theorem outputWeightLower_requiredTailWeight
    {matrix : Mat2 QI} (determinant : matrix.det ≠ 0) (epsilon : ℚ) :
    outputWeightLower matrix (requiredTailWeight matrix epsilon) =
      targetOutputWeight matrix epsilon := by
  unfold outputWeightLower requiredTailWeight
  field_simp [ne_of_gt (firstColumnWeight_pos determinant)]
  ring

theorem outputWeightLower_mono_threshold (matrix : Mat2 QI)
    {lower upper : ℚ} (ordered : lower ≤ upper) :
    outputWeightLower matrix lower ≤ outputWeightLower matrix upper := by
  have scaled := mul_le_mul_of_nonneg_left ordered
    (firstColumnWeight_nonneg matrix)
  dsimp only [outputWeightLower]
  linarith

theorem requiredTailWeight_le_depth_power (matrix : Mat2 QI) (epsilon : ℚ) :
    requiredTailWeight matrix epsilon ≤
      (2 : ℚ) ^ decoderUnaryDepth matrix epsilon := by
  let depth := decoderUnaryDepth matrix epsilon
  have ceiling : requiredTailWeight matrix epsilon ≤ (depth : ℚ) := by
    exact Nat.le_ceil (requiredTailWeight matrix epsilon)
  have naturalPower : depth + 1 ≤ 2 ^ depth :=
    CCL.BinaryNormalization.succ_le_two_pow depth
  have castPower : (depth : ℚ) ≤ (2 : ℚ) ^ depth := by
    exact_mod_cast (show depth ≤ 2 ^ depth by omega)
  exact ceiling.trans (by simpa only [depth] using castPower)

theorem outputWeightLower_depth_power_pos
    {matrix : Mat2 QI} (determinant : matrix.det ≠ 0) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) :
    0 < outputWeightLower matrix
      ((2 : ℚ) ^ decoderUnaryDepth matrix epsilon) := by
  have lowerBound := outputWeightLower_mono_threshold matrix
    (requiredTailWeight_le_depth_power matrix epsilon)
  rw [outputWeightLower_requiredTailWeight determinant epsilon] at lowerBound
  exact (targetOutputWeight_pos matrix epsilonPositive).trans_le lowerBound

/-- The computable decoder-specific unary depth forces the transported raw
cylinder diameter below any positive rational request. -/
theorem cylinderRadiusSq_depth_power_le
    {matrix : Mat2 QI} (determinant : matrix.det ≠ 0) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) :
    cylinderRadiusSq matrix
      ((2 : ℚ) ^ decoderUnaryDepth matrix epsilon) ≤ epsilon := by
  let depthPower : ℚ := (2 : ℚ) ^ decoderUnaryDepth matrix epsilon
  have firstPositive := firstColumnWeight_pos determinant
  have targetPositive := targetOutputWeight_pos matrix epsilonPositive
  have outputPositive : 0 < outputWeightLower matrix depthPower := by
    simpa only [depthPower] using
      outputWeightLower_depth_power_pos determinant epsilonPositive
  have outputBound : targetOutputWeight matrix epsilon ≤
      outputWeightLower matrix depthPower := by
    have bound := outputWeightLower_mono_threshold matrix
      (requiredTailWeight_le_depth_power matrix epsilon)
    rw [outputWeightLower_requiredTailWeight determinant epsilon] at bound
    simpa only [depthPower] using bound
  have targetFraction :
      4 * normSq matrix.det /
          (firstColumnWeight matrix * epsilon) ≤
        targetOutputWeight matrix epsilon := by
    dsimp only [targetOutputWeight]
    linarith
  have numeratorBound :
      4 * normSq matrix.det ≤
        targetOutputWeight matrix epsilon *
          (firstColumnWeight matrix * epsilon) :=
    (div_le_iff₀ (mul_pos firstPositive epsilonPositive)).mp targetFraction
  have denominatorBound :
      firstColumnWeight matrix * targetOutputWeight matrix epsilon ≤
        firstColumnWeight matrix * outputWeightLower matrix depthPower :=
    mul_le_mul_of_nonneg_left outputBound firstPositive.le
  unfold cylinderRadiusSq truncationRadiusSq
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (mul_pos firstPositive outputPositive)).2
  calc
    4 * normSq matrix.det ≤
        targetOutputWeight matrix epsilon *
          (firstColumnWeight matrix * epsilon) := numeratorBound
    _ = epsilon *
        (firstColumnWeight matrix * targetOutputWeight matrix epsilon) := by
      ring
    _ ≤ epsilon *
        (firstColumnWeight matrix * outputWeightLower matrix depthPower) :=
      mul_le_mul_of_nonneg_left denominatorBound epsilonPositive.le

/-- Homogeneous decoder output is a nonzero rescaling of its affine
homographic value whenever the parser denominator is nonzero. -/
theorem act_affine_eq_scale_homographic (matrix : Mat2 QI) (tail : QI)
    (denominator : RawParserSemantics.denominator matrix tail ≠ 0) :
    Mat2.act matrix (Proj.affine tail) =
      (Proj.affine (RatBox.homographic matrix tail)).scale
        (RawParserSemantics.denominator matrix tail) := by
  have denominator' : matrix.c * tail + matrix.d ≠ 0 := by
    simpa only [RawParserSemantics.denominator] using denominator
  apply Proj.ext
  · simp only [Mat2.act, Proj.affine, Proj.scale, mul_one,
      RawParserSemantics.denominator, RatBox.homographic]
    calc
      matrix.a * tail + matrix.b =
          (matrix.a * tail + matrix.b) *
            (inv (matrix.c * tail + matrix.d) *
              (matrix.c * tail + matrix.d)) := by
        rw [inv_mul _ denominator', _root_.mul_one]
      _ = (matrix.c * tail + matrix.d) *
          ((matrix.a * tail + matrix.b) *
            inv (matrix.c * tail + matrix.d)) := by ring
  · simp only [Mat2.act, Proj.affine, Proj.scale,
      RawParserSemantics.denominator, _root_.mul_one]

theorem chordalSq_homographic_eq_act
    (matrix : Mat2 QI) {left right : QI}
    (leftDenominator : RawParserSemantics.denominator matrix left ≠ 0)
    (rightDenominator : RawParserSemantics.denominator matrix right ≠ 0) :
    chordalSq (Proj.affine (RatBox.homographic matrix left))
        (Proj.affine (RatBox.homographic matrix right)) =
      chordalSq (Mat2.act matrix (Proj.affine left))
        (Mat2.act matrix (Proj.affine right)) := by
  rw [act_affine_eq_scale_homographic matrix left leftDenominator,
    act_affine_eq_scale_homographic matrix right rightDenominator,
    chordalSq_scale_left _ leftDenominator,
    chordalSq_scale_right _ rightDenominator]

/-- An arbitrary word in the initial-low unary phase still has the identity
decoder, so the parser's active small-tail inequality applies directly to its
represented affine inputs. -/
theorem lowUnary_norm_upper_of_phase
    {word : Prefix.Word} {count : ℕ} {input : QI}
    (phase : (RawParser.parse word).phase = .lowUnary (count + 1))
    (represented : RawParserSemantics.Represented word input) :
    (2 : ℚ) ^ count * normSq input < 1 := by
  rcases represented with ⟨tail, _denominator, inputEq, holds⟩
  have matrixEq :=
    RawParser.parse_matrix_eq_identity_of_lowUnary phase
  rw [matrixEq, CCLUnaryCylinder.identity_homographic] at inputEq
  subst input
  have active := holds.2
  rw [phase] at active
  exact active

/-- The standalone initial-low unary diameter theorem, generalized from its
canonical word spelling to every parser word with the same certified phase. -/
theorem lowUnary_chordalSq_le_of_phase
    {word : Prefix.Word} {count : ℕ} {left right : QI}
    (phase : (RawParser.parse word).phase = .lowUnary (count + 1))
    (leftRepresented : RawParserSemantics.Represented word left)
    (rightRepresented : RawParserSemantics.Represented word right) :
    chordalSq (Proj.affine left) (Proj.affine right) ≤
      CCLUnaryCylinder.lowRadiusSq count := by
  let threshold : ℚ := (2 : ℚ) ^ count
  have thresholdPositive : 0 < threshold := by
    dsimp [threshold]
    positivity
  have leftSmall : normSq left < 1 / threshold := by
    apply (lt_div_iff₀ thresholdPositive).2
    simpa only [threshold, _root_.mul_comm] using
      lowUnary_norm_upper_of_phase phase leftRepresented
  have rightSmall : normSq right < 1 / threshold := by
    apply (lt_div_iff₀ thresholdPositive).2
    simpa only [threshold, _root_.mul_comm] using
      lowUnary_norm_upper_of_phase phase rightRepresented
  have difference := normSq_sub_le_two left right
  have affineBound :=
    CCLChordalEnvelope.chordalSq_affine_le_normSq left right
  have differenceBound : normSq (left - right) ≤ 4 / threshold := by
    have radiusIdentity :
        4 / threshold = 2 * (1 / threshold + 1 / threshold) := by
      ring
    rw [radiusIdentity]
    linarith
  exact affineBound.trans (by
    simpa only [CCLUnaryCylinder.lowRadiusSq, threshold] using differenceBound)

/-- Arbitrary-word envelope for a nonempty initial-low unary run. -/
def lowUnaryEnvelopeOfPhase (word : Prefix.Word) (count : ℕ)
    (phase : (RawParser.parse word).phase = .lowUnary (count + 1)) :
    RawCylinderEnvelope where
  truncation := ⟨word⟩
  radiusSq := CCLUnaryCylinder.lowRadiusSq count
  radiusSq_nonneg := CCLUnaryCylinder.lowRadiusSq_nonneg count
  diameter := lowUnary_chordalSq_le_of_phase phase

/-- Squared chordal diameter bound retained after the initial-low delimiter
and through zero, one, or two sector bits. -/
def initialLowSectorRadiusSq (exponent : ℕ) : ℚ :=
  8 / (2 : ℚ) ^ exponent

theorem initialLowSectorRadiusSq_nonneg (exponent : ℕ) :
    0 ≤ initialLowSectorRadiusSq exponent := by
  dsimp [initialLowSectorRadiusSq]
  positivity

theorem initialLowSectorRadiusSq_le_of_le {smaller larger : ℕ}
    (ordered : smaller ≤ larger) :
    initialLowSectorRadiusSq larger ≤
      initialLowSectorRadiusSq smaller := by
  apply div_le_div_of_nonneg_left (by norm_num)
  · positivity
  · exact_mod_cast
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) ordered

theorem initialLowSector_norm_upper_of_phase
    {word : Prefix.Word} {exponent : ℕ} {bits : RawParser.SectorBits}
    {input : QI}
    (phase : (RawParser.parse word).phase =
      .sector .initialLow exponent bits)
    (represented : RawParserSemantics.Represented word input) :
    (2 : ℚ) ^ exponent * normSq input < 2 := by
  rcases represented with ⟨tail, _denominator, inputEq, holds⟩
  have matrixEq :=
    RawParser.parse_matrix_eq_identity_of_initialLow_sector phase
  rw [matrixEq, CCLUnaryCylinder.identity_homographic] at inputEq
  subst input
  have active := holds.2
  rw [phase] at active
  exact active.1.2

theorem initialLowSector_chordalSq_le_of_phase
    {word : Prefix.Word} {exponent : ℕ} {bits : RawParser.SectorBits}
    {left right : QI}
    (phase : (RawParser.parse word).phase =
      .sector .initialLow exponent bits)
    (leftRepresented : RawParserSemantics.Represented word left)
    (rightRepresented : RawParserSemantics.Represented word right) :
    chordalSq (Proj.affine left) (Proj.affine right) ≤
      initialLowSectorRadiusSq exponent := by
  let threshold : ℚ := (2 : ℚ) ^ exponent
  have thresholdPositive : 0 < threshold := by
    dsimp [threshold]
    positivity
  have leftSmall : normSq left < 2 / threshold := by
    apply (lt_div_iff₀ thresholdPositive).2
    simpa only [threshold, _root_.mul_comm] using
      initialLowSector_norm_upper_of_phase phase leftRepresented
  have rightSmall : normSq right < 2 / threshold := by
    apply (lt_div_iff₀ thresholdPositive).2
    simpa only [threshold, _root_.mul_comm] using
      initialLowSector_norm_upper_of_phase phase rightRepresented
  have difference := normSq_sub_le_two left right
  have affineBound :=
    CCLChordalEnvelope.chordalSq_affine_le_normSq left right
  have differenceBound : normSq (left - right) ≤ 8 / threshold := by
    have radiusIdentity :
        8 / threshold = 2 * (2 / threshold + 2 / threshold) := by
      ring
    rw [radiusIdentity]
    linarith
  exact affineBound.trans (by
    simpa only [initialLowSectorRadiusSq, threshold] using differenceBound)

/-- Arbitrary-word envelope for a partial initial-low sector code. -/
def initialLowSectorEnvelopeOfPhase (word : Prefix.Word) (exponent : ℕ)
    (bits : RawParser.SectorBits)
    (phase : (RawParser.parse word).phase =
      .sector .initialLow exponent bits) : RawCylinderEnvelope where
  truncation := ⟨word⟩
  radiusSq := initialLowSectorRadiusSq exponent
  radiusSq_nonneg := initialLowSectorRadiusSq_nonneg exponent
  diameter := initialLowSector_chordalSq_le_of_phase phase

/-- One common initial-low counter works both before and after the delimiter:
at `binaryDepth epsilon + 1`, the sector's extra factor two is absorbed by
the next binary power. -/
def initialLowContractionDepth (epsilon : ℚ) : ℕ :=
  CCLUnaryCylinder.binaryDepth epsilon + 1

theorem lowUnaryRadiusSq_initialLowContractionDepth_le
    {epsilon : ℚ} (epsilonPositive : 0 < epsilon) :
    CCLUnaryCylinder.lowRadiusSq
      (initialLowContractionDepth epsilon - 1) ≤ epsilon := by
  simpa [initialLowContractionDepth] using
    CCLUnaryCylinder.lowRadiusSq_binaryDepth_le epsilonPositive

theorem initialLowSectorRadiusSq_contractionDepth_le
    {epsilon : ℚ} (epsilonPositive : 0 < epsilon) :
    initialLowSectorRadiusSq (initialLowContractionDepth epsilon) ≤
      epsilon := by
  have binaryBound :=
    CCLUnaryCylinder.binaryDepth_sufficient epsilonPositive
  rw [initialLowSectorRadiusSq, initialLowContractionDepth, pow_succ]
  convert binaryBound using 1
  ring

/-- Finite tail-lower-bound data for one arbitrary raw parser prefix. -/
structure ParserTailLowerBound (word : Prefix.Word) where
  threshold : ℚ
  thresholdPositive : 0 < threshold
  lower : ∀ {tail : QI}, (RawParser.parse word).Holds tail →
    threshold ≤ normSq tail
  outputLowerPositive :
    0 < outputWeightLower (RawParser.parse word).matrix threshold

/-- Radial parser information before the finite output-weight positivity
comparison is attempted. -/
structure ParserRadialLowerBound (word : Prefix.Word) where
  threshold : ℚ
  thresholdPositive : 0 < threshold
  lower : ∀ {tail : QI}, (RawParser.parse word).Holds tail →
    threshold ≤ normSq tail

def ParserRadialLowerBound.withOutputPositive {word : Prefix.Word}
    (bound : ParserRadialLowerBound word)
    (outputLowerPositive :
      0 < outputWeightLower (RawParser.parse word).matrix bound.threshold) :
    ParserTailLowerBound word where
  threshold := bound.threshold
  thresholdPositive := bound.thresholdPositive
  lower := bound.lower
  outputLowerPositive := outputLowerPositive

/-- Inspect the finite parser phase and extract its available large-tail
power bound.  Initial-low phases use their separate small-tail theorem and
therefore return `none` here. -/
def parserRadialLowerBound? (word : Prefix.Word) :
    Option (ParserRadialLowerBound word) := by
  cases phase : (RawParser.parse word).phase with
  | initial => exact none
  | highUnary count =>
      exact some
        { threshold := (2 : ℚ) ^ count
          thresholdPositive := by positivity
          lower := by
            intro tail holds
            have active := holds.2
            rw [phase] at active
            exact active }
  | lowUnary _ => exact none
  | loopUnary count =>
      exact some
        { threshold := (2 : ℚ) ^ count
          thresholdPositive := by positivity
          lower := by
            intro tail holds
            have active := holds.2
            rw [phase] at active
            exact active.le }
  | sector kind exponent bits =>
      cases kind with
      | initialLow => exact none
      | initialHigh =>
          exact some
            { threshold := (2 : ℚ) ^ exponent
              thresholdPositive := by positivity
              lower := by
                intro tail holds
                have active := holds.2
                rw [phase] at active
                exact active.1.1 }
      | loop =>
          exact some
            { threshold := (2 : ℚ) ^ exponent
              thresholdPositive := by positivity
              lower := by
                intro tail holds
                have active := holds.2
                rw [phase] at active
                exact active.1.1.le }

/-- Transport any certified large-tail parser prefix to a cylinder-diameter
certificate on original affine inputs. -/
def envelopeOfTailLowerBound {word : Prefix.Word}
    (bound : ParserTailLowerBound word) : RawCylinderEnvelope where
  truncation := ⟨word⟩
  radiusSq := cylinderRadiusSq (RawParser.parse word).matrix bound.threshold
  radiusSq_nonneg := cylinderRadiusSq_nonneg _ bound.outputLowerPositive
  diameter := by
    intro left right leftRepresented rightRepresented
    rcases leftRepresented with
      ⟨leftTail, leftDenominator, leftEq, leftHolds⟩
    rcases rightRepresented with
      ⟨rightTail, rightDenominator, rightEq, rightHolds⟩
    rw [leftEq, rightEq,
      chordalSq_homographic_eq_act _ leftDenominator rightDenominator]
    exact chordalSq_act_le_cylinderRadiusSq
      (RawParser.parse_det_ne word) bound.outputLowerPositive
      (bound.lower leftHolds) (bound.lower rightHolds)

theorem two_pow_le_two_pow {smaller larger : ℕ}
    (ordered : smaller ≤ larger) :
    (2 : ℚ) ^ smaller ≤ (2 : ℚ) ^ larger := by
  exact_mod_cast
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) ordered

/-- A phase whose active predicate implies the decoder-specific computed tail
threshold receives the same transported contraction certificate, even if its
unary counter has already advanced beyond the first sufficient exponent. -/
def computedDepthEnvelope (word : Prefix.Word) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon)
    (lower : ∀ {tail : QI}, (RawParser.parse word).Holds tail →
      (2 : ℚ) ^ decoderUnaryDepth (RawParser.parse word).matrix epsilon ≤
        normSq tail) : RawCylinderEnvelope :=
  envelopeOfTailLowerBound
    { threshold :=
        (2 : ℚ) ^ decoderUnaryDepth (RawParser.parse word).matrix epsilon
      thresholdPositive := by positivity
      lower := lower
      outputLowerPositive := outputWeightLower_depth_power_pos
        (RawParser.parse_det_ne word) epsilonPositive }

theorem computedDepthEnvelope_radiusSq_le
    (word : Prefix.Word) {epsilon : ℚ} (epsilonPositive : 0 < epsilon)
    (lower : ∀ {tail : QI}, (RawParser.parse word).Holds tail →
      (2 : ℚ) ^ decoderUnaryDepth (RawParser.parse word).matrix epsilon ≤
        normSq tail) :
    (computedDepthEnvelope word epsilon epsilonPositive lower).radiusSq ≤
      epsilon := by
  change cylinderRadiusSq (RawParser.parse word).matrix
    ((2 : ℚ) ^ decoderUnaryDepth
      (RawParser.parse word).matrix epsilon) ≤ epsilon
  exact cylinderRadiusSq_depth_power_le
    (RawParser.parse_det_ne word) epsilonPositive

/-- Total finite attempt to construct the current homographic cylinder
envelope.  Failure means only that the conservative output-weight lower bound
is not yet positive (or that the parser is in an initial-low phase). -/
def automaticEnvelope? (word : Prefix.Word) : Option RawCylinderEnvelope :=
  match parserRadialLowerBound? word with
  | none => none
  | some bound =>
      if positive :
          0 < outputWeightLower (RawParser.parse word).matrix bound.threshold
      then some (envelopeOfTailLowerBound
        (bound.withOutputPositive positive))
      else none

theorem automaticEnvelope?_word {word : Prefix.Word}
    {envelope : RawCylinderEnvelope}
    (found : automaticEnvelope? word = some envelope) :
    envelope.truncation.word = word := by
  unfold automaticEnvelope? at found
  split at found
  · cases found
  · split at found
    · cases found
      rfl
    · cases found

/-- A parser state in its subsequent-loop unary phase supplies the exact
large-tail threshold needed by the homographic cylinder bound. -/
def loopUnaryTailLowerBound (word : Prefix.Word) (count : ℕ)
    (phase : (RawParser.parse word).phase = .loopUnary count)
    (outputLowerPositive :
      0 < outputWeightLower (RawParser.parse word).matrix ((2 : ℚ) ^ count)) :
    ParserTailLowerBound word where
  threshold := (2 : ℚ) ^ count
  thresholdPositive := by positivity
  lower := by
    intro tail holds
    have active := holds.2
    rw [phase] at active
    exact active.le
  outputLowerPositive := outputLowerPositive

/-- The initial-high unary phase is handled by the same generic transport. -/
def highUnaryTailLowerBound (word : Prefix.Word) (count : ℕ)
    (phase : (RawParser.parse word).phase = .highUnary count)
    (outputLowerPositive :
      0 < outputWeightLower (RawParser.parse word).matrix ((2 : ℚ) ^ count)) :
    ParserTailLowerBound word where
  threshold := (2 : ℚ) ^ count
  thresholdPositive := by positivity
  lower := by
    intro tail holds
    have active := holds.2
    rw [phase] at active
    exact active
  outputLowerPositive := outputLowerPositive

/-- A partial sector code following a loop delimiter retains the same radial
large-tail bound, regardless of whether zero, one, or two sector bits were
read. -/
def loopSectorTailLowerBound (word : Prefix.Word) (exponent : ℕ)
    (bits : RawParser.SectorBits)
    (phase : (RawParser.parse word).phase = .sector .loop exponent bits)
    (outputLowerPositive :
      0 < outputWeightLower (RawParser.parse word).matrix
        ((2 : ℚ) ^ exponent)) :
    ParserTailLowerBound word where
  threshold := (2 : ℚ) ^ exponent
  thresholdPositive := by positivity
  lower := by
    intro tail holds
    have active := holds.2
    rw [phase] at active
    exact active.1.1.le
  outputLowerPositive := outputLowerPositive

/-- A partial sector code following an initial-high delimiter likewise keeps
the completed unary threshold. -/
def highSectorTailLowerBound (word : Prefix.Word) (exponent : ℕ)
    (bits : RawParser.SectorBits)
    (phase : (RawParser.parse word).phase = .sector .initialHigh exponent bits)
    (outputLowerPositive :
      0 < outputWeightLower (RawParser.parse word).matrix
        ((2 : ℚ) ^ exponent)) :
    ParserTailLowerBound word where
  threshold := (2 : ℚ) ^ exponent
  thresholdPositive := by positivity
  lower := by
    intro tail holds
    have active := holds.2
    rw [phase] at active
    exact active.1.1
  outputLowerPositive := outputLowerPositive

/-- A loop-unary prefix that has reached its decoder-specific computed depth
comes with a cylinder envelope below the requested squared diameter. -/
def loopUnaryContractedEnvelope (word : Prefix.Word) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon)
    (phase : (RawParser.parse word).phase = .loopUnary
      (decoderUnaryDepth (RawParser.parse word).matrix epsilon)) :
    RawCylinderEnvelope :=
  envelopeOfTailLowerBound
    (loopUnaryTailLowerBound word
      (decoderUnaryDepth (RawParser.parse word).matrix epsilon) phase
      (outputWeightLower_depth_power_pos
        (RawParser.parse_det_ne word) epsilonPositive))

theorem loopUnaryContractedEnvelope_radiusSq_le
    (word : Prefix.Word) {epsilon : ℚ} (epsilonPositive : 0 < epsilon)
    (phase : (RawParser.parse word).phase = .loopUnary
      (decoderUnaryDepth (RawParser.parse word).matrix epsilon)) :
    (loopUnaryContractedEnvelope word epsilon epsilonPositive phase).radiusSq ≤
      epsilon := by
  change cylinderRadiusSq (RawParser.parse word).matrix
    ((2 : ℚ) ^ decoderUnaryDepth (RawParser.parse word).matrix epsilon) ≤
      epsilon
  exact cylinderRadiusSq_depth_power_le
    (RawParser.parse_det_ne word) epsilonPositive

/-- The initial-high unary phase has the same computed contraction guarantee. -/
def highUnaryContractedEnvelope (word : Prefix.Word) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon)
    (phase : (RawParser.parse word).phase = .highUnary
      (decoderUnaryDepth (RawParser.parse word).matrix epsilon)) :
    RawCylinderEnvelope :=
  envelopeOfTailLowerBound
    (highUnaryTailLowerBound word
      (decoderUnaryDepth (RawParser.parse word).matrix epsilon) phase
      (outputWeightLower_depth_power_pos
        (RawParser.parse_det_ne word) epsilonPositive))

theorem highUnaryContractedEnvelope_radiusSq_le
    (word : Prefix.Word) {epsilon : ℚ} (epsilonPositive : 0 < epsilon)
    (phase : (RawParser.parse word).phase = .highUnary
      (decoderUnaryDepth (RawParser.parse word).matrix epsilon)) :
    (highUnaryContractedEnvelope word epsilon epsilonPositive phase).radiusSq ≤
      epsilon := by
  change cylinderRadiusSq (RawParser.parse word).matrix
    ((2 : ℚ) ^ decoderUnaryDepth (RawParser.parse word).matrix epsilon) ≤
      epsilon
  exact cylinderRadiusSq_depth_power_le
    (RawParser.parse_det_ne word) epsilonPositive

/-- Any partial loop-sector code retains the computed radial contraction
bound reached immediately before its delimiter. -/
def loopSectorContractedEnvelope (word : Prefix.Word) (bits : RawParser.SectorBits)
    (epsilon : ℚ) (epsilonPositive : 0 < epsilon)
    (phase : (RawParser.parse word).phase = .sector .loop
      (decoderUnaryDepth (RawParser.parse word).matrix epsilon) bits) :
    RawCylinderEnvelope :=
  envelopeOfTailLowerBound
    (loopSectorTailLowerBound word
      (decoderUnaryDepth (RawParser.parse word).matrix epsilon) bits phase
      (outputWeightLower_depth_power_pos
        (RawParser.parse_det_ne word) epsilonPositive))

theorem loopSectorContractedEnvelope_radiusSq_le
    (word : Prefix.Word) (bits : RawParser.SectorBits) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon)
    (phase : (RawParser.parse word).phase = .sector .loop
      (decoderUnaryDepth (RawParser.parse word).matrix epsilon) bits) :
    (loopSectorContractedEnvelope word bits epsilon epsilonPositive phase).radiusSq ≤
      epsilon := by
  change cylinderRadiusSq (RawParser.parse word).matrix
    ((2 : ℚ) ^ decoderUnaryDepth (RawParser.parse word).matrix epsilon) ≤
      epsilon
  exact cylinderRadiusSq_depth_power_le
    (RawParser.parse_det_ne word) epsilonPositive

/-- Partial initial-high sector codes also retain their computed contraction
bound until the decoder block is completed. -/
def highSectorContractedEnvelope (word : Prefix.Word) (bits : RawParser.SectorBits)
    (epsilon : ℚ) (epsilonPositive : 0 < epsilon)
    (phase : (RawParser.parse word).phase = .sector .initialHigh
      (decoderUnaryDepth (RawParser.parse word).matrix epsilon) bits) :
    RawCylinderEnvelope :=
  envelopeOfTailLowerBound
    (highSectorTailLowerBound word
      (decoderUnaryDepth (RawParser.parse word).matrix epsilon) bits phase
      (outputWeightLower_depth_power_pos
        (RawParser.parse_det_ne word) epsilonPositive))

theorem highSectorContractedEnvelope_radiusSq_le
    (word : Prefix.Word) (bits : RawParser.SectorBits) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon)
    (phase : (RawParser.parse word).phase = .sector .initialHigh
      (decoderUnaryDepth (RawParser.parse word).matrix epsilon) bits) :
    (highSectorContractedEnvelope word bits epsilon epsilonPositive phase).radiusSq ≤
      epsilon := by
  change cylinderRadiusSq (RawParser.parse word).matrix
    ((2 : ℚ) ^ decoderUnaryDepth (RawParser.parse word).matrix epsilon) ≤
      epsilon
  exact cylinderRadiusSq_depth_power_le
    (RawParser.parse_det_ne word) epsilonPositive

end CCLHomographicCylinder
end FTA
