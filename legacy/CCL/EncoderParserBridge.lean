import CCL.Encoding.Encoder
import CCL.Encoding.RawParserSemantics

/-!
# Encoder comparisons as raw-parser predicates

This module connects the bounded integer normalization data carried by the
terminating encoder to the rational predicates used by the arbitrary-prefix
parser.  It is the arithmetic half of the encoder/parser trace theorem.
-/

namespace CCL
namespace EncoderParserBridge

open GaussianRat Integral

abbrev QI := GaussianRat

/-- A certified high normalization gives exactly the parser's closed/open
high radial bracket on the represented fraction value. -/
theorem high_radialBracket (fraction : Frac)
    (scan : BinaryNormalization.HighResult
      (normNat fraction.num) (normNat fraction.den)) :
    RawParser.radialBracket .initialHigh scan.exponent fraction.value := by
  rw [RawParser.radialBracket, Frac.normSq_value]
  have denominatorPositive : (0 : ℚ) < normNat fraction.den := by
    exact_mod_cast normNat_pos fraction.den_ne
  constructor
  · apply (le_div_iff₀ denominatorPositive).2
    exact_mod_cast scan.lower
  · apply (div_lt_iff₀ denominatorPositive).2
    exact_mod_cast scan.upper

/-- A certified low normalization gives exactly the parser's weak/strict low
radial bracket. -/
theorem low_radialBracket (fraction : Frac)
    (scan : BinaryNormalization.LowResult
      (normNat fraction.num) (normNat fraction.den)) :
    RawParser.radialBracket .initialLow scan.exponent fraction.value := by
  rw [RawParser.radialBracket, Frac.normSq_value]
  have denominatorPositive : (0 : ℚ) < normNat fraction.den := by
    exact_mod_cast normNat_pos fraction.den_ne
  rw [show (2 : ℚ) ^ scan.exponent *
      ((normNat fraction.num : ℚ) / normNat fraction.den) =
      ((2 : ℚ) ^ scan.exponent * normNat fraction.num) /
        normNat fraction.den by ring]
  constructor
  · apply (le_div_iff₀ denominatorPositive).2
    norm_num
    exact_mod_cast scan.lower
  · apply (div_lt_iff₀ denominatorPositive).2
    exact_mod_cast scan.upper

/-- A certified loop normalization gives exactly the parser's strict/closed
loop radial bracket. -/
theorem loop_radialBracket (fraction : Frac)
    (scan : BinaryNormalization.LoopResult
      (normNat fraction.num) (normNat fraction.den)) :
    RawParser.radialBracket .loop scan.exponent fraction.value := by
  rw [RawParser.radialBracket, Frac.normSq_value]
  have denominatorPositive : (0 : ℚ) < normNat fraction.den := by
    exact_mod_cast normNat_pos fraction.den_ne
  constructor
  · apply (lt_div_iff₀ denominatorPositive).2
    exact_mod_cast scan.lower
  · apply (div_le_iff₀ denominatorPositive).2
    exact_mod_cast scan.upper

/-- Multiply a fraction denominator by the integral power used by high and
loop normalization. -/
def scaleDenominator (fraction : Frac) (exponent : ℕ) : Frac :=
  ⟨fraction.num, gammaInt ^ exponent * fraction.den,
    mul_ne_zero (pow_ne_zero _ (by decide)) fraction.den_ne⟩

/-- Multiply a fraction numerator by the integral power used by low initial
normalization. -/
def scaleNumerator (fraction : Frac) (exponent : ℕ) : Frac :=
  ⟨gammaInt ^ exponent * fraction.num, fraction.den, fraction.den_ne⟩

theorem scaleDenominator_value (fraction : Frac) (exponent : ℕ) :
    (scaleDenominator fraction exponent).value =
      fraction.value * inv (natPow gamma exponent) := by
  simp only [scaleDenominator, Frac.value, toRat_mul, toRat_gammaInt_pow]
  change toRat fraction.num *
      (natPow gamma exponent * toRat fraction.den)⁻¹ =
    toRat fraction.num * (toRat fraction.den)⁻¹ *
      (natPow gamma exponent)⁻¹
  rw [mul_inv_rev]
  ring

theorem scaleNumerator_value (fraction : Frac) (exponent : ℕ) :
    (scaleNumerator fraction exponent).value =
      natPow gamma exponent * fraction.value := by
  simp only [scaleNumerator, Frac.value, toRat_mul, toRat_gammaInt_pow]
  ring

/-- The normalized fractions constructed by the encoder agree exactly with
the parser's rational normalization coordinate. -/
theorem scaleDenominator_normalizedValue
    (kind : RawParser.BlockKind) (fraction : Frac) (exponent : ℕ)
    (notLow : kind ≠ .initialLow) :
    (scaleDenominator fraction exponent).value =
      RawParser.normalizedValue kind exponent fraction.value := by
  cases kind <;> simp_all [RawParser.normalizedValue, scaleDenominator_value]

theorem scaleNumerator_normalizedValue
    (fraction : Frac) (exponent : ℕ) :
    (scaleNumerator fraction exponent).value =
      RawParser.normalizedValue .initialLow exponent fraction.value := by
  exact scaleNumerator_value fraction exponent

/-- The public scan names used to expose the exponents hidden inside the
encoder's proof-producing constructors. -/
def highScan (fraction : Frac)
    (high : 2 * normNat fraction.den ≤ normNat fraction.num) :=
  BinaryNormalization.high (normNat fraction.num) (normNat fraction.den)
    (normNat_pos fraction.den_ne) high

def lowScan (fraction : Frac) (numerator : fraction.num ≠ 0)
    (low : normNat fraction.num < 2 * normNat fraction.den) :=
  BinaryNormalization.low (normNat fraction.num) (normNat fraction.den)
    (normNat_pos numerator) (normNat_pos fraction.den_ne) low

def loopScan (fraction : Frac)
    (outside : normNat fraction.den < normNat fraction.num) :=
  BinaryNormalization.loop (normNat fraction.num) (normNat fraction.den)
    (normNat_pos fraction.den_ne) outside

theorem initialHigh_header (fraction : Frac) (numerator : fraction.num ≠ 0)
    (high : 2 * normNat fraction.den ≤ normNat fraction.num) :
    (CCLEncoder.initialHigh fraction numerator high).header =
      List.replicate (highScan fraction high).exponent true ++ [false] := by
  rfl

theorem initialHigh_fraction
    (fraction : Frac) (numerator : fraction.num ≠ 0)
    (high : 2 * normNat fraction.den ≤ normNat fraction.num) :
    (CCLEncoder.initialHigh fraction numerator high).annulus.frac =
      scaleDenominator fraction (highScan fraction high).exponent := by
  rfl

theorem initialLow_header (fraction : Frac) (numerator : fraction.num ≠ 0)
    (low : normNat fraction.num < 2 * normNat fraction.den) :
    (CCLEncoder.initialLow fraction numerator low).header =
      false :: List.replicate (lowScan fraction numerator low).exponent true ++
        [false] := by
  rfl

theorem initialLow_fraction
    (fraction : Frac) (numerator : fraction.num ≠ 0)
    (low : normNat fraction.num < 2 * normNat fraction.den) :
    (CCLEncoder.initialLow fraction numerator low).annulus.frac =
      scaleNumerator fraction (lowScan fraction numerator low).exponent := by
  rfl

theorem normalizeLoop_exponent
    (fraction : Frac) (oldMeasure : ℕ)
    (outside : normNat fraction.den < normNat fraction.num)
    (numeratorMeasure : normNat fraction.num = oldMeasure) :
    (CCLEncoder.normalizeLoop fraction oldMeasure outside numeratorMeasure).exponent =
      (loopScan fraction outside).exponent := by
  rfl

theorem normalizeLoop_fraction
    (fraction : Frac) (oldMeasure : ℕ)
    (outside : normNat fraction.den < normNat fraction.num)
    (numeratorMeasure : normNat fraction.num = oldMeasure) :
    (CCLEncoder.normalizeLoop fraction oldMeasure outside numeratorMeasure).annulus.frac =
      scaleDenominator fraction (loopScan fraction outside).exponent := by
  rfl

/-- The first selected sector in each encoder branch satisfies the parser's
entire completed-block predicate on the pre-normalization value. -/
theorem initialHigh_fullBlock
    (fraction : Frac) (numerator : fraction.num ≠ 0)
    (high : 2 * normNat fraction.den ≤ normNat fraction.num) :
    let initial := CCLEncoder.initialHigh fraction numerator high
    let exponent := (highScan fraction high).exponent
    RawParser.fullBlockHolds .initialHigh exponent
      (Sector.select initial.annulus.frac.value) fraction.value := by
  dsimp only
  constructor
  · exact high_radialBracket fraction (highScan fraction high)
  · have normalized :
        RawParser.normalizedValue .initialHigh (highScan fraction high).exponent
            fraction.value =
          (CCLEncoder.initialHigh fraction numerator high).annulus.frac.value := by
      rw [initialHigh_fraction, scaleDenominator_normalizedValue]
      decide
    rw [normalized]
    exact Sector.select_spec _
      (CCLEncoder.initialHigh fraction numerator high).annulus.band.1

theorem initialLow_fullBlock
    (fraction : Frac) (numerator : fraction.num ≠ 0)
    (low : normNat fraction.num < 2 * normNat fraction.den) :
    let initial := CCLEncoder.initialLow fraction numerator low
    let exponent := (lowScan fraction numerator low).exponent
    RawParser.fullBlockHolds .initialLow exponent
      (Sector.select initial.annulus.frac.value) fraction.value := by
  dsimp only
  constructor
  · exact low_radialBracket fraction (lowScan fraction numerator low)
  · have normalized :
        RawParser.normalizedValue .initialLow
            (lowScan fraction numerator low).exponent fraction.value =
          (CCLEncoder.initialLow fraction numerator low).annulus.frac.value := by
      rw [initialLow_fraction, scaleNumerator_normalizedValue]
    rw [normalized]
    exact Sector.select_spec _
      (CCLEncoder.initialLow fraction numerator low).annulus.band.1

theorem normalizeLoop_fullBlock
    (fraction : Frac) (oldMeasure : ℕ)
    (outside : normNat fraction.den < normNat fraction.num)
    (numeratorMeasure : normNat fraction.num = oldMeasure) :
    let normalized :=
      CCLEncoder.normalizeLoop fraction oldMeasure outside numeratorMeasure
    let exponent := (loopScan fraction outside).exponent
    RawParser.fullBlockHolds .loop exponent
      (Sector.select normalized.annulus.frac.value) fraction.value := by
  dsimp only
  constructor
  · exact loop_radialBracket fraction (loopScan fraction outside)
  · have normalizedValue :
        RawParser.normalizedValue .loop (loopScan fraction outside).exponent
            fraction.value =
          (CCLEncoder.normalizeLoop fraction oldMeasure outside
            numeratorMeasure).annulus.frac.value := by
      rw [normalizeLoop_fraction, scaleDenominator_normalizedValue]
      decide
    rw [normalizedValue]
    exact Sector.select_spec _
      (CCLEncoder.normalizeLoop fraction oldMeasure outside
        numeratorMeasure).annulus.band.1

/-- Every completed radial bracket normalizes into the common closed annulus.
This is the sector-independent part of the completed-block estimate. -/
theorem normalizedValue_band_of_radialBracket
    (kind : RawParser.BlockKind) (exponent : ℕ) (value : QI)
    (radial : RawParser.radialBracket kind exponent value) :
    Sector.Band (RawParser.normalizedValue kind exponent value) := by
  have powerPositive : (0 : ℚ) < (2 : ℚ) ^ exponent := pow_pos (by norm_num) _
  cases kind with
  | initialHigh =>
      rcases radial with ⟨lower, upper⟩
      have powerNe : natPow gamma exponent ≠ 0 :=
        RawParser.natPow_gamma_ne exponent
      have normIdentity :
          normSq (RawParser.normalizedValue .initialHigh exponent value) =
            normSq value / (2 : ℚ) ^ exponent := by
        rw [RawParser.normalizedValue, normSq_mul, normSq_inv _ powerNe,
          normSq_natPow, normSq_gamma]
        ring
      rw [Sector.Band, normIdentity]
      constructor
      · exact (le_div_iff₀ powerPositive).2 (by simpa using lower)
      · apply (div_le_iff₀ powerPositive).2
        have upper' : normSq value < 2 * (2 : ℚ) ^ exponent := by
          calc
            normSq value < (2 : ℚ) ^ (exponent + 1) := upper
            _ = 2 * (2 : ℚ) ^ exponent := by rw [pow_succ]; ring
        exact upper'.le
  | initialLow =>
      rcases radial with ⟨lower, upper⟩
      rw [Sector.Band, RawParser.normalizedValue, normSq_mul,
        normSq_natPow, normSq_gamma]
      exact ⟨lower, upper.le⟩
  | loop =>
      rcases radial with ⟨lower, upper⟩
      have powerNe : natPow gamma exponent ≠ 0 :=
        RawParser.natPow_gamma_ne exponent
      have normIdentity :
          normSq (RawParser.normalizedValue .loop exponent value) =
            normSq value / (2 : ℚ) ^ exponent := by
        rw [RawParser.normalizedValue, normSq_mul, normSq_inv _ powerNe,
          normSq_natPow, normSq_gamma]
        ring
      rw [Sector.Band, normIdentity]
      constructor
      · exact (le_div_iff₀ powerPositive).2 (by simpa using lower.le)
      · apply (div_le_iff₀ powerPositive).2
        calc
          normSq value ≤ (2 : ℚ) ^ (exponent + 1) := upper
          _ = 2 * (2 : ℚ) ^ exponent := by rw [pow_succ]; ring

/-- Every completed block therefore lies in the common closed annulus needed
by the sector contraction theorem. -/
theorem normalizedValue_band_of_fullBlock
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (value : QI)
    (full : RawParser.fullBlockHolds kind exponent sector value) :
    Sector.Band (RawParser.normalizedValue kind exponent value) :=
  normalizedValue_band_of_radialBracket kind exponent value full.1

/-- The unique affine value whose normalized sector coordinate is the
displayed representative.  This is the pre-inversion terminal tail. -/
def terminalBefore
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector) : QI :=
  match kind with
  | .initialLow => inv (natPow gamma exponent) * sector.rep
  | .initialHigh | .loop => natPow gamma exponent * sector.rep

@[simp] theorem normalizedValue_terminalBefore
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector) :
    RawParser.normalizedValue kind exponent
      (terminalBefore kind exponent sector) = sector.rep := by
  have powerNe : natPow gamma exponent ≠ 0 :=
    RawParser.natPow_gamma_ne exponent
  cases kind with
  | initialHigh =>
      rw [RawParser.normalizedValue, terminalBefore]
      calc
        (natPow gamma exponent * sector.rep) * inv (natPow gamma exponent) =
            sector.rep * (natPow gamma exponent *
              inv (natPow gamma exponent)) := by ring
        _ = sector.rep := by rw [mul_inv _ powerNe, mul_one]
  | initialLow =>
      rw [RawParser.normalizedValue, terminalBefore]
      calc
        natPow gamma exponent *
            (inv (natPow gamma exponent) * sector.rep) =
            (natPow gamma exponent * inv (natPow gamma exponent)) *
              sector.rep := by ring
        _ = sector.rep := by rw [mul_inv _ powerNe, one_mul]
  | loop =>
      rw [RawParser.normalizedValue, terminalBefore]
      calc
        (natPow gamma exponent * sector.rep) * inv (natPow gamma exponent) =
            sector.rep * (natPow gamma exponent *
              inv (natPow gamma exponent)) := by ring
        _ = sector.rep := by rw [mul_inv _ powerNe, mul_one]

/-- Conversely, zero normalized residual determines the terminal tail
uniquely. -/
theorem eq_terminalBefore_of_normalizedValue_eq
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (before : QI)
    (terminal : RawParser.normalizedValue kind exponent before = sector.rep) :
    before = terminalBefore kind exponent sector := by
  have powerNe : natPow gamma exponent ≠ 0 :=
    RawParser.natPow_gamma_ne exponent
  cases kind with
  | initialHigh =>
      change before * inv (natPow gamma exponent) = sector.rep at terminal
      rw [terminalBefore]
      calc
        before = before * (inv (natPow gamma exponent) *
            natPow gamma exponent) := by rw [inv_mul _ powerNe, mul_one]
        _ = (before * inv (natPow gamma exponent)) *
            natPow gamma exponent := by ring
        _ = sector.rep * natPow gamma exponent := by rw [terminal]
        _ = natPow gamma exponent * sector.rep := GaussianRat.mul_comm _ _
  | initialLow =>
      change natPow gamma exponent * before = sector.rep at terminal
      rw [terminalBefore]
      calc
        before = (inv (natPow gamma exponent) *
            natPow gamma exponent) * before := by rw [inv_mul _ powerNe, one_mul]
        _ = inv (natPow gamma exponent) *
            (natPow gamma exponent * before) := by ring
        _ = inv (natPow gamma exponent) * sector.rep := by rw [terminal]
  | loop =>
      change before * inv (natPow gamma exponent) = sector.rep at terminal
      rw [terminalBefore]
      calc
        before = before * (inv (natPow gamma exponent) *
            natPow gamma exponent) := by rw [inv_mul _ powerNe, mul_one]
        _ = (before * inv (natPow gamma exponent)) *
            natPow gamma exponent := by ring
        _ = sector.rep * natPow gamma exponent := by rw [terminal]
        _ = natPow gamma exponent * sector.rep := GaussianRat.mul_comm _ _

/-- A nonterminal selected sector subtraction produces a reciprocal tail in
the loop parser's strict outside region. -/
theorem inverse_selected_loop_active
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (value : QI)
    (full : RawParser.fullBlockHolds kind exponent sector value)
    (residual :
      RawParser.normalizedValue kind exponent value - sector.rep ≠ 0) :
    RawParser.activeHolds (.loopUnary 0)
      (inv (gamma *
        (RawParser.normalizedValue kind exponent value - sector.rep))) := by
  let radial := RawParser.normalizedValue kind exponent value - sector.rep
  have radialSmall : normSq radial < 1 / 2 := by
    exact Sector.contraction
      (normalizedValue_band_of_fullBlock kind exponent sector value full)
      sector full.2
  have gammaNe : gamma ≠ 0 := by
    intro zero
    have norm := congrArg normSq zero
    norm_num at norm
  have denominatorNe : gamma * radial ≠ 0 :=
    mul_ne_zero gammaNe (by simpa [radial] using residual)
  have denominatorPositive : 0 < normSq (gamma * radial) :=
    normSq_pos denominatorNe
  have denominatorSmall : normSq (gamma * radial) < 1 := by
    rw [normSq_mul, normSq_gamma]
    linarith
  rw [RawParser.activeHolds, pow_zero, normSq_inv _ denominatorNe]
  exact (lt_div_iff₀ denominatorPositive).2 (by
    simpa using denominatorSmall)

/-- The rational value after integral subtraction/inversion is exactly the
affine reciprocal used by the paper. -/
theorem postInversion_value
    (old : CCLEncoder.Annulus) (post : CCLEncoder.PostInversion old) :
    post.frac.value =
      inv (gamma *
        (old.frac.value - Sector.rep (Sector.select old.frac.value))) := by
  let sector := Sector.select old.frac.value
  let numerator := toRat old.frac.num
  let denominator := toRat old.frac.den
  let residual := numerator - sector.rep * denominator
  have denominatorNe : denominator ≠ 0 := old.frac.den_toRat_ne
  have residualNe : residual ≠ 0 := by
    intro zero
    have integralZero :
        old.frac.num - sectorInt sector * old.frac.den = 0 := by
      apply toRat_injective
      simpa [residual, numerator, denominator] using zero
    apply post.frac.den_ne
    rw [post.den_eq]
    simp [sector, integralZero]
  have oldResidual : old.frac.value - sector.rep =
      residual * inv denominator := by
    change numerator * inv denominator - sector.rep =
      residual * inv denominator
    rw [GaussianRat.sub_eq_add_neg]
    dsimp only [residual]
    rw [GaussianRat.sub_eq_add_neg]
    field_simp [denominatorNe]
    have cancel : inv denominator * sector.rep * denominator = sector.rep := by
      calc
        inv denominator * sector.rep * denominator =
            sector.rep * (inv denominator * denominator) := by ring
        _ = sector.rep := by rw [inv_mul _ denominatorNe, mul_one]
    have cancel' : inv denominator * (sector.rep * denominator) = sector.rep := by
      calc
        inv denominator * (sector.rep * denominator) =
            inv denominator * sector.rep * denominator := by ring
        _ = sector.rep := cancel
    rw [show inv denominator *
        (numerator + -(sector.rep * denominator)) =
      inv denominator * numerator +
        -(inv denominator * (sector.rep * denominator)) by ring]
    rw [cancel']
    ring
  have postValue : post.frac.value =
      denominator * inv (gamma * residual) := by
    rw [Frac.value, post.num_eq, post.den_eq]
    simp only [toRat_mul, toRat_gammaInt, toRat_sub, toRat_sectorInt]
    rfl
  rw [postValue, show Sector.select old.frac.value = sector by rfl,
    oldResidual]
  change denominator * (gamma * residual)⁻¹ =
    (gamma * (residual * denominator⁻¹))⁻¹
  rw [show gamma * (residual * denominator⁻¹) =
      (gamma * residual) * denominator⁻¹ by ring]
  have inverseProduct :
      ((gamma * residual) * denominator⁻¹)⁻¹ =
        denominator * (gamma * residual)⁻¹ := by
    rw [mul_inv_rev, inv_inv]
  rw [inverseProduct]

theorem postInversion_outside
    (old : CCLEncoder.Annulus) (post : CCLEncoder.PostInversion old) :
    normNat post.frac.den < normNat post.frac.num := by
  rw [post.num_eq]
  exact post.den_descent

theorem postInversion_value_ne_zero
    (old : CCLEncoder.Annulus) (post : CCLEncoder.PostInversion old) :
    post.frac.value ≠ 0 := by
  apply post.frac.value_ne_zero
  rw [post.num_eq]
  exact old.frac.den_ne

private theorem gamma_ne : gamma ≠ 0 := by
  intro zero
  have norm := congrArg normSq zero
  norm_num at norm

private theorem inv_inv_value (value : QI) : inv (inv value) = value := by
  change value⁻¹⁻¹ = value
  exact inv_inv value

private theorem inv_mul_rev_value (left right : QI) :
    inv (left * right) = inv right * inv left := by
  change (left * right)⁻¹ = right⁻¹ * left⁻¹
  exact mul_inv_rev left right

private theorem inverse_gamma_inverse_mul
    (radial : QI) (radialNe : radial ≠ 0) :
    inv (gamma * inv (gamma * radial)) = radial := by
  have gammaNe : gamma ≠ 0 := gamma_ne
  have gammaRadialNe : gamma * radial ≠ 0 := mul_ne_zero gammaNe radialNe
  have gammaTimesInverse :
      gamma * inv (gamma * radial) = inv radial := by
    rw [inv_mul_rev_value]
    calc
      gamma * (inv radial * inv gamma) =
          inv radial * (gamma * inv gamma) := by ring
      _ = inv radial := by rw [mul_inv _ gammaNe, mul_one]
  rw [gammaTimesInverse, inv_inv_value]

private theorem regularBlock_homographic_inverse
    (exponent : ℕ) (sector : Sector) (value radial : QI)
    (radialNe : radial ≠ 0)
    (decomposition :
      value = natPow gamma exponent * (sector.rep + radial)) :
    RatBox.homographic (CCLDecoder.regularBlock exponent sector)
        (inv (gamma * radial)) = value := by
  let power := natPow gamma exponent
  let tail := inv (gamma * radial)
  have inverseDenominator : inv (gamma * tail) = radial := by
    simpa only [tail] using inverse_gamma_inverse_mul radial radialNe
  have cancellation : gamma * tail * radial = 1 := by
    have gammaTail : gamma * tail = inv radial := by
      calc
        gamma * tail = inv (inv (gamma * tail)) :=
          (inv_inv_value (gamma * tail)).symm
        _ = inv radial := by rw [inverseDenominator]
    calc
      gamma * tail * radial = inv radial * radial := by rw [gammaTail]
      _ = 1 := inv_mul _ radialNe
  rw [RatBox.homographic]
  simp only [CCLDecoder.regularBlock]
  simp only [add_zero]
  change (natPow gamma (exponent + 1) * sector.rep * tail + power) *
      inv (gamma * tail) = value
  rw [inverseDenominator, decomposition]
  rw [natPow_succ]
  calc
    (power * gamma * sector.rep * tail + power) * radial =
        power * (sector.rep * (gamma * tail * radial) + radial) := by ring
    _ = power * (sector.rep + radial) := by rw [cancellation, mul_one]

private theorem lowBlock_homographic_inverse
    (exponent : ℕ) (sector : Sector) (value radial : QI)
    (radialNe : radial ≠ 0)
    (decomposition :
      natPow gamma exponent * value = sector.rep + radial) :
    RatBox.homographic (CCLDecoder.lowBlock exponent sector)
        (inv (gamma * radial)) = value := by
  let power := natPow gamma exponent
  let tail := inv (gamma * radial)
  have powerNe : power ≠ 0 := RawParser.natPow_gamma_ne exponent
  have inverseGammaTail : inv (gamma * tail) = radial := by
    simpa only [tail] using inverse_gamma_inverse_mul radial radialNe
  have denominatorInverse :
      inv (natPow gamma (exponent + 1) * tail) =
        radial * inv power := by
    rw [natPow_succ]
    change inv ((power * gamma) * tail) = radial * inv power
    rw [show (power * gamma) * tail = power * (gamma * tail) by ring]
    rw [inv_mul_rev_value, inverseGammaTail]
  have cancellation : gamma * tail * radial = 1 := by
    have gammaTail : gamma * tail = inv radial := by
      calc
        gamma * tail = inv (inv (gamma * tail)) :=
          (inv_inv_value (gamma * tail)).symm
        _ = inv radial := by rw [inverseGammaTail]
    calc
      gamma * tail * radial = inv radial * radial := by rw [gammaTail]
      _ = 1 := inv_mul _ radialNe
  rw [RatBox.homographic]
  simp only [CCLDecoder.lowBlock]
  simp only [add_zero]
  change (gamma * sector.rep * tail + 1) *
      inv (natPow gamma (exponent + 1) * tail) = value
  rw [denominatorInverse]
  calc
    (gamma * sector.rep * tail + 1) * (radial * inv power) =
        (sector.rep * (gamma * tail * radial) + radial) * inv power := by
      ring
    _ = (sector.rep + radial) * inv power := by
      rw [cancellation, mul_one]
    _ = (power * value) * inv power := by rw [decomposition]
    _ = value * (power * inv power) := by ring
    _ = value := by rw [mul_inv _ powerNe, mul_one]

/-- One completed parser block maps the reciprocal post-inversion tail back
to its pre-normalization value. -/
theorem block_homographic_inverse
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (value : QI)
    (residual :
      RawParser.normalizedValue kind exponent value - sector.rep ≠ 0) :
    RatBox.homographic (RawParser.blockMatrix kind exponent sector)
        (inv (gamma *
          (RawParser.normalizedValue kind exponent value - sector.rep))) =
      value := by
  cases kind with
  | initialHigh =>
      let radial := value * inv (natPow gamma exponent) - sector.rep
      have radialNe : radial ≠ 0 := residual
      apply regularBlock_homographic_inverse exponent sector value radial radialNe
      have powerNe := RawParser.natPow_gamma_ne exponent
      dsimp only [radial]
      rw [GaussianRat.sub_eq_add_neg]
      calc
        value = value * (inv (natPow gamma exponent) *
            natPow gamma exponent) := by
          rw [inv_mul _ powerNe, mul_one]
        _ = natPow gamma exponent *
            (sector.rep +
              (value * inv (natPow gamma exponent) + -sector.rep)) := by ring
  | initialLow =>
      let radial := natPow gamma exponent * value - sector.rep
      have radialNe : radial ≠ 0 := residual
      apply lowBlock_homographic_inverse exponent sector value radial radialNe
      dsimp only [radial]
      rw [GaussianRat.sub_eq_add_neg]
      ring
  | loop =>
      let radial := value * inv (natPow gamma exponent) - sector.rep
      have radialNe : radial ≠ 0 := residual
      apply regularBlock_homographic_inverse exponent sector value radial radialNe
      have powerNe := RawParser.natPow_gamma_ne exponent
      dsimp only [radial]
      rw [GaussianRat.sub_eq_add_neg]
      calc
        value = value * (inv (natPow gamma exponent) *
            natPow gamma exponent) := by
          rw [inv_mul _ powerNe, mul_one]
        _ = natPow gamma exponent *
            (sector.rep +
              (value * inv (natPow gamma exponent) + -sector.rep)) := by ring

theorem block_inverse_denominator_ne
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (value : QI)
    (residual :
      RawParser.normalizedValue kind exponent value - sector.rep ≠ 0) :
    RawParserSemantics.denominator
      (RawParser.blockMatrix kind exponent sector)
      (inv (gamma *
        (RawParser.normalizedValue kind exponent value - sector.rep))) ≠ 0 := by
  have tailNe :
      inv (gamma *
        (RawParser.normalizedValue kind exponent value - sector.rep)) ≠ 0 :=
    inv_ne_zero (mul_ne_zero gamma_ne residual)
  cases kind with
  | initialHigh =>
      simpa [RawParserSemantics.denominator, RawParser.blockMatrix,
        CCLDecoder.regularBlock] using mul_ne_zero gamma_ne tailNe
  | initialLow =>
      simpa [RawParserSemantics.denominator, RawParser.blockMatrix,
        CCLDecoder.lowBlock] using
          mul_ne_zero (RawParser.natPow_gamma_ne (exponent + 1)) tailNe
  | loop =>
      simpa [RawParserSemantics.denominator, RawParser.blockMatrix,
        CCLDecoder.regularBlock] using mul_ne_zero gamma_ne tailNe

theorem tail_ne_of_block_denominator
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (tail : QI)
    (denominator : RawParserSemantics.denominator
      (RawParser.blockMatrix kind exponent sector) tail ≠ 0) :
    tail ≠ 0 := by
  intro zero
  subst tail
  apply denominator
  cases kind <;>
    simp [RawParserSemantics.denominator, RawParser.blockMatrix,
      CCLDecoder.regularBlock, CCLDecoder.lowBlock]

/-- A completed block followed by an affine tail normalizes to its selected
sector representative plus the reciprocal correction. -/
theorem normalizedValue_block_homographic
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (tail : QI)
    (denominator : RawParserSemantics.denominator
      (RawParser.blockMatrix kind exponent sector) tail ≠ 0) :
    RawParser.normalizedValue kind exponent
        (RatBox.homographic (RawParser.blockMatrix kind exponent sector) tail) =
      sector.rep + inv (gamma * tail) := by
  have tailNe := tail_ne_of_block_denominator kind exponent sector tail
    denominator
  have gammaTailNe : gamma * tail ≠ 0 := mul_ne_zero gamma_ne tailNe
  let power := natPow gamma exponent
  have powerNe : power ≠ 0 := RawParser.natPow_gamma_ne exponent
  have powerCancel : power * inv power = 1 := mul_inv _ powerNe
  have denominatorCancel : gamma * tail * inv (gamma * tail) = 1 :=
    mul_inv _ gammaTailNe
  cases kind with
  | initialHigh =>
      simp only [RawParser.normalizedValue, RawParser.blockMatrix,
        CCLDecoder.regularBlock, RatBox.homographic, GaussianRat.add_zero,
        natPow_succ]
      change ((power * gamma * sector.rep * tail + power) *
        inv (gamma * tail)) * inv power = sector.rep + inv (gamma * tail)
      calc
        ((power * gamma * sector.rep * tail + power) *
            inv (gamma * tail)) * inv power =
          sector.rep * (gamma * tail * inv (gamma * tail)) *
              (power * inv power) +
            inv (gamma * tail) * (power * inv power) := by ring
        _ = sector.rep + inv (gamma * tail) := by
          simp only [denominatorCancel, powerCancel, GaussianRat.mul_one]
  | initialLow =>
      have inverseDenominator :
          inv (natPow gamma (exponent + 1) * tail) =
            inv (gamma * tail) * inv power := by
        rw [natPow_succ]
        change inv ((power * gamma) * tail) =
          inv (gamma * tail) * inv power
        rw [show (power * gamma) * tail = power * (gamma * tail) by ring]
        exact inv_mul_rev_value power (gamma * tail)
      simp only [RawParser.normalizedValue, RawParser.blockMatrix,
        CCLDecoder.lowBlock, RatBox.homographic, GaussianRat.add_zero]
      change power * ((gamma * sector.rep * tail + 1) *
        inv (natPow gamma (exponent + 1) * tail)) =
          sector.rep + inv (gamma * tail)
      rw [inverseDenominator]
      calc
        power * ((gamma * sector.rep * tail + 1) *
            (inv (gamma * tail) * inv power)) =
          sector.rep * (gamma * tail * inv (gamma * tail)) *
              (power * inv power) +
            inv (gamma * tail) * (power * inv power) := by ring
        _ = sector.rep + inv (gamma * tail) := by
          simp only [denominatorCancel, powerCancel, GaussianRat.mul_one]
  | loop =>
      simp only [RawParser.normalizedValue, RawParser.blockMatrix,
        CCLDecoder.regularBlock, RatBox.homographic, GaussianRat.add_zero,
        natPow_succ]
      change ((power * gamma * sector.rep * tail + power) *
        inv (gamma * tail)) * inv power = sector.rep + inv (gamma * tail)
      calc
        ((power * gamma * sector.rep * tail + power) *
            inv (gamma * tail)) * inv power =
          sector.rep * (gamma * tail * inv (gamma * tail)) *
              (power * inv power) +
            inv (gamma * tail) * (power * inv power) := by ring
        _ = sector.rep + inv (gamma * tail) := by
          simp only [denominatorCancel, powerCancel, GaussianRat.mul_one]

/-- Once a selected sector subtraction has zero residual, the completed block
has projective tail `ω`; no affine tail can represent either next raw bit. -/
theorem terminal_sector_no_canStep
    (state : RawParser.State) (kind : RawParser.BlockKind) (exponent : ℕ)
    (first second third : Bool) (input before : QI)
    (determinant : state.matrix.det ≠ 0)
    (phase : state.phase =
      .sector kind exponent (.two first second))
    (beforeRepresents : RawParserSemantics.Represents state input before)
    (full : RawParser.fullBlockHolds kind exponent
      (RawParser.sectorOfBits first second third) before)
    (terminal : RawParser.normalizedValue kind exponent before =
      (RawParser.sectorOfBits first second third).rep)
    (bit : Bool) :
    ¬ RawParserSemantics.CanStep state input bit := by
  rintro ⟨tail, afterRepresents⟩
  let candidate := RawParser.sectorOfBits first second bit
  let block := RawParser.blockMatrix kind exponent candidate
  have afterCompleted : RawParserSemantics.Represents
      (RawParser.completeSector state kind exponent first second bit)
        input tail := by
    rw [← RawParserSemantics.step_eq_completeSector state kind exponent
      first second bit phase]
    exact afterRepresents
  have newest :
      (RawParser.Constraint.mk block kind exponent candidate).Holds tail := by
    apply afterCompleted.2.2.1
    simp [RawParser.completeSector, candidate, block]
  have previousRepresents :=
    RawParserSemantics.completeSector_represents_previous state kind exponent
      first second bit input tail phase afterCompleted
  have previousEqual : before = RatBox.homographic block tail := by
    simpa [candidate, block] using
      RawParserSemantics.Represents.tail_unique determinant beforeRepresents
        previousRepresents
  have selectedHolds :
      (RawParser.sectorOfBits first second third).Holds
        (RawParser.normalizedValue kind exponent
          (RatBox.homographic block tail)) := by
    rw [← previousEqual]
    exact full.2
  have candidateHolds : candidate.Holds
      (RawParser.normalizedValue kind exponent
        (RatBox.homographic block tail)) := by
    exact newest.2.2
  have candidateEqual : candidate =
      RawParser.sectorOfBits first second third :=
    Sector.holds_unique candidateHolds selectedHolds
  have bitEqual : bit = third := by
    cases first <;> cases second <;> cases bit <;> cases third <;>
      simp_all [candidate, RawParser.sectorOfBits]
  subst bit
  have blockEqual : block = RawParser.blockMatrix kind exponent
      (RawParser.sectorOfBits first second third) := by
    rfl
  have normalizedTail := normalizedValue_block_homographic kind exponent
    (RawParser.sectorOfBits first second third) tail (by
      simpa [RawParserSemantics.denominator, block, candidate] using newest.1)
  have terminalEquation :
      (RawParser.sectorOfBits first second third).rep =
        (RawParser.sectorOfBits first second third).rep + inv (gamma * tail) := by
    calc
      (RawParser.sectorOfBits first second third).rep =
          RawParser.normalizedValue kind exponent before := terminal.symm
      _ = RawParser.normalizedValue kind exponent
          (RatBox.homographic block tail) := congrArg
            (RawParser.normalizedValue kind exponent) previousEqual
      _ = (RawParser.sectorOfBits first second third).rep +
          inv (gamma * tail) := by simpa [blockEqual] using normalizedTail
  have inverseZero : inv (gamma * tail) = 0 := by
    apply add_left_cancel
      (a := (RawParser.sectorOfBits first second third).rep)
    simpa using terminalEquation.symm
  have tailNe := tail_ne_of_block_denominator kind exponent
    (RawParser.sectorOfBits first second third) tail (by
      simpa [RawParserSemantics.denominator, block, candidate] using newest.1)
  exact (inv_ne_zero (mul_ne_zero gamma_ne tailNe)) inverseZero

/-- Finite predicate for a proposed next bit at the unique affine tail of a
represented parser state.  Ordinary phases test the next state's predicate at
the same tail.  A third sector bit additionally requires a nonzero subtraction
before changing to reciprocal coordinates. -/
def CanAdvanceAt (state : RawParser.State) (bit : Bool) (before : QI) : Prop :=
  match state.phase with
  | .sector kind exponent (.two first second) =>
      let sector := RawParser.sectorOfBits first second bit
      RawParser.fullBlockHolds kind exponent sector before ∧
        RawParser.normalizedValue kind exponent before - sector.rep ≠ 0
  | _ => (RawParser.step state bit).Holds before

instance canAdvanceAtDecidable
    (state : RawParser.State) (bit : Bool) (before : QI) :
    Decidable (CanAdvanceAt state bit before) := by
  unfold CanAdvanceAt
  split
  · infer_instance
  · exact decidable_of_iff
      ((RawParser.step state bit).holdsBool before = true)
      (RawParser.State.holdsBool_eq_true (RawParser.step state bit) before)

/-- The two finite next-bit predicates are disjoint at every affine tail.
This is stronger than semantic parser uniqueness: it does not require the
current state to represent an input, because both predicates are evaluated at
the same proposed tail. -/
theorem not_canAdvanceAt_false_and_true
    (state : RawParser.State) (before : QI) :
    ¬(CanAdvanceAt state false before ∧
      CanAdvanceAt state true before) := by
  rintro ⟨falseHolds, trueHolds⟩
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      have low := falseHolds.2
      have high := trueHolds.2
      change normSq before < 2 at low
      change (2 : ℚ) ^ 1 ≤ normSq before at high
      norm_num at high
      linarith
  | highUnary count =>
      have upper := falseHolds.2.1.2
      have lower := trueHolds.2
      change normSq before < (2 : ℚ) ^ (count + 1) at upper
      change (2 : ℚ) ^ (count + 1) ≤ normSq before at lower
      linarith
  | lowUnary count =>
      have lower := falseHolds.2.1.1
      have upper := trueHolds.2
      change 1 ≤ (2 : ℚ) ^ count * normSq before at lower
      change (2 : ℚ) ^ count * normSq before < 1 at upper
      linarith
  | loopUnary count =>
      have upper := falseHolds.2.1.2
      have lower := trueHolds.2
      change normSq before ≤ (2 : ℚ) ^ (count + 1) at upper
      change (2 : ℚ) ^ (count + 1) < normSq before at lower
      linarith
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          rcases falseHolds.2 with
            ⟨_, falseSector, falseMember, falseSectorHolds⟩
          rcases trueHolds.2 with
            ⟨_, trueSector, trueMember, trueSectorHolds⟩
          have sectorEqual := Sector.holds_unique falseSectorHolds
            trueSectorHolds
          subst trueSector
          have falsePrefix : [false] <+: falseSector.code :=
            of_decide_eq_true (List.mem_filter.mp falseMember).2
          have truePrefix : [true] <+: falseSector.code :=
            of_decide_eq_true (List.mem_filter.mp trueMember).2
          cases falseSector <;> simp_all
      | one first =>
          rcases falseHolds.2 with
            ⟨_, falseSector, falseMember, falseSectorHolds⟩
          rcases trueHolds.2 with
            ⟨_, trueSector, trueMember, trueSectorHolds⟩
          have sectorEqual := Sector.holds_unique falseSectorHolds
            trueSectorHolds
          subst trueSector
          have falsePrefix : [first, false] <+: falseSector.code :=
            of_decide_eq_true (List.mem_filter.mp falseMember).2
          have truePrefix : [first, true] <+: falseSector.code :=
            of_decide_eq_true (List.mem_filter.mp trueMember).2
          cases first <;> cases falseSector <;> simp_all
      | two first second =>
          have sectorEqual := Sector.holds_unique falseHolds.1.2
            trueHolds.1.2
          cases first <;> cases second <;>
            simp [RawParser.sectorOfBits] at sectorEqual

/-- Hence any two finite next-bit predicates holding at the same tail select
the same bit. -/
theorem canAdvanceAt_unique
    {state : RawParser.State} {before : QI} {left right : Bool}
    (leftHolds : CanAdvanceAt state left before)
    (rightHolds : CanAdvanceAt state right before) :
    left = right := by
  cases left <;> cases right
  · rfl
  · exact (not_canAdvanceAt_false_and_true state before
      ⟨leftHolds, rightHolds⟩).elim
  · exact (not_canAdvanceAt_false_and_true state before
      ⟨rightHolds, leftHolds⟩).elim
  · rfl

/-- Exact semantic reduction for the next-bit controller.  Once an invertible
state represents the input through its unique current tail, semantic
possibility of a bit is equivalent to the explicit rational predicate above.
This is the parser-level decision statement consumed by Theorem 10.2's
generalized-circle machinery. -/
theorem canStep_iff_canAdvanceAt
    (state : RawParser.State) (input before : QI)
    (determinant : state.matrix.det ≠ 0)
    (beforeRepresents : RawParserSemantics.Represents state input before)
    (bit : Bool) :
    RawParserSemantics.CanStep state input bit ↔
      CanAdvanceAt state bit before := by
  constructor
  · intro possible
    rcases possible with ⟨after, afterRepresents⟩
    have previousRepresents := RawParserSemantics.step_represents_previous
      state bit input after afterRepresents
    have previousEqual := RawParserSemantics.Represents.tail_unique
      determinant beforeRepresents previousRepresents
    rcases state with ⟨phase, matrix, history⟩
    cases phase with
    | initial =>
        simp only [RawParserSemantics.previousTail] at previousEqual
        subst before
        simpa [CanAdvanceAt] using afterRepresents.2.2
    | highUnary count =>
        simp only [RawParserSemantics.previousTail] at previousEqual
        subst before
        simpa [CanAdvanceAt] using afterRepresents.2.2
    | lowUnary count =>
        simp only [RawParserSemantics.previousTail] at previousEqual
        subst before
        simpa [CanAdvanceAt] using afterRepresents.2.2
    | loopUnary count =>
        simp only [RawParserSemantics.previousTail] at previousEqual
        subst before
        simpa [CanAdvanceAt] using afterRepresents.2.2
    | sector kind exponent bits =>
        cases bits with
        | zero =>
            simp only [RawParserSemantics.previousTail] at previousEqual
            subst before
            simpa [CanAdvanceAt] using afterRepresents.2.2
        | one first =>
            simp only [RawParserSemantics.previousTail] at previousEqual
            subst before
            simpa [CanAdvanceAt] using afterRepresents.2.2
        | two first second =>
            let sector := RawParser.sectorOfBits first second bit
            let block := RawParser.blockMatrix kind exponent sector
            have newest :
                (RawParser.Constraint.mk block kind exponent sector).Holds
                  after := by
              apply afterRepresents.2.2.1
              simp [RawParser.step, RawParser.completeSector, sector, block]
            have previousEqual' :
                before = RatBox.homographic block after := by
              simpa [RawParserSemantics.previousTail, sector, block] using
                previousEqual
            have full : RawParser.fullBlockHolds kind exponent sector before := by
              rw [previousEqual']
              exact newest.2
            have residual :
                RawParser.normalizedValue kind exponent before -
                    sector.rep ≠ 0 := by
              intro zero
              have terminal :
                  RawParser.normalizedValue kind exponent before = sector.rep :=
                by
                  apply GaussianRat.ext
                  · have realPart := congrArg GaussianRat.re zero
                    simp only [GaussianRat.sub_re, GaussianRat.zero_re] at realPart
                    linarith
                  · have imaginaryPart := congrArg GaussianRat.im zero
                    simp only [GaussianRat.sub_im, GaussianRat.zero_im] at imaginaryPart
                    linarith
              have impossible := terminal_sector_no_canStep
                ⟨.sector kind exponent (.two first second), matrix, history⟩
                kind exponent first second bit input before determinant rfl
                beforeRepresents (by simpa [sector] using full)
                (by simpa [sector] using terminal) bit
              exact impossible ⟨after, afterRepresents⟩
            exact ⟨full, residual⟩
  · intro advance
    rcases state with ⟨phase, matrix, history⟩
    cases phase with
    | initial =>
        refine ⟨before, ?_⟩
        apply RawParserSemantics.step_represents_next
          ⟨.initial, matrix, history⟩ bit input before
        · simpa [RawParserSemantics.previousTail] using beforeRepresents
        · simpa [CanAdvanceAt] using advance
    | highUnary count =>
        refine ⟨before, ?_⟩
        apply RawParserSemantics.step_represents_next
          ⟨.highUnary count, matrix, history⟩ bit input before
        · simpa [RawParserSemantics.previousTail] using beforeRepresents
        · simpa [CanAdvanceAt] using advance
    | lowUnary count =>
        refine ⟨before, ?_⟩
        apply RawParserSemantics.step_represents_next
          ⟨.lowUnary count, matrix, history⟩ bit input before
        · simpa [RawParserSemantics.previousTail] using beforeRepresents
        · simpa [CanAdvanceAt] using advance
    | loopUnary count =>
        refine ⟨before, ?_⟩
        apply RawParserSemantics.step_represents_next
          ⟨.loopUnary count, matrix, history⟩ bit input before
        · simpa [RawParserSemantics.previousTail] using beforeRepresents
        · simpa [CanAdvanceAt] using advance
    | sector kind exponent bits =>
        cases bits with
        | zero =>
            refine ⟨before, ?_⟩
            apply RawParserSemantics.step_represents_next
              ⟨.sector kind exponent .zero, matrix, history⟩ bit input before
            · simpa [RawParserSemantics.previousTail] using beforeRepresents
            · simpa [CanAdvanceAt] using advance
        | one first =>
            refine ⟨before, ?_⟩
            apply RawParserSemantics.step_represents_next
              ⟨.sector kind exponent (.one first), matrix, history⟩ bit input
                before
            · simpa [RawParserSemantics.previousTail] using beforeRepresents
            · simpa [CanAdvanceAt] using advance
        | two first second =>
            let sector := RawParser.sectorOfBits first second bit
            let tail := inv (gamma *
              (RawParser.normalizedValue kind exponent before - sector.rep))
            rcases advance with ⟨full, residual⟩
            refine ⟨tail, ?_⟩
            have completed :=
              RawParserSemantics.completeSector_represents_next
                ⟨.sector kind exponent (.two first second), matrix, history⟩
                kind exponent first second bit input before tail rfl
                beforeRepresents
                (by simpa [tail, sector] using
                  (block_homographic_inverse kind exponent sector before
                    residual))
                (by simpa [tail, sector] using
                  (block_inverse_denominator_ne kind exponent sector before
                    residual))
                (by simpa [sector] using full)
                (by simpa [tail, sector] using
                  (inverse_selected_loop_active kind exponent sector before
                    full residual))
            rw [RawParserSemantics.step_eq_completeSector
              ⟨.sector kind exponent (.two first second), matrix, history⟩
              kind exponent first second bit rfl]
            exact completed

/-- Total local outcome after evaluating the two finite next-bit predicates at
the unique represented affine tail. -/
inductive LocalDecision (state : RawParser.State) (input : QI) where
  | terminal (none : ∀ bit, ¬RawParserSemantics.CanStep state input bit)
  | next (bit : Bool) (possible : RawParserSemantics.CanStep state input bit)
      (unique : ∀ other, RawParserSemantics.CanStep state input other →
        other = bit)

/-- Evaluate both Boolean choices through `CanAdvanceAt`.  This is a genuinely
finite next-bit decision for a represented rational input; the enclosing FTA
controller supplies the corresponding finite side certificate for an unnamed
winding-one track. -/
def decideLocal
    (state : RawParser.State) (input before : QI)
    (determinant : state.matrix.det ≠ 0)
    (beforeRepresents : RawParserSemantics.Represents state input before) :
    LocalDecision state input := by
  by_cases falseAdvance : CanAdvanceAt state false before
  · have falsePossible : RawParserSemantics.CanStep state input false :=
      (canStep_iff_canAdvanceAt state input before determinant
        beforeRepresents false).2 falseAdvance
    exact .next false falsePossible (by
      intro other otherPossible
      exact RawParserSemantics.canStep_unique determinant otherPossible
        falsePossible)
  · by_cases trueAdvance : CanAdvanceAt state true before
    · have truePossible : RawParserSemantics.CanStep state input true :=
        (canStep_iff_canAdvanceAt state input before determinant
          beforeRepresents true).2 trueAdvance
      exact .next true truePossible (by
        intro other otherPossible
        exact RawParserSemantics.canStep_unique determinant otherPossible
          truePossible)
    · exact .terminal (by
        intro bit possible
        cases bit
        · exact falseAdvance
            ((canStep_iff_canAdvanceAt state input before determinant
              beforeRepresents false).1 possible)
        · exact trueAdvance
            ((canStep_iff_canAdvanceAt state input before determinant
              beforeRepresents true).1 possible))

/-- Immediately after a nonterminal inversion, the loop parser's exponent-zero
active predicate holds. -/
theorem postInversion_loop_active
    (old : CCLEncoder.Annulus) (post : CCLEncoder.PostInversion old) :
    RawParser.activeHolds (.loopUnary 0) post.frac.value := by
  rw [RawParser.activeHolds, pow_zero, Frac.normSq_value]
  have denominatorPositive : (0 : ℚ) < normNat post.frac.den := by
    exact_mod_cast normNat_pos post.frac.den_ne
  apply (lt_div_iff₀ denominatorPositive).2
  norm_num
  exact_mod_cast postInversion_outside old post

/-- Named bit projections for the fixed three-bit sector table. -/
def sectorFirstBit : Sector → Bool
  | .east | .northEast | .north | .northWest => false
  | .west | .southWest | .south | .southEast => true

def sectorSecondBit : Sector → Bool
  | .east | .northEast | .west | .southWest => false
  | .north | .northWest | .south | .southEast => true

def sectorThirdBit : Sector → Bool
  | .east | .north | .west | .south => false
  | .northEast | .northWest | .southWest | .southEast => true

@[simp] theorem sector_code_eq_bits (sector : Sector) :
    sector.code =
      [sectorFirstBit sector, sectorSecondBit sector, sectorThirdBit sector] := by
  cases sector <;> rfl

@[simp] theorem sectorOfBits_projection (sector : Sector) :
    RawParser.sectorOfBits (sectorFirstBit sector) (sectorSecondBit sector)
      (sectorThirdBit sector) = sector := by
  cases sector <;> rfl

/-- Exact data carried by the only affine-terminal parser situation: two
sector bits have been read and the unique compatible third-bit subtraction
has zero residual. -/
inductive TerminalSectorAt (state : RawParser.State) (before : QI) : Prop where
  | mk (kind : RawParser.BlockKind) (exponent : ℕ)
      (first second third : Bool)
      (phase : state.phase = .sector kind exponent (.two first second))
      (full : RawParser.fullBlockHolds kind exponent
        (RawParser.sectorOfBits first second third) before)
      (residualZero : RawParser.normalizedValue kind exponent before =
        (RawParser.sectorOfBits first second third).rep)

private theorem sector_mem_zero_candidates (sector : Sector) :
    sector ∈ RawParser.sectorCandidates .zero := by
  cases sector <;> native_decide

private theorem sector_mem_one_projection (sector : Sector) :
    sector ∈ RawParser.sectorCandidates (.one (sectorFirstBit sector)) := by
  cases sector <;> native_decide

private theorem sector_mem_two_projection (sector : Sector) :
    sector ∈ RawParser.sectorCandidates
      (.two (sectorFirstBit sector) (sectorSecondBit sector)) := by
  cases sector <;> native_decide

private theorem first_projection_of_mem_one
    (first : Bool) (sector : Sector)
    (member : sector ∈ RawParser.sectorCandidates (.one first)) :
    sectorFirstBit sector = first := by
  cases first <;> cases sector <;> simp_all [sectorFirstBit]

private theorem projections_of_mem_two
    (first second : Bool) (sector : Sector)
    (member : sector ∈ RawParser.sectorCandidates (.two first second)) :
    sectorFirstBit sector = first ∧ sectorSecondBit sector = second := by
  cases first <;> cases second <;> cases sector <;>
    simp_all [sectorFirstBit, sectorSecondBit]

/-- A completed radial bracket always supplies the active zero-bit sector
fragment by selecting the unique table row of its normalized value. -/
private theorem sector_zero_active_of_radial
    (kind : RawParser.BlockKind) (exponent : ℕ) (before : QI)
    (radial : RawParser.radialBracket kind exponent before) :
    RawParser.activeHolds (.sector kind exponent .zero) before := by
  let sector := Sector.select (RawParser.normalizedValue kind exponent before)
  have band := normalizedValue_band_of_radialBracket kind exponent before radial
  exact ⟨radial, sector, sector_mem_zero_candidates sector,
    Sector.select_spec _ band.1⟩

/-- Constructive converse to `terminal_sector_no_canStep` at the finite
predicate level.  If a currently valid parser state admits neither Boolean
child, then it is necessarily a completed sector prefix and its uniquely
compatible subtraction residual is exactly zero. -/
theorem terminalSectorAt_of_no_canAdvanceAt
    (state : RawParser.State) (before : QI)
    (current : state.Holds before)
    (none : ∀ bit, ¬CanAdvanceAt state bit before) :
    TerminalSectorAt state before := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      by_cases high : 2 ≤ normSq before
      · exact (none true (by
          simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds,
            RawParser.activeHolds] using And.intro current.1 high)).elim
      · have low : normSq before < 2 := lt_of_not_ge high
        exact (none false (by
          simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds,
            RawParser.activeHolds] using And.intro current.1 low)).elim
  | highUnary count =>
      by_cases high : (2 : ℚ) ^ (count + 1) ≤ normSq before
      · exact (none true (by
          simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds,
            RawParser.activeHolds] using And.intro current.1 high)).elim
      · have radial : RawParser.radialBracket .initialHigh count before :=
          ⟨current.2, lt_of_not_ge high⟩
        have active := sector_zero_active_of_radial .initialHigh count before radial
        exact (none false (by
          simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds] using
            And.intro current.1 active)).elim
  | lowUnary count =>
      cases count with
      | zero =>
          by_cases low : normSq before < 1
          · exact (none true (by
              simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds,
                RawParser.activeHolds] using And.intro current.1 low)).elim
          · have radial : RawParser.radialBracket .initialLow 0 before := by
              rw [RawParser.radialBracket, pow_zero]
              exact ⟨by simpa using not_lt.mp low,
                by simpa [RawParser.activeHolds] using current.2⟩
            have active := sector_zero_active_of_radial .initialLow 0 before radial
            exact (none false (by
              simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds] using
                And.intro current.1 active)).elim
      | succ count =>
          by_cases low :
              (2 : ℚ) ^ (count + 1) * normSq before < 1
          · exact (none true (by
              simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds,
                RawParser.activeHolds] using And.intro current.1 low)).elim
          · have currentUpper :
                (2 : ℚ) ^ count * normSq before < 1 := by
              simpa [RawParser.activeHolds] using current.2
            have upper :
                (2 : ℚ) ^ (count + 1) * normSq before < 2 := by
              calc
                (2 : ℚ) ^ (count + 1) * normSq before =
                    2 * ((2 : ℚ) ^ count * normSq before) := by
                  rw [pow_succ]
                  ring
                _ < 2 * 1 :=
                  mul_lt_mul_of_pos_left currentUpper (by norm_num)
                _ = 2 := by norm_num
            have radial :
                RawParser.radialBracket .initialLow (count + 1) before :=
              ⟨not_lt.mp low, upper⟩
            have active := sector_zero_active_of_radial .initialLow
              (count + 1) before radial
            exact (none false (by
              simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds] using
                And.intro current.1 active)).elim
  | loopUnary count =>
      by_cases bounded : normSq before ≤ (2 : ℚ) ^ (count + 1)
      · have radial : RawParser.radialBracket .loop count before :=
          ⟨current.2, bounded⟩
        have active := sector_zero_active_of_radial .loop count before radial
        exact (none false (by
          simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds] using
            And.intro current.1 active)).elim
      · have high : (2 : ℚ) ^ (count + 1) < normSq before :=
          lt_of_not_ge bounded
        exact (none true (by
          simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds,
            RawParser.activeHolds] using And.intro current.1 high)).elim
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          rcases current.2 with ⟨radial, sector, _member, sectorHolds⟩
          let bit := sectorFirstBit sector
          have active : RawParser.activeHolds
              (.sector kind exponent (.one bit)) before :=
            ⟨radial, sector, sector_mem_one_projection sector, sectorHolds⟩
          exact (none bit (by
            simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds, bit]
              using And.intro current.1 active)).elim
      | one first =>
          rcases current.2 with ⟨radial, sector, member, sectorHolds⟩
          have firstProjection := first_projection_of_mem_one first sector member
          let bit := sectorSecondBit sector
          have memberTwo : sector ∈
              RawParser.sectorCandidates (.two first bit) := by
            rw [← firstProjection]
            exact sector_mem_two_projection sector
          have active : RawParser.activeHolds
              (.sector kind exponent (.two first bit)) before :=
            ⟨radial, sector, memberTwo, sectorHolds⟩
          exact (none bit (by
            simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds, bit]
              using And.intro current.1 active)).elim
      | two first second =>
          rcases current.2 with ⟨radial, sector, member, sectorHolds⟩
          have projections := projections_of_mem_two first second sector member
          let third := sectorThirdBit sector
          have sectorEquality :
              RawParser.sectorOfBits first second third = sector := by
            rw [← projections.1, ← projections.2]
            exact sectorOfBits_projection sector
          have full : RawParser.fullBlockHolds kind exponent
              (RawParser.sectorOfBits first second third) before := by
            refine ⟨radial, ?_⟩
            rw [sectorEquality]
            exact sectorHolds
          by_cases residualZero :
              RawParser.normalizedValue kind exponent before =
                (RawParser.sectorOfBits first second third).rep
          · exact .mk kind exponent first second third rfl full residualZero
          · have residualNonzero :
                RawParser.normalizedValue kind exponent before -
                    (RawParser.sectorOfBits first second third).rep ≠ 0 :=
              by
                intro zero
                apply residualZero
                apply GaussianRat.ext
                · have realPart := congrArg GaussianRat.re zero
                  simp only [GaussianRat.sub_re, GaussianRat.zero_re] at realPart
                  linarith
                · have imaginaryPart := congrArg GaussianRat.im zero
                  simp only [GaussianRat.sub_im, GaussianRat.zero_im]
                    at imaginaryPart
                  linarith
            exact (none third ⟨full, residualNonzero⟩).elim

private theorem foldl_highUnary_true
    (count amount : ℕ) (matrix : Mat2 QI)
    (history : List RawParser.Constraint) :
    (List.replicate amount true).foldl RawParser.step
        ⟨RawParser.Phase.highUnary count, matrix, history⟩ =
      ⟨RawParser.Phase.highUnary (count + amount), matrix, history⟩ := by
  induction amount generalizing count with
  | zero => simp
  | succ amount inductionHypothesis =>
      rw [List.replicate_succ, List.foldl_cons]
      simp only [RawParser.step, if_pos]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (count + 1)

private theorem foldl_lowUnary_true
    (count amount : ℕ) (matrix : Mat2 QI)
    (history : List RawParser.Constraint) :
    (List.replicate amount true).foldl RawParser.step
        ⟨RawParser.Phase.lowUnary count, matrix, history⟩ =
      ⟨RawParser.Phase.lowUnary (count + amount), matrix, history⟩ := by
  induction amount generalizing count with
  | zero => simp
  | succ amount inductionHypothesis =>
      rw [List.replicate_succ, List.foldl_cons]
      simp only [RawParser.step, if_pos]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (count + 1)

private theorem foldl_loopUnary_true
    (count amount : ℕ) (matrix : Mat2 QI)
    (history : List RawParser.Constraint) :
    (List.replicate amount true).foldl RawParser.step
        ⟨RawParser.Phase.loopUnary count, matrix, history⟩ =
      ⟨RawParser.Phase.loopUnary (count + amount), matrix, history⟩ := by
  induction amount generalizing count with
  | zero => simp
  | succ amount inductionHypothesis =>
      rw [List.replicate_succ, List.foldl_cons]
      simp only [RawParser.step, if_pos]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (count + 1)

private theorem foldl_sector_first_two
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (first second : Bool) (matrix : Mat2 QI)
    (history : List RawParser.Constraint) :
    [first, second].foldl RawParser.step
        ⟨RawParser.Phase.sector kind exponent .zero, matrix, history⟩ =
      ⟨RawParser.Phase.sector kind exponent (.two first second),
        matrix, history⟩ := by
  rfl

theorem parse_initialHigh_through_two_sector_bits
    (exponent : ℕ) (positive : 1 ≤ exponent) (sector : Sector) :
    RawParser.parse
        (List.replicate exponent true ++ [false] ++
          [sectorFirstBit sector, sectorSecondBit sector]) =
      ⟨RawParser.Phase.sector .initialHigh exponent
          (.two (sectorFirstBit sector) (sectorSecondBit sector)),
        RawParser.identityMatrix, []⟩ := by
  cases exponent with
  | zero => omega
  | succ amount =>
      rw [RawParser.parse, List.foldl_append, List.foldl_append,
        List.replicate_succ, List.foldl_cons]
      change [sectorFirstBit sector, sectorSecondBit sector].foldl RawParser.step
        ([false].foldl RawParser.step
          ((List.replicate amount true).foldl RawParser.step
            ⟨RawParser.Phase.highUnary 1, RawParser.identityMatrix, []⟩)) = _
      rw [foldl_highUnary_true]
      rw [show [false].foldl RawParser.step
          ⟨RawParser.Phase.highUnary (1 + amount),
            RawParser.identityMatrix, []⟩ =
        ⟨RawParser.Phase.sector .initialHigh (1 + amount) .zero,
          RawParser.identityMatrix, []⟩ by rfl]
      simpa [Nat.add_comm] using
        foldl_sector_first_two .initialHigh (1 + amount)
          (sectorFirstBit sector) (sectorSecondBit sector)
          RawParser.identityMatrix []

theorem parse_initialLow_through_two_sector_bits
    (exponent : ℕ) (sector : Sector) :
    RawParser.parse
        (false :: List.replicate exponent true ++ [false] ++
          [sectorFirstBit sector, sectorSecondBit sector]) =
      ⟨RawParser.Phase.sector .initialLow exponent
          (.two (sectorFirstBit sector) (sectorSecondBit sector)),
        RawParser.identityMatrix, []⟩ := by
  rw [RawParser.parse, List.foldl_append, List.foldl_append,
    List.foldl_cons]
  change [sectorFirstBit sector, sectorSecondBit sector].foldl RawParser.step
    ([false].foldl RawParser.step
      ((List.replicate exponent true).foldl RawParser.step
        ⟨RawParser.Phase.lowUnary 0, RawParser.identityMatrix, []⟩)) = _
  rw [foldl_lowUnary_true]
  rw [show [false].foldl RawParser.step
      ⟨RawParser.Phase.lowUnary (0 + exponent), RawParser.identityMatrix, []⟩ =
    ⟨RawParser.Phase.sector .initialLow (0 + exponent) .zero,
      RawParser.identityMatrix, []⟩ by rfl]
  simpa only [_root_.zero_add] using
    foldl_sector_first_two .initialLow exponent
      (sectorFirstBit sector) (sectorSecondBit sector)
      RawParser.identityMatrix []

/-- Parsing a loop header and two sector bits from any completed-block state
preserves its matrix and history until the third sector bit. -/
theorem foldl_loop_through_two_sector_bits
    (state : RawParser.State) (exponent : ℕ) (sector : Sector)
    (phase : state.phase = .loopUnary 0) :
    (List.replicate exponent true ++ [false] ++
      [sectorFirstBit sector, sectorSecondBit sector]).foldl
        RawParser.step state =
      ⟨RawParser.Phase.sector .loop exponent
          (.two (sectorFirstBit sector) (sectorSecondBit sector)),
        state.matrix, state.history⟩ := by
  rcases state with ⟨statePhase, matrix, history⟩
  simp only at phase
  subst statePhase
  rw [List.foldl_append, List.foldl_append, foldl_loopUnary_true]
  rw [show [false].foldl RawParser.step
      ⟨RawParser.Phase.loopUnary (0 + exponent), matrix, history⟩ =
    ⟨RawParser.Phase.sector .loop (0 + exponent) .zero,
      matrix, history⟩ by rfl]
  simpa only [_root_.zero_add] using
    foldl_sector_first_two .loop exponent
      (sectorFirstBit sector) (sectorSecondBit sector) matrix history

private theorem sector_mem_projected_candidates (sector : Sector) :
    sector ∈ RawParser.sectorCandidates
      (.two (sectorFirstBit sector) (sectorSecondBit sector)) := by
  simpa using RawParserSemantics.sectorOfBits_mem_two_candidates
    (sectorFirstBit sector) (sectorSecondBit sector) (sectorThirdBit sector)

theorem initialHigh_twoBits_represents
    (fraction : Frac) (numerator : fraction.num ≠ 0)
    (high : 2 * normNat fraction.den ≤ normNat fraction.num) :
    let initial := CCLEncoder.initialHigh fraction numerator high
    let exponent := (highScan fraction high).exponent
    let sector := Sector.select initial.annulus.frac.value
    RawParserSemantics.Represents
      (RawParser.parse
        (List.replicate exponent true ++ [false] ++
          [sectorFirstBit sector, sectorSecondBit sector]))
      fraction.value fraction.value := by
  dsimp only
  let initial := CCLEncoder.initialHigh fraction numerator high
  let exponent := (highScan fraction high).exponent
  let sector := Sector.select initial.annulus.frac.value
  have full := initialHigh_fullBlock fraction numerator high
  have parsed := parse_initialHigh_through_two_sector_bits exponent
    (highScan fraction high).positive sector
  have initialRepresents :=
    RawParserSemantics.initialState_represents fraction.value
  rw [parsed]
  refine ⟨initialRepresents.1, initialRepresents.2.1, ?_⟩
  constructor
  · simp
  · exact ⟨full.1, sector, sector_mem_projected_candidates sector, full.2⟩

theorem initialLow_twoBits_represents
    (fraction : Frac) (numerator : fraction.num ≠ 0)
    (low : normNat fraction.num < 2 * normNat fraction.den) :
    let initial := CCLEncoder.initialLow fraction numerator low
    let exponent := (lowScan fraction numerator low).exponent
    let sector := Sector.select initial.annulus.frac.value
    RawParserSemantics.Represents
      (RawParser.parse
        (false :: List.replicate exponent true ++ [false] ++
          [sectorFirstBit sector, sectorSecondBit sector]))
      fraction.value fraction.value := by
  dsimp only
  let initial := CCLEncoder.initialLow fraction numerator low
  let exponent := (lowScan fraction numerator low).exponent
  let sector := Sector.select initial.annulus.frac.value
  have full := initialLow_fullBlock fraction numerator low
  have parsed := parse_initialLow_through_two_sector_bits exponent sector
  have initialRepresents :=
    RawParserSemantics.initialState_represents fraction.value
  rw [parsed]
  refine ⟨initialRepresents.1, initialRepresents.2.1, ?_⟩
  constructor
  · simp
  · exact ⟨full.1, sector, sector_mem_projected_candidates sector, full.2⟩

theorem loop_twoBits_represents
    (state : RawParser.State) (input value : QI)
    (statePhase : state.phase = .loopUnary 0)
    (before : RawParserSemantics.Represents state input value)
    (exponent : ℕ) (sector : Sector)
    (full : RawParser.fullBlockHolds .loop exponent sector value) :
    RawParserSemantics.Represents
      ((List.replicate exponent true ++ [false] ++
        [sectorFirstBit sector, sectorSecondBit sector]).foldl
          RawParser.step state) input value := by
  rw [foldl_loop_through_two_sector_bits state exponent sector statePhase]
  refine ⟨before.1, before.2.1, before.2.2.1, ?_⟩
  exact ⟨full.1, sector, sector_mem_projected_candidates sector, full.2⟩

theorem postInversion_residual_ne
    (old : CCLEncoder.Annulus) (post : CCLEncoder.PostInversion old) :
    old.frac.value - Sector.rep (Sector.select old.frac.value) ≠ 0 := by
  intro zero
  have value := postInversion_value old post
  rw [zero, mul_zero, inv_zero] at value
  exact postInversion_value_ne_zero old post value

/-- An integral zero subtraction says exactly that the represented fraction
is the selected Gaussian-rational sector representative. -/
theorem fraction_value_eq_sector_rep_of_sub_eq_zero
    (fraction : Frac) (sector : Sector)
    (terminal : fraction.num - sectorInt sector * fraction.den = 0) :
    fraction.value = sector.rep := by
  have numeratorEq :
      fraction.num = sectorInt sector * fraction.den := sub_eq_zero.mp terminal
  rw [Frac.value, numeratorEq, toRat_mul, toRat_sectorInt]
  calc
    sector.rep * toRat fraction.den * inv (toRat fraction.den) =
        sector.rep * (toRat fraction.den * inv (toRat fraction.den)) := by
      ring
    _ = sector.rep := by
      rw [mul_inv _ fraction.den_toRat_ne, GaussianRat.mul_one]

/-- Complete the selected third sector bit using the encoder's actual
post-inversion affine tail. -/
theorem complete_selected_sector
    (state : RawParser.State) (kind : RawParser.BlockKind) (exponent : ℕ)
    (input before : QI) (old : CCLEncoder.Annulus)
    (post : CCLEncoder.PostInversion old)
    (statePhase : state.phase =
      .sector kind exponent
        (.two (sectorFirstBit (Sector.select old.frac.value))
          (sectorSecondBit (Sector.select old.frac.value))))
    (beforeRepresents : RawParserSemantics.Represents state input before)
    (normalized :
      RawParser.normalizedValue kind exponent before = old.frac.value)
    (full : RawParser.fullBlockHolds kind exponent
      (Sector.select old.frac.value) before) :
    RawParserSemantics.Represents
      (RawParser.completeSector state kind exponent
        (sectorFirstBit (Sector.select old.frac.value))
        (sectorSecondBit (Sector.select old.frac.value))
        (sectorThirdBit (Sector.select old.frac.value)))
      input post.frac.value := by
  let sector := Sector.select old.frac.value
  have residual :
      RawParser.normalizedValue kind exponent before - sector.rep ≠ 0 := by
    rw [normalized]
    exact postInversion_residual_ne old post
  have postValue : post.frac.value =
      inv (gamma *
        (RawParser.normalizedValue kind exponent before - sector.rep)) := by
    rw [postInversion_value,
      show Sector.select old.frac.value = sector by rfl, ← normalized]
  apply RawParserSemantics.completeSector_represents_next state kind exponent
    (sectorFirstBit sector) (sectorSecondBit sector) (sectorThirdBit sector)
    input before post.frac.value statePhase beforeRepresents
  · rw [postValue]
    simpa using block_homographic_inverse kind exponent sector before residual
  · rw [postValue]
    simpa using block_inverse_denominator_ne kind exponent sector before residual
  · simpa using full
  · exact postInversion_loop_active old post

/-- Every encoder suffix contains at least its selected three-bit sector
code. -/
theorem two_lt_encodeTail_length (annulus : CCLEncoder.Annulus) :
    2 < (CCLEncoder.encodeTail annulus).word.length := by
  rw [CCLEncoder.encodeTail]
  split <;> simp

private theorem represented_base_is_prefix
    {base word : Prefix.Word} {input : QI}
    (baseRepresents : RawParserSemantics.Represented base input)
    (wordRepresents : RawParserSemantics.Represented word input)
    (length : base.length ≤ word.length) :
    base <+: word := by
  have takeRepresents : RawParserSemantics.Represented
      (word.take base.length) input :=
    RawParserSemantics.represented_of_prefix (List.take_prefix base.length word)
      wordRepresents
  have takeLength : (word.take base.length).length = base.length := by
    simp [List.length_take, min_eq_left length]
  have takeEqual : word.take base.length = base :=
    RawParserSemantics.represented_eq_of_length_eq takeLength takeRepresents
      baseRepresents
  rw [← takeEqual]
  exact List.take_prefix base.length word

/-- Every proper prefix of the encoder suffix beginning at a selected sector
is represented by an affine parser tail.  The terminal third sector bit is
excluded automatically; a nonterminal third bit changes to the actual
post-inversion tail and recurses at the strictly smaller denominator norm. -/
theorem encodeTail_proper_prefix_represented
    (annulus : CCLEncoder.Annulus) (base : Prefix.Word)
    (kind : RawParser.BlockKind) (exponent : ℕ) (input before : QI)
    (normalized :
      RawParser.normalizedValue kind exponent before = annulus.frac.value)
    (full : RawParser.fullBlockHolds kind exponent
      (Sector.select annulus.frac.value) before)
    (baseRepresents : RawParserSemantics.Represents
      (RawParser.parse
        (base ++ [sectorFirstBit (Sector.select annulus.frac.value),
          sectorSecondBit (Sector.select annulus.frac.value)])) input before)
    (basePhase :
      (RawParser.parse
        (base ++ [sectorFirstBit (Sector.select annulus.frac.value),
          sectorSecondBit (Sector.select annulus.frac.value)])).phase =
        .sector kind exponent
          (.two (sectorFirstBit (Sector.select annulus.frac.value))
            (sectorSecondBit (Sector.select annulus.frac.value))))
    (depth : ℕ)
    (proper : depth < (base ++ (CCLEncoder.encodeTail annulus).word).length) :
    RawParserSemantics.Represented
      ((base ++ (CCLEncoder.encodeTail annulus).word).take depth) input := by
  let sector := Sector.select annulus.frac.value
  let residual :=
    annulus.frac.num - sectorInt sector * annulus.frac.den
  by_cases terminal : residual = 0
  · have tailWord : (CCLEncoder.encodeTail annulus).word = sector.code := by
      rw [CCLEncoder.encodeTail]
      simp [sector, residual, terminal]
    let baseTwo :=
      base ++ [sectorFirstBit sector, sectorSecondBit sector]
    have baseTwoRepresents : RawParserSemantics.Represented baseTwo input := by
      exact ⟨before, by simpa [baseTwo, sector] using baseRepresents⟩
    have totalWord : base ++ (CCLEncoder.encodeTail annulus).word =
        baseTwo ++ [sectorThirdBit sector] := by
      rw [tailWord, sector_code_eq_bits]
      simp [baseTwo, List.append_assoc]
    have takeLength :
        ((base ++ (CCLEncoder.encodeTail annulus).word).take depth).length ≤
          baseTwo.length := by
      rw [totalWord] at proper ⊢
      rw [List.length_take, min_eq_left (Nat.le_of_lt proper)]
      simp only [List.length_append, List.length_singleton] at proper ⊢
      omega
    apply RawParserSemantics.represented_of_prefix
      (represented := baseTwoRepresents)
    apply (List.isPrefix_append_of_length takeLength).mp
    rw [← totalWord]
    exact List.take_prefix depth _
  · let post := CCLEncoder.postInversion annulus (by
        simpa [residual, sector] using terminal)
    have postOutside := postInversion_outside annulus post
    have postNumeratorMeasure :
        normNat post.frac.num = normNat annulus.frac.den := by
      rw [post.num_eq]
    let next := CCLEncoder.normalizeLoop post.frac
      (normNat annulus.frac.den) postOutside postNumeratorMeasure
    let nextExponent := (loopScan post.frac postOutside).exponent
    have nextExponentEq : next.exponent = nextExponent := by
      exact normalizeLoop_exponent post.frac (normNat annulus.frac.den)
        postOutside postNumeratorMeasure
    let baseTwo :=
      base ++ [sectorFirstBit sector, sectorSecondBit sector]
    let state := RawParser.parse baseTwo
    have stateRepresents : RawParserSemantics.Represents state input before := by
      simpa [state, baseTwo, sector] using baseRepresents
    have statePhase : state.phase =
        .sector kind exponent
          (.two (sectorFirstBit sector) (sectorSecondBit sector)) := by
      simpa [state, baseTwo, sector] using basePhase
    have completedRepresents := complete_selected_sector state kind exponent
      input before annulus post statePhase stateRepresents normalized full
    let completedBase := base ++ sector.code
    have parsedCompleted : RawParser.parse completedBase =
        RawParser.completeSector state kind exponent
          (sectorFirstBit sector) (sectorSecondBit sector)
          (sectorThirdBit sector) := by
      calc
        RawParser.parse completedBase =
            RawParser.parse
              (baseTwo ++ [sectorThirdBit sector]) := by
          congr 1
          simp [completedBase, baseTwo, sector_code_eq_bits,
            List.append_assoc]
        _ = RawParser.step state (sectorThirdBit sector) := by
          simp [RawParser.parse, List.foldl_append, state, baseTwo]
        _ = RawParser.completeSector state kind exponent
            (sectorFirstBit sector) (sectorSecondBit sector)
            (sectorThirdBit sector) :=
          RawParserSemantics.step_eq_completeSector state kind exponent
            (sectorFirstBit sector) (sectorSecondBit sector)
            (sectorThirdBit sector) statePhase
    have completedStateRepresents : RawParserSemantics.Represents
        (RawParser.parse completedBase) input post.frac.value := by
      rw [parsedCompleted]
      exact completedRepresents
    have completedPhase : (RawParser.parse completedBase).phase =
        .loopUnary 0 := by
      rw [parsedCompleted]
      rfl
    have nextFull : RawParser.fullBlockHolds .loop nextExponent
        (Sector.select next.annulus.frac.value) post.frac.value := by
      simpa [nextExponent, next] using
        normalizeLoop_fullBlock post.frac (normNat annulus.frac.den)
          postOutside postNumeratorMeasure
    have nextNormalized :
        RawParser.normalizedValue .loop nextExponent post.frac.value =
          next.annulus.frac.value := by
      rw [show next.annulus.frac =
          scaleDenominator post.frac nextExponent by
        simpa [nextExponent, next] using
          normalizeLoop_fraction post.frac (normNat annulus.frac.den)
            postOutside postNumeratorMeasure]
      exact (scaleDenominator_normalizedValue .loop post.frac nextExponent
        (by decide)).symm
    let nextSector := Sector.select next.annulus.frac.value
    have nextTwoRepresents := loop_twoBits_represents
      (RawParser.parse completedBase) input post.frac.value completedPhase
      completedStateRepresents nextExponent nextSector nextFull
    let nextBase := completedBase ++
      List.replicate nextExponent true ++ [false]
    have parsedNextTwo : RawParserSemantics.Represents
        (RawParser.parse
          (nextBase ++ [sectorFirstBit nextSector,
            sectorSecondBit nextSector])) input post.frac.value := by
      simpa [nextBase, RawParser.parse, List.foldl_append, List.append_assoc]
        using nextTwoRepresents
    have parsedNextPhase :
        (RawParser.parse
          (nextBase ++ [sectorFirstBit nextSector,
            sectorSecondBit nextSector])).phase =
          .sector .loop nextExponent
            (.two (sectorFirstBit nextSector)
              (sectorSecondBit nextSector)) := by
      rw [RawParser.parse, List.foldl_append]
      simpa [nextBase, RawParser.parse, List.foldl_append,
        List.append_assoc] using
        congrArg RawParser.State.phase
          (foldl_loop_through_two_sector_bits
            (RawParser.parse completedBase) nextExponent nextSector
            completedPhase)
    have wordEq : base ++ (CCLEncoder.encodeTail annulus).word =
        nextBase ++ (CCLEncoder.encodeTail next.annulus).word := by
      rw [CCLEncoder.encodeTail]
      simp [sector, residual, terminal, post, next, nextExponent,
        nextExponentEq, completedBase, nextBase, sector_code_eq_bits,
        List.append_assoc]
    rw [wordEq] at proper ⊢
    exact encodeTail_proper_prefix_represented next.annulus nextBase .loop
      nextExponent input post.frac.value nextNormalized nextFull
      parsedNextTwo parsedNextPhase depth proper
termination_by normNat annulus.frac.den
decreasing_by
  exact next.measure_lt

/-- The affine semantics recognizes exactly strict prefixes of the actual
terminating encoder suffix.  At a terminal subtraction neither possible next
bit has an affine tail; otherwise the proof follows the encoder's strict
denominator descent. -/
theorem represented_strictPrefix_encodeTail
    (annulus : CCLEncoder.Annulus) (base : Prefix.Word)
    (kind : RawParser.BlockKind) (exponent : ℕ) (input before : QI)
    (normalized :
      RawParser.normalizedValue kind exponent before = annulus.frac.value)
    (full : RawParser.fullBlockHolds kind exponent
      (Sector.select annulus.frac.value) before)
    (baseRepresents : RawParserSemantics.Represents
      (RawParser.parse
        (base ++ [sectorFirstBit (Sector.select annulus.frac.value),
          sectorSecondBit (Sector.select annulus.frac.value)])) input before)
    (basePhase :
      (RawParser.parse
        (base ++ [sectorFirstBit (Sector.select annulus.frac.value),
          sectorSecondBit (Sector.select annulus.frac.value)])).phase =
        .sector kind exponent
          (.two (sectorFirstBit (Sector.select annulus.frac.value))
            (sectorSecondBit (Sector.select annulus.frac.value))))
    (word : Prefix.Word)
    (wordRepresents : RawParserSemantics.Represented word input) :
    word <+: base ++ (CCLEncoder.encodeTail annulus).word ∧
      word ≠ base ++ (CCLEncoder.encodeTail annulus).word := by
  let sector := Sector.select annulus.frac.value
  let baseTwo :=
    base ++ [sectorFirstBit sector, sectorSecondBit sector]
  have baseTwoRepresents : RawParserSemantics.Represented baseTwo input := by
    exact ⟨before, by simpa [baseTwo, sector] using baseRepresents⟩
  have baseTwoLength :
      baseTwo.length <
        (base ++ (CCLEncoder.encodeTail annulus).word).length := by
    have tailLength := two_lt_encodeTail_length annulus
    simp only [baseTwo, List.length_append, List.length_cons, List.length_nil]
    omega
  by_cases short : word.length ≤ baseTwo.length
  · have proper :
        word.length <
          (base ++ (CCLEncoder.encodeTail annulus).word).length :=
      lt_of_le_of_lt short baseTwoLength
    have encoderPrefixRepresents := encodeTail_proper_prefix_represented
      annulus base kind exponent input before normalized full baseRepresents
        basePhase word.length proper
    have prefixLength :
        word.length =
          ((base ++ (CCLEncoder.encodeTail annulus).word).take
            word.length).length := by
      rw [List.length_take, min_eq_left (Nat.le_of_lt proper)]
    have wordEqual := RawParserSemantics.represented_eq_of_length_eq
      prefixLength wordRepresents encoderPrefixRepresents
    constructor
    · rw [wordEqual]
      exact List.take_prefix word.length _
    · intro equal
      have lengthEqual := congrArg List.length equal
      omega
  · have long : baseTwo.length < word.length := Nat.lt_of_not_ge short
    let residual :=
      annulus.frac.num - sectorInt sector * annulus.frac.den
    by_cases terminal : residual = 0
    · have basePrefix : baseTwo <+: word :=
        represented_base_is_prefix baseTwoRepresents wordRepresents
          (Nat.le_of_lt long)
      rcases basePrefix with ⟨suffix, rfl⟩
      cases suffix with
      | nil => simp at long
      | cons bit rest =>
          have childRepresents : RawParserSemantics.Represented
              (baseTwo ++ [bit]) input := by
            apply RawParserSemantics.represented_of_prefix
              (word := baseTwo ++ bit :: rest) (represented := wordRepresents)
            exact ⟨rest, by simp [List.append_assoc]⟩
          have terminalValue : annulus.frac.value = sector.rep :=
            fraction_value_eq_sector_rep_of_sub_eq_zero annulus.frac sector
              (by simpa [residual, sector] using terminal)
          have noStep := terminal_sector_no_canStep
            (RawParser.parse baseTwo) kind exponent
            (sectorFirstBit sector) (sectorSecondBit sector)
            (sectorThirdBit sector) input before
            (RawParser.parse_det_ne baseTwo)
            (by simpa [baseTwo, sector] using basePhase)
            (by simpa [baseTwo, sector] using baseRepresents)
            (by simpa [sector] using full)
            (by simpa [sector] using normalized.trans terminalValue) bit
          have possible : RawParserSemantics.CanStep
              (RawParser.parse baseTwo) input bit := by
            rcases childRepresents with ⟨tail, childRepresents⟩
            exact ⟨tail, by
              simpa [RawParser.parse, List.foldl_append] using childRepresents⟩
          exact (noStep possible).elim
    · let post := CCLEncoder.postInversion annulus (by
          simpa [residual, sector] using terminal)
      have postOutside := postInversion_outside annulus post
      have postNumeratorMeasure :
          normNat post.frac.num = normNat annulus.frac.den := by
        rw [post.num_eq]
      let next := CCLEncoder.normalizeLoop post.frac
        (normNat annulus.frac.den) postOutside postNumeratorMeasure
      let nextExponent := (loopScan post.frac postOutside).exponent
      have nextExponentEq : next.exponent = nextExponent := by
        exact normalizeLoop_exponent post.frac (normNat annulus.frac.den)
          postOutside postNumeratorMeasure
      let state := RawParser.parse baseTwo
      have stateRepresents :
          RawParserSemantics.Represents state input before := by
        simpa [state, baseTwo, sector] using baseRepresents
      have statePhase : state.phase =
          .sector kind exponent
            (.two (sectorFirstBit sector) (sectorSecondBit sector)) := by
        simpa [state, baseTwo, sector] using basePhase
      have completedRepresents := complete_selected_sector state kind exponent
        input before annulus post statePhase stateRepresents normalized full
      let completedBase := base ++ sector.code
      have parsedCompleted : RawParser.parse completedBase =
          RawParser.completeSector state kind exponent
            (sectorFirstBit sector) (sectorSecondBit sector)
            (sectorThirdBit sector) := by
        calc
          RawParser.parse completedBase =
              RawParser.parse (baseTwo ++ [sectorThirdBit sector]) := by
            congr 1
            simp [completedBase, baseTwo, sector_code_eq_bits,
              List.append_assoc]
          _ = RawParser.step state (sectorThirdBit sector) := by
            simp [RawParser.parse, List.foldl_append, state, baseTwo]
          _ = RawParser.completeSector state kind exponent
              (sectorFirstBit sector) (sectorSecondBit sector)
              (sectorThirdBit sector) :=
            RawParserSemantics.step_eq_completeSector state kind exponent
              (sectorFirstBit sector) (sectorSecondBit sector)
              (sectorThirdBit sector) statePhase
      have completedStateRepresents : RawParserSemantics.Represents
          (RawParser.parse completedBase) input post.frac.value := by
        rw [parsedCompleted]
        exact completedRepresents
      have completedPhase : (RawParser.parse completedBase).phase =
          .loopUnary 0 := by
        rw [parsedCompleted]
        rfl
      have nextFull : RawParser.fullBlockHolds .loop nextExponent
          (Sector.select next.annulus.frac.value) post.frac.value := by
        simpa [nextExponent, next] using
          normalizeLoop_fullBlock post.frac (normNat annulus.frac.den)
            postOutside postNumeratorMeasure
      have nextNormalized :
          RawParser.normalizedValue .loop nextExponent post.frac.value =
            next.annulus.frac.value := by
        rw [show next.annulus.frac =
            scaleDenominator post.frac nextExponent by
          simpa [nextExponent, next] using
            normalizeLoop_fraction post.frac (normNat annulus.frac.den)
              postOutside postNumeratorMeasure]
        exact (scaleDenominator_normalizedValue .loop post.frac nextExponent
          (by decide)).symm
      let nextSector := Sector.select next.annulus.frac.value
      have nextTwoRepresents := loop_twoBits_represents
        (RawParser.parse completedBase) input post.frac.value completedPhase
        completedStateRepresents nextExponent nextSector nextFull
      let nextBase := completedBase ++
        List.replicate nextExponent true ++ [false]
      have parsedNextTwo : RawParserSemantics.Represents
          (RawParser.parse
            (nextBase ++ [sectorFirstBit nextSector,
              sectorSecondBit nextSector])) input post.frac.value := by
        simpa [nextBase, RawParser.parse, List.foldl_append,
          List.append_assoc] using nextTwoRepresents
      have parsedNextPhase :
          (RawParser.parse
            (nextBase ++ [sectorFirstBit nextSector,
              sectorSecondBit nextSector])).phase =
            .sector .loop nextExponent
              (.two (sectorFirstBit nextSector)
                (sectorSecondBit nextSector)) := by
        rw [RawParser.parse, List.foldl_append]
        simpa [nextBase, RawParser.parse, List.foldl_append,
          List.append_assoc] using
          congrArg RawParser.State.phase
            (foldl_loop_through_two_sector_bits
              (RawParser.parse completedBase) nextExponent nextSector
              completedPhase)
      have wordEq : base ++ (CCLEncoder.encodeTail annulus).word =
          nextBase ++ (CCLEncoder.encodeTail next.annulus).word := by
        rw [CCLEncoder.encodeTail]
        simp [sector, residual, terminal, post, next, nextExponent,
          nextExponentEq, completedBase, nextBase, sector_code_eq_bits,
          List.append_assoc]
      rw [wordEq]
      exact represented_strictPrefix_encodeTail next.annulus nextBase .loop
        nextExponent input post.frac.value nextNormalized nextFull
        parsedNextTwo parsedNextPhase word wordRepresents
termination_by normNat annulus.frac.den
decreasing_by
  exact next.measure_lt

private theorem initialHigh_proper_prefix_represented
    (fraction : Frac) (numerator : fraction.num ≠ 0)
    (high : 2 * normNat fraction.den ≤ normNat fraction.num)
    (depth : ℕ)
    (proper : depth <
      ((CCLEncoder.initialHigh fraction numerator high).header ++
        (CCLEncoder.encodeTail
          (CCLEncoder.initialHigh fraction numerator high).annulus).word).length) :
    RawParserSemantics.Represented
      (((CCLEncoder.initialHigh fraction numerator high).header ++
        (CCLEncoder.encodeTail
          (CCLEncoder.initialHigh fraction numerator high).annulus).word).take
            depth) fraction.value := by
  let initial := CCLEncoder.initialHigh fraction numerator high
  let exponent := (highScan fraction high).exponent
  let sector := Sector.select initial.annulus.frac.value
  have normalized :
      RawParser.normalizedValue .initialHigh exponent fraction.value =
        initial.annulus.frac.value := by
    rw [show initial.annulus.frac = scaleDenominator fraction exponent by
      simpa [initial, exponent] using initialHigh_fraction fraction numerator high]
    exact (scaleDenominator_normalizedValue .initialHigh fraction exponent
      (by decide)).symm
  have full := initialHigh_fullBlock fraction numerator high
  have twoBits := initialHigh_twoBits_represents fraction numerator high
  have phase := parse_initialHigh_through_two_sector_bits exponent
    (highScan fraction high).positive sector
  have phase' := congrArg RawParser.State.phase phase
  apply encodeTail_proper_prefix_represented initial.annulus initial.header
    .initialHigh exponent fraction.value fraction.value normalized full
  · simpa [initial, exponent, sector, initialHigh_header] using twoBits
  · simpa [initial, exponent, sector, initialHigh_header] using phase'
  · simpa [initial] using proper

private theorem initialLow_proper_prefix_represented
    (fraction : Frac) (numerator : fraction.num ≠ 0)
    (low : normNat fraction.num < 2 * normNat fraction.den)
    (depth : ℕ)
    (proper : depth <
      ((CCLEncoder.initialLow fraction numerator low).header ++
        (CCLEncoder.encodeTail
          (CCLEncoder.initialLow fraction numerator low).annulus).word).length) :
    RawParserSemantics.Represented
      (((CCLEncoder.initialLow fraction numerator low).header ++
        (CCLEncoder.encodeTail
          (CCLEncoder.initialLow fraction numerator low).annulus).word).take
            depth) fraction.value := by
  let initial := CCLEncoder.initialLow fraction numerator low
  let exponent := (lowScan fraction numerator low).exponent
  let sector := Sector.select initial.annulus.frac.value
  have normalized :
      RawParser.normalizedValue .initialLow exponent fraction.value =
        initial.annulus.frac.value := by
    rw [show initial.annulus.frac = scaleNumerator fraction exponent by
      simpa [initial, exponent] using initialLow_fraction fraction numerator low]
    exact (scaleNumerator_normalizedValue fraction exponent).symm
  have full := initialLow_fullBlock fraction numerator low
  have twoBits := initialLow_twoBits_represents fraction numerator low
  have phase := parse_initialLow_through_two_sector_bits exponent sector
  have phase' := congrArg RawParser.State.phase phase
  apply encodeTail_proper_prefix_represented initial.annulus initial.header
    .initialLow exponent fraction.value fraction.value normalized full
  · simpa [initial, exponent, sector, initialLow_header] using twoBits
  · simpa [initial, exponent, sector, initialLow_header] using phase'
  · simpa [initial] using proper

/-- Every proper raw prefix emitted by the terminating integral encoder has
the affine parser semantics proved above. -/
theorem encode_proper_prefix_represented
    (fraction : Frac) (numerator : fraction.num ≠ 0) (depth : ℕ)
    (proper : depth < (CCLEncoder.encode fraction numerator).length) :
    RawParserSemantics.Represented
      ((CCLEncoder.encode fraction numerator).take depth) fraction.value := by
  by_cases high : 2 * normNat fraction.den ≤ normNat fraction.num
  · rw [CCLEncoder.encode_eq_high fraction numerator high] at proper ⊢
    exact initialHigh_proper_prefix_represented fraction numerator high depth
      (by simpa using proper)
  · have low := Nat.lt_of_not_ge high
    rw [CCLEncoder.encode_eq_low fraction numerator low] at proper ⊢
    exact initialLow_proper_prefix_represented fraction numerator
      low depth (by simpa using proper)

private theorem initialHigh_represented_strictPrefix
    (fraction : Frac) (numerator : fraction.num ≠ 0)
    (high : 2 * normNat fraction.den ≤ normNat fraction.num)
    (word : Prefix.Word)
    (wordRepresents : RawParserSemantics.Represented word fraction.value) :
    word <+:
        (CCLEncoder.initialHigh fraction numerator high).header ++
          (CCLEncoder.encodeTail
            (CCLEncoder.initialHigh fraction numerator high).annulus).word ∧
      word ≠
        (CCLEncoder.initialHigh fraction numerator high).header ++
          (CCLEncoder.encodeTail
            (CCLEncoder.initialHigh fraction numerator high).annulus).word := by
  let initial := CCLEncoder.initialHigh fraction numerator high
  let exponent := (highScan fraction high).exponent
  let sector := Sector.select initial.annulus.frac.value
  have normalized :
      RawParser.normalizedValue .initialHigh exponent fraction.value =
        initial.annulus.frac.value := by
    rw [show initial.annulus.frac = scaleDenominator fraction exponent by
      simpa [initial, exponent] using
        initialHigh_fraction fraction numerator high]
    exact (scaleDenominator_normalizedValue .initialHigh fraction exponent
      (by decide)).symm
  have full := initialHigh_fullBlock fraction numerator high
  have twoBits := initialHigh_twoBits_represents fraction numerator high
  have phase := parse_initialHigh_through_two_sector_bits exponent
    (highScan fraction high).positive sector
  have phase' := congrArg RawParser.State.phase phase
  apply represented_strictPrefix_encodeTail initial.annulus initial.header
    .initialHigh exponent fraction.value fraction.value normalized full
  · simpa [initial, exponent, sector, initialHigh_header] using twoBits
  · simpa [initial, exponent, sector, initialHigh_header] using phase'
  · exact wordRepresents

private theorem initialLow_represented_strictPrefix
    (fraction : Frac) (numerator : fraction.num ≠ 0)
    (low : normNat fraction.num < 2 * normNat fraction.den)
    (word : Prefix.Word)
    (wordRepresents : RawParserSemantics.Represented word fraction.value) :
    word <+:
        (CCLEncoder.initialLow fraction numerator low).header ++
          (CCLEncoder.encodeTail
            (CCLEncoder.initialLow fraction numerator low).annulus).word ∧
      word ≠
        (CCLEncoder.initialLow fraction numerator low).header ++
          (CCLEncoder.encodeTail
            (CCLEncoder.initialLow fraction numerator low).annulus).word := by
  let initial := CCLEncoder.initialLow fraction numerator low
  let exponent := (lowScan fraction numerator low).exponent
  let sector := Sector.select initial.annulus.frac.value
  have normalized :
      RawParser.normalizedValue .initialLow exponent fraction.value =
        initial.annulus.frac.value := by
    rw [show initial.annulus.frac = scaleNumerator fraction exponent by
      simpa [initial, exponent] using
        initialLow_fraction fraction numerator low]
    exact (scaleNumerator_normalizedValue fraction exponent).symm
  have full := initialLow_fullBlock fraction numerator low
  have twoBits := initialLow_twoBits_represents fraction numerator low
  have phase := parse_initialLow_through_two_sector_bits exponent sector
  have phase' := congrArg RawParser.State.phase phase
  apply represented_strictPrefix_encodeTail initial.annulus initial.header
    .initialLow exponent fraction.value fraction.value normalized full
  · simpa [initial, exponent, sector, initialLow_header] using twoBits
  · simpa [initial, exponent, sector, initialLow_header] using phase'
  · exact wordRepresents

/-- Soundness of the raw parser against the terminating integral encoder:
every affinely represented word is a strict prefix of the unique emitted
word. -/
theorem represented_strictPrefix_encode
    (fraction : Frac) (numerator : fraction.num ≠ 0)
    (word : Prefix.Word)
    (represented : RawParserSemantics.Represented word fraction.value) :
    word <+: CCLEncoder.encode fraction numerator ∧
      word ≠ CCLEncoder.encode fraction numerator := by
  by_cases high : 2 * normNat fraction.den ≤ normNat fraction.num
  · rw [CCLEncoder.encode_eq_high fraction numerator high]
    exact initialHigh_represented_strictPrefix fraction numerator high word
      represented
  · have low := Nat.lt_of_not_ge high
    rw [CCLEncoder.encode_eq_low fraction numerator low]
    exact initialLow_represented_strictPrefix fraction numerator low word
      represented

/-- Exact parser/encoder bridge: affine parser semantics holds precisely on
the proper finite prefixes of the terminating encoder output. -/
theorem represented_iff_strictPrefix_encode
    (fraction : Frac) (numerator : fraction.num ≠ 0)
    (word : Prefix.Word) :
    RawParserSemantics.Represented word fraction.value ↔
      word <+: CCLEncoder.encode fraction numerator ∧
        word ≠ CCLEncoder.encode fraction numerator := by
  constructor
  · exact represented_strictPrefix_encode fraction numerator word
  · rintro ⟨isPrefix, strict⟩
    rcases isPrefix with ⟨suffix, encodingEq⟩
    have suffixNe : suffix ≠ [] := by
      intro empty
      subst suffix
      exact strict (by simpa using encodingEq)
    have proper : word.length <
        (CCLEncoder.encode fraction numerator).length := by
      rw [← encodingEq]
      have suffixPositive : 0 < suffix.length :=
        List.length_pos_iff.mpr suffixNe
      simp only [List.length_append]
      omega
    have represented := encode_proper_prefix_represented fraction numerator
      word.length proper
    have prefixTake :
        (CCLEncoder.encode fraction numerator).take word.length = word := by
      rw [← encodingEq]
      simp
    rwa [prefixTake] at represented

end EncoderParserBridge
end CCL
