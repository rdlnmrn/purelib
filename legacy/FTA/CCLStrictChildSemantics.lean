import FTA.CCLBranchPlan
import FTA.CCLHermitianBox

/-!
# Stable next-bit semantics on a strict parser cell

The finite branch plan records only the comparisons that can change the next
raw bit.  This module proves the missing semantic direction: two points that
satisfy the current parser state and lie on the same strict side of every
planned comparison cannot select different children.
-/

namespace FTA
namespace CCLStrictChildSemantics

open CCL CCL.GaussianRat
open CCL.EncoderParserBridge
open FTA.CCLBranchPlan
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLHermitianBox

abbrev QI := CCL.GaussianRat

/-- The raw bit selected by the genuinely new comparison at a parser phase.
Unlike `CanAdvanceAt`, this finite discriminator deliberately ignores retained
history and predicates shared by both children. -/
def localBit (phase : RawParser.Phase) (value : QI) : Bool :=
  match phase with
  | .initial => decide ((2 : ℚ) ≤ normSq value)
  | .highUnary count =>
      decide ((2 : ℚ) ^ (count + 1) ≤ normSq value)
  | .lowUnary count =>
      decide (normSq value < ((2 : ℚ) ^ count)⁻¹)
  | .loopUnary count =>
      decide ((2 : ℚ) ^ (count + 1) < normSq value)
  | .sector kind exponent bits =>
      let z := RawParser.normalizedValue kind exponent value
      match bits with
      | .zero =>
          !decide (1 / 2 ≤ z.im) &&
            (decide (z.im ≤ -1 / 2) || decide (z.re ≤ -1 / 2))
      | .one false => decide (z.re < 1 / 2)
      | .one true => decide (-1 / 2 < z.re)
      | .two false false => decide (1 / 2 ≤ z.im)
      | .two false true => decide (z.re ≤ -1 / 2)
      | .two true false => decide (z.im ≤ -1 / 2)
      | .two true true => decide (1 / 2 ≤ z.re)

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

/-- Every actually admissible child has the phase-local bit.  Historical
constraints establish reachability but cannot influence this Boolean. -/
theorem canAdvanceAt_bit_eq_localBit
    (state : RawParser.State) (value : QI) (bit : Bool)
    (holds : CanAdvanceAt state bit value) :
    bit = localBit state.phase value := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bit with
      | false =>
          have low : normSq value < 2 := by
            simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds,
              RawParser.activeHolds] using holds.2
          simp [localBit, not_le.mpr low]
      | true =>
          have high : (2 : ℚ) ≤ normSq value := by
            simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds,
              RawParser.activeHolds] using holds.2
          simp [localBit, high]
  | highUnary count =>
      cases bit with
      | false =>
          have low : normSq value < (2 : ℚ) ^ (count + 1) := by
            simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds,
              RawParser.activeHolds] using holds.2.1.2
          simp [localBit, not_le.mpr low]
      | true =>
          have high : (2 : ℚ) ^ (count + 1) ≤ normSq value := by
            simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds,
              RawParser.activeHolds] using holds.2
          simp [localBit, high]
  | lowUnary count =>
      have powerPositive : (0 : ℚ) < (2 : ℚ) ^ count :=
        pow_pos (by norm_num) count
      cases bit with
      | false =>
          have lower : 1 ≤ (2 : ℚ) ^ count * normSq value := by
            simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds,
              RawParser.activeHolds] using holds.2.1.1
          have low : ¬(normSq value < ((2 : ℚ) ^ count)⁻¹) := by
            rw [not_lt]
            rw [show ((2 : ℚ) ^ count)⁻¹ = 1 / (2 : ℚ) ^ count by simp]
            apply (div_le_iff₀ powerPositive).2
            calc
              (1 : ℚ) ≤ (2 : ℚ) ^ count * normSq value := lower
              _ = normSq value * (2 : ℚ) ^ count := by ring
          simp [localBit, low]
      | true =>
          have scaled : (2 : ℚ) ^ count * normSq value < 1 := by
            cases count with
            | zero =>
                simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds,
                  RawParser.activeHolds] using holds.2
            | succ count =>
                simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds,
                  RawParser.activeHolds] using holds.2
          have low : normSq value < ((2 : ℚ) ^ count)⁻¹ := by
            rw [show ((2 : ℚ) ^ count)⁻¹ = 1 / (2 : ℚ) ^ count by simp]
            apply (lt_div_iff₀ powerPositive).2
            calc
              normSq value * (2 : ℚ) ^ count =
                  (2 : ℚ) ^ count * normSq value := by ring
              _ < 1 := scaled
          simp [localBit, low]
  | loopUnary count =>
      cases bit with
      | false =>
          have bounded : normSq value ≤ (2 : ℚ) ^ (count + 1) := by
            simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds,
              RawParser.activeHolds] using holds.2.1.2
          simp [localBit, not_lt_of_ge bounded]
      | true =>
          have high : (2 : ℚ) ^ (count + 1) < normSq value := by
            simpa [CanAdvanceAt, RawParser.step, RawParser.State.Holds,
              RawParser.activeHolds] using holds.2
          simp [localBit, high]
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          rcases holds.2 with ⟨radial, sector, member, sectorHolds⟩
          have projection := first_projection_of_mem_one bit
            sector member
          cases sector <;> simp [sectorFirstBit] at projection <;>
            subst bit <;>
            by_cases high : 1 / 2 ≤
              (RawParser.normalizedValue kind exponent value).im <;>
            by_cases low :
              (RawParser.normalizedValue kind exponent value).im ≤ -1 / 2 <;>
            by_cases left :
              (RawParser.normalizedValue kind exponent value).re ≤ -1 / 2 <;>
            simp_all [localBit, Sector.Holds] <;> linarith
      | one first =>
          rcases holds.2 with ⟨radial, sector, member, sectorHolds⟩
          have projections := projections_of_mem_two first bit
            sector member
          cases first <;> cases bit <;> cases sector <;>
            simp_all [localBit, Sector.Holds] <;> linarith
      | two first second =>
          rcases holds.1 with ⟨radial, sectorHolds⟩
          cases first <;> cases second <;> cases bit <;>
            simp_all [localBit, RawParser.sectorOfBits, Sector.Holds]

@[simp] theorem eval_normalizedRealComparisonForm
    (kind : RawParser.BlockKind) (exponent : ℕ) (threshold : ℚ) (z : QI) :
    (realComparisonForm
      (CCLParserGeometry.normalizedMatrix kind exponent
        RawParser.identityMatrix) threshold).eval z =
      (RawParser.normalizedValue kind exponent z).re - threshold := by
  let M := CCLParserGeometry.normalizedMatrix kind exponent
    RawParser.identityMatrix
  have lowerRow := CCLParserGeometry.normalizedMatrix_lowerRow kind exponent
    RawParser.identityMatrix
  have denominator : M.c * z + M.d ≠ 0 := by
    rw [lowerRow.1, lowerRow.2]
    exact CCLParserGeometry.identityMatrix_denominator_ne z
  have homographic : RatBox.homographic M z =
      RawParser.normalizedValue kind exponent z := by
    simpa [M, CCLParserGeometry.homographic_identityMatrix] using
      CCLParserGeometry.homographic_normalizedMatrix kind exponent
        RawParser.identityMatrix z
  rw [cleared_real_identity M threshold z denominator, homographic]
  rw [lowerRow.1, lowerRow.2]
  simp [RawParser.identityMatrix, normSq]

@[simp] theorem eval_normalizedImagComparisonForm
    (kind : RawParser.BlockKind) (exponent : ℕ) (threshold : ℚ) (z : QI) :
    (imagComparisonForm
      (CCLParserGeometry.normalizedMatrix kind exponent
        RawParser.identityMatrix) threshold).eval z =
      (RawParser.normalizedValue kind exponent z).im - threshold := by
  let M := CCLParserGeometry.normalizedMatrix kind exponent
    RawParser.identityMatrix
  have lowerRow := CCLParserGeometry.normalizedMatrix_lowerRow kind exponent
    RawParser.identityMatrix
  have denominator : M.c * z + M.d ≠ 0 := by
    rw [lowerRow.1, lowerRow.2]
    exact CCLParserGeometry.identityMatrix_denominator_ne z
  have homographic : RatBox.homographic M z =
      RawParser.normalizedValue kind exponent z := by
    simpa [M, CCLParserGeometry.homographic_identityMatrix] using
      CCLParserGeometry.homographic_normalizedMatrix kind exponent
        RawParser.identityMatrix z
  rw [cleared_imag_identity M threshold z denominator, homographic]
  rw [lowerRow.1, lowerRow.2]
  simp [RawParser.identityMatrix, normSq]

private theorem decide_lt_threshold_eq_of_mul_sub_pos
    (left right threshold : ℚ)
    (same : 0 < (left - threshold) * (right - threshold)) :
    decide (left < threshold) = decide (right < threshold) := by
  apply Bool.decide_congr
  constructor
  · intro leftLow
    by_contra rightNotLow
    have nonpositive :
        (left - threshold) * (right - threshold) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    exact (not_lt_of_ge nonpositive) same
  · intro rightLow
    by_contra leftNotLow
    have nonpositive :
        (left - threshold) * (right - threshold) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    exact (not_lt_of_ge nonpositive) same

private theorem decide_threshold_le_eq_of_mul_sub_pos
    (left right threshold : ℚ)
    (same : 0 < (left - threshold) * (right - threshold)) :
    decide (threshold ≤ left) = decide (threshold ≤ right) := by
  apply Bool.decide_congr
  constructor
  · intro leftHigh
    by_contra rightNotHigh
    have nonpositive :
        (left - threshold) * (right - threshold) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    exact (not_lt_of_ge nonpositive) same
  · intro rightHigh
    by_contra leftNotHigh
    have nonpositive :
        (left - threshold) * (right - threshold) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    exact (not_lt_of_ge nonpositive) same

private theorem decide_le_threshold_eq_of_mul_sub_pos
    (left right threshold : ℚ)
    (same : 0 < (left - threshold) * (right - threshold)) :
    decide (left ≤ threshold) = decide (right ≤ threshold) := by
  apply Bool.decide_congr
  constructor
  · intro leftLow
    by_contra rightNotLow
    have nonpositive :
        (left - threshold) * (right - threshold) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    exact (not_lt_of_ge nonpositive) same
  · intro rightLow
    by_contra leftNotLow
    have nonpositive :
        (left - threshold) * (right - threshold) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    exact (not_lt_of_ge nonpositive) same

private theorem decide_threshold_lt_eq_of_mul_sub_pos
    (left right threshold : ℚ)
    (same : 0 < (left - threshold) * (right - threshold)) :
    decide (threshold < left) = decide (threshold < right) := by
  apply Bool.decide_congr
  constructor
  · intro leftHigh
    by_contra rightNotHigh
    have nonpositive :
        (left - threshold) * (right - threshold) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    exact (not_lt_of_ge nonpositive) same
  · intro rightHigh
    by_contra leftNotHigh
    have nonpositive :
        (left - threshold) * (right - threshold) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    exact (not_lt_of_ge nonpositive) same

/-- Two rational comparison values have the same complete sign status when
they are strictly on the same side of zero or are both exactly zero.  The
second alternative is essential on a retained parser-boundary path. -/
def SameSignOrBothZero (left right : ℚ) : Prop :=
  0 < left * right ∨ (left = 0 ∧ right = 0)

private theorem decide_lt_threshold_eq_of_sameSignOrBothZero
    (left right threshold : ℚ)
    (same : SameSignOrBothZero (left - threshold) (right - threshold)) :
    decide (left < threshold) = decide (right < threshold) := by
  rcases same with strict | ⟨leftZero, rightZero⟩
  · exact decide_lt_threshold_eq_of_mul_sub_pos left right threshold strict
  · have leftEq : left = threshold := sub_eq_zero.mp leftZero
    have rightEq : right = threshold := sub_eq_zero.mp rightZero
    simp [leftEq, rightEq]

private theorem decide_threshold_le_eq_of_sameSignOrBothZero
    (left right threshold : ℚ)
    (same : SameSignOrBothZero (left - threshold) (right - threshold)) :
    decide (threshold ≤ left) = decide (threshold ≤ right) := by
  rcases same with strict | ⟨leftZero, rightZero⟩
  · exact decide_threshold_le_eq_of_mul_sub_pos left right threshold strict
  · have leftEq : left = threshold := sub_eq_zero.mp leftZero
    have rightEq : right = threshold := sub_eq_zero.mp rightZero
    simp [leftEq, rightEq]

private theorem decide_le_threshold_eq_of_sameSignOrBothZero
    (left right threshold : ℚ)
    (same : SameSignOrBothZero (left - threshold) (right - threshold)) :
    decide (left ≤ threshold) = decide (right ≤ threshold) := by
  rcases same with strict | ⟨leftZero, rightZero⟩
  · exact decide_le_threshold_eq_of_mul_sub_pos left right threshold strict
  · have leftEq : left = threshold := sub_eq_zero.mp leftZero
    have rightEq : right = threshold := sub_eq_zero.mp rightZero
    simp [leftEq, rightEq]

private theorem decide_threshold_lt_eq_of_sameSignOrBothZero
    (left right threshold : ℚ)
    (same : SameSignOrBothZero (left - threshold) (right - threshold)) :
    decide (threshold < left) = decide (threshold < right) := by
  rcases same with strict | ⟨leftZero, rightZero⟩
  · exact decide_threshold_lt_eq_of_mul_sub_pos left right threshold strict
  · have leftEq : left = threshold := sub_eq_zero.mp leftZero
    have rightEq : right = threshold := sub_eq_zero.mp rightZero
    simp [leftEq, rightEq]

/-- The phase-local discriminator is also constant on a closed sign stratum:
each required comparison may either keep one strict sign or remain exact
equality at both points. -/
theorem localBit_eq_of_localDecisionForms_sameSignOrBothZero
    (phase : RawParser.Phase) (left right : QI)
    (sameSigns : ∀ form ∈ localDecisionForms phase,
      SameSignOrBothZero (form.eval left) (form.eval right)) :
    localBit phase left = localBit phase right := by
  cases phase with
  | initial =>
      have sign := sameSigns
        (CCLParserGeometry.affineNormComparisonForm 2)
          (by simp [localDecisionForms])
      simp only [CCLParserGeometry.eval_affineNormComparisonForm] at sign
      exact decide_threshold_le_eq_of_sameSignOrBothZero _ _ 2 sign
  | highUnary count =>
      have sign := sameSigns
        (CCLParserGeometry.affineNormComparisonForm
          ((2 : ℚ) ^ (count + 1))) (by simp [localDecisionForms])
      simp only [CCLParserGeometry.eval_affineNormComparisonForm] at sign
      exact decide_threshold_le_eq_of_sameSignOrBothZero _ _
        ((2 : ℚ) ^ (count + 1)) sign
  | lowUnary count =>
      cases count with
      | zero =>
          have sign := sameSigns
            (CCLParserGeometry.affineNormComparisonForm 1)
              (by simp [localDecisionForms])
          simp only [CCLParserGeometry.eval_affineNormComparisonForm] at sign
          simpa [localBit] using
            decide_lt_threshold_eq_of_sameSignOrBothZero (normSq left)
              (normSq right) 1 sign
      | succ count =>
          have sign := sameSigns
            (CCLParserGeometry.affineNormComparisonForm
              (1 / (2 : ℚ) ^ (count + 1)))
                (by simp [localDecisionForms])
          simp only [CCLParserGeometry.eval_affineNormComparisonForm] at sign
          apply decide_lt_threshold_eq_of_sameSignOrBothZero _ _
            (((2 : ℚ) ^ (count + 1))⁻¹)
          simpa only [one_div] using sign
  | loopUnary count =>
      have sign := sameSigns
        (CCLParserGeometry.affineNormComparisonForm
          ((2 : ℚ) ^ (count + 1))) (by simp [localDecisionForms])
      simp only [CCLParserGeometry.eval_affineNormComparisonForm] at sign
      exact decide_threshold_lt_eq_of_sameSignOrBothZero _ _
        ((2 : ℚ) ^ (count + 1)) sign
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          have realLow := sameSigns
            (realComparisonForm
              (CCLParserGeometry.normalizedMatrix kind exponent
                RawParser.identityMatrix) (-1 / 2))
              (by simp [localDecisionForms])
          have imagHigh := sameSigns
            (imagComparisonForm
              (CCLParserGeometry.normalizedMatrix kind exponent
                RawParser.identityMatrix) (1 / 2))
              (by simp [localDecisionForms])
          have imagLow := sameSigns
            (imagComparisonForm
              (CCLParserGeometry.normalizedMatrix kind exponent
                RawParser.identityMatrix) (-1 / 2))
              (by simp [localDecisionForms])
          simp only [eval_normalizedRealComparisonForm] at realLow
          simp only [eval_normalizedImagComparisonForm] at imagHigh imagLow
          have realEq := decide_le_threshold_eq_of_sameSignOrBothZero _ _
            (-1 / 2) realLow
          have imagHighEq := decide_threshold_le_eq_of_sameSignOrBothZero _ _
            (1 / 2) imagHigh
          have imagLowEq := decide_le_threshold_eq_of_sameSignOrBothZero _ _
            (-1 / 2) imagLow
          simp only [localBit]
          rw [imagHighEq, imagLowEq, realEq]
      | one first =>
          cases first with
          | false =>
              have realHigh := sameSigns
                (realComparisonForm
                  (CCLParserGeometry.normalizedMatrix kind exponent
                    RawParser.identityMatrix) (1 / 2))
                (by simp [localDecisionForms])
              simp only [eval_normalizedRealComparisonForm] at realHigh
              exact decide_lt_threshold_eq_of_sameSignOrBothZero _ _ (1 / 2)
                realHigh
          | true =>
              have realLow := sameSigns
                (realComparisonForm
                  (CCLParserGeometry.normalizedMatrix kind exponent
                    RawParser.identityMatrix) (-1 / 2))
                (by simp [localDecisionForms])
              simp only [eval_normalizedRealComparisonForm] at realLow
              exact decide_threshold_lt_eq_of_sameSignOrBothZero _ _ (-1 / 2)
                realLow
      | two first second =>
          cases first <;> cases second
          · have imagHigh := sameSigns
              (imagComparisonForm
                (CCLParserGeometry.normalizedMatrix kind exponent
                  RawParser.identityMatrix) (1 / 2))
                (by simp [localDecisionForms])
            simp only [eval_normalizedImagComparisonForm] at imagHigh
            exact decide_threshold_le_eq_of_sameSignOrBothZero _ _ (1 / 2)
              imagHigh
          · have realLow := sameSigns
              (realComparisonForm
                (CCLParserGeometry.normalizedMatrix kind exponent
                  RawParser.identityMatrix) (-1 / 2))
                (by simp [localDecisionForms])
            simp only [eval_normalizedRealComparisonForm] at realLow
            exact decide_le_threshold_eq_of_sameSignOrBothZero _ _ (-1 / 2)
              realLow
          · have imagLow := sameSigns
              (imagComparisonForm
                (CCLParserGeometry.normalizedMatrix kind exponent
                  RawParser.identityMatrix) (-1 / 2))
                (by simp [localDecisionForms])
            simp only [eval_normalizedImagComparisonForm] at imagLow
            exact decide_le_threshold_eq_of_sameSignOrBothZero _ _ (-1 / 2)
              imagLow
          · have realHigh := sameSigns
              (realComparisonForm
                (CCLParserGeometry.normalizedMatrix kind exponent
                  RawParser.identityMatrix) (1 / 2))
                (by simp [localDecisionForms])
            simp only [eval_normalizedRealComparisonForm] at realHigh
            exact decide_threshold_le_eq_of_sameSignOrBothZero _ _ (1 / 2)
              realHigh

/-- The larger lookahead plan remains a sufficient sign family, by
restriction to the forms which decide the current bit. -/
theorem localBit_eq_of_localForms_sameSignOrBothZero
    (phase : RawParser.Phase) (left right : QI)
    (sameSigns : ∀ form ∈ localForms phase,
      SameSignOrBothZero (form.eval left) (form.eval right)) :
    localBit phase left = localBit phase right := by
  apply localBit_eq_of_localDecisionForms_sameSignOrBothZero
  intro form member
  exact sameSigns form (localDecisionForms_subset_localForms phase member)

/-- The phase-local discriminator is constant on every open sign cell cut out
by the finite local branch plan. -/
theorem localBit_eq_of_localForms_sameSigns
    (phase : RawParser.Phase) (left right : QI)
    (sameSigns : ∀ form ∈ localForms phase,
      0 < form.eval left * form.eval right) :
    localBit phase left = localBit phase right := by
  cases phase with
  | initial =>
      have sign := sameSigns
        (CCLParserGeometry.affineNormComparisonForm 2) (by simp)
      simp only [CCLParserGeometry.eval_affineNormComparisonForm] at sign
      exact decide_threshold_le_eq_of_mul_sub_pos _ _ 2 sign
  | highUnary count =>
      have sign := sameSigns
        (CCLParserGeometry.affineNormComparisonForm
          ((2 : ℚ) ^ (count + 1))) (by simp)
      simp only [CCLParserGeometry.eval_affineNormComparisonForm] at sign
      exact decide_threshold_le_eq_of_mul_sub_pos _ _
        ((2 : ℚ) ^ (count + 1)) sign
  | lowUnary count =>
      cases count with
      | zero =>
          have sign := sameSigns
            (CCLParserGeometry.affineNormComparisonForm 1) (by simp)
          simp only [CCLParserGeometry.eval_affineNormComparisonForm] at sign
          simpa [localBit] using
            decide_lt_threshold_eq_of_mul_sub_pos (normSq left)
              (normSq right) 1 sign
      | succ count =>
          have sign := sameSigns
            (CCLParserGeometry.affineNormComparisonForm
              (1 / (2 : ℚ) ^ (count + 1))) (by simp)
          simp only [CCLParserGeometry.eval_affineNormComparisonForm] at sign
          apply decide_lt_threshold_eq_of_mul_sub_pos _ _
            (((2 : ℚ) ^ (count + 1))⁻¹)
          simpa only [one_div] using sign
  | loopUnary count =>
      have sign := sameSigns
        (CCLParserGeometry.affineNormComparisonForm
          ((2 : ℚ) ^ (count + 1))) (by simp)
      simp only [CCLParserGeometry.eval_affineNormComparisonForm] at sign
      exact decide_threshold_lt_eq_of_mul_sub_pos _ _
        ((2 : ℚ) ^ (count + 1)) sign
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          have realLow := sameSigns
            (realComparisonForm
              (CCLParserGeometry.normalizedMatrix kind exponent
                RawParser.identityMatrix) (-1 / 2)) (by simp)
          have imagHigh := sameSigns
            (imagComparisonForm
              (CCLParserGeometry.normalizedMatrix kind exponent
                RawParser.identityMatrix) (1 / 2)) (by simp)
          have imagLow := sameSigns
            (imagComparisonForm
              (CCLParserGeometry.normalizedMatrix kind exponent
                RawParser.identityMatrix) (-1 / 2)) (by simp)
          simp only [eval_normalizedRealComparisonForm] at realLow
          simp only [eval_normalizedImagComparisonForm] at imagHigh imagLow
          have realEq := decide_le_threshold_eq_of_mul_sub_pos _ _
            (-1 / 2) realLow
          have imagHighEq := decide_threshold_le_eq_of_mul_sub_pos _ _
            (1 / 2) imagHigh
          have imagLowEq := decide_le_threshold_eq_of_mul_sub_pos _ _
            (-1 / 2) imagLow
          simp only [localBit]
          rw [imagHighEq, imagLowEq, realEq]
      | one first =>
          cases first with
          | false =>
              have realHigh := sameSigns
                (realComparisonForm
                  (CCLParserGeometry.normalizedMatrix kind exponent
                    RawParser.identityMatrix) (1 / 2)) (by simp)
              have imagHigh := sameSigns
                (imagComparisonForm
                  (CCLParserGeometry.normalizedMatrix kind exponent
                    RawParser.identityMatrix) (1 / 2)) (by simp)
              simp only [eval_normalizedRealComparisonForm] at realHigh
              exact decide_lt_threshold_eq_of_mul_sub_pos _ _ (1 / 2)
                realHigh
          | true =>
              have realLow := sameSigns
                (realComparisonForm
                  (CCLParserGeometry.normalizedMatrix kind exponent
                    RawParser.identityMatrix) (-1 / 2)) (by simp)
              have imagLow := sameSigns
                (imagComparisonForm
                  (CCLParserGeometry.normalizedMatrix kind exponent
                    RawParser.identityMatrix) (-1 / 2)) (by simp)
              simp only [eval_normalizedRealComparisonForm] at realLow
              exact decide_threshold_lt_eq_of_mul_sub_pos _ _ (-1 / 2)
                realLow
      | two first second =>
          cases first <;> cases second
          · have imagHigh := sameSigns
              (imagComparisonForm
                (CCLParserGeometry.normalizedMatrix kind exponent
                  RawParser.identityMatrix) (1 / 2)) (by simp)
            simp only [eval_normalizedImagComparisonForm] at imagHigh
            exact decide_threshold_le_eq_of_mul_sub_pos _ _ (1 / 2)
              imagHigh
          · have realLow := sameSigns
              (realComparisonForm
                (CCLParserGeometry.normalizedMatrix kind exponent
                  RawParser.identityMatrix) (-1 / 2)) (by simp)
            simp only [eval_normalizedRealComparisonForm] at realLow
            exact decide_le_threshold_eq_of_mul_sub_pos _ _ (-1 / 2)
              realLow
          · have imagLow := sameSigns
              (imagComparisonForm
                (CCLParserGeometry.normalizedMatrix kind exponent
                  RawParser.identityMatrix) (-1 / 2)) (by simp)
            simp only [eval_normalizedImagComparisonForm] at imagLow
            exact decide_le_threshold_eq_of_mul_sub_pos _ _ (-1 / 2)
              imagLow
          · have realHigh := sameSigns
              (realComparisonForm
                (CCLParserGeometry.normalizedMatrix kind exponent
                  RawParser.identityMatrix) (1 / 2)) (by simp)
            simp only [eval_normalizedRealComparisonForm] at realHigh
            exact decide_threshold_le_eq_of_mul_sub_pos _ _ (1 / 2)
              realHigh

/-- The same local discriminator in the original polynomial coordinate. -/
def inputLocalBit (state : RawParser.State) (input : QI) : Bool :=
  localBit state.phase
    (RatBox.homographic (adjugate state.matrix) input)

/-- Pullback signs preserve the local discriminator just as they preserve the
two semantic child predicates. -/
theorem inputLocalBit_eq_of_inputForms_sameSigns
    (state : RawParser.State) (left right : QI)
    (leftDenominator :
      (adjugate state.matrix).c * left +
        (adjugate state.matrix).d ≠ 0)
    (rightDenominator :
      (adjugate state.matrix).c * right +
        (adjugate state.matrix).d ≠ 0)
    (sameSigns : ∀ form ∈ inputForms state,
      0 < form.eval left * form.eval right) :
    inputLocalBit state left = inputLocalBit state right := by
  apply localBit_eq_of_localForms_sameSigns
  intro form member
  have inputMember : pullbackForm (adjugate state.matrix) form ∈
      inputForms state := by
    rw [inputForms_eq_map_pullback]
    exact List.mem_map.mpr ⟨form, member, rfl⟩
  have inputSign := sameSigns
    (pullbackForm (adjugate state.matrix) form) inputMember
  rw [eval_pullbackForm (adjugate state.matrix) form left leftDenominator,
    eval_pullbackForm (adjugate state.matrix) form right rightDenominator]
    at inputSign
  have scalePositive : 0 <
      normSq ((adjugate state.matrix).c * left +
          (adjugate state.matrix).d) *
        normSq ((adjugate state.matrix).c * right +
          (adjugate state.matrix).d) :=
    mul_pos (normSq_pos leftDenominator) (normSq_pos rightDenominator)
  have rearranged : 0 <
      (form.eval (RatBox.homographic (adjugate state.matrix) left) *
        form.eval (RatBox.homographic (adjugate state.matrix) right)) *
      (normSq ((adjugate state.matrix).c * left +
          (adjugate state.matrix).d) *
        normSq ((adjugate state.matrix).c * right +
          (adjugate state.matrix).d)) := by
    nlinarith
  nlinarith

/-- Pullback by the inverse decoder preserves the closed sign stratum just as
it preserves an open sign cell.  Positive denominator norms preserve strict
products, and cannot turn a nonzero form value into an exact zero. -/
theorem inputLocalBit_eq_of_inputDecisionForms_sameSignOrBothZero
    (state : RawParser.State) (left right : QI)
    (leftDenominator :
      (adjugate state.matrix).c * left +
        (adjugate state.matrix).d ≠ 0)
    (rightDenominator :
      (adjugate state.matrix).c * right +
        (adjugate state.matrix).d ≠ 0)
    (sameSigns : ∀ form ∈ inputDecisionForms state,
      SameSignOrBothZero (form.eval left) (form.eval right)) :
    inputLocalBit state left = inputLocalBit state right := by
  apply localBit_eq_of_localDecisionForms_sameSignOrBothZero
  intro form member
  have inputMember : pullbackForm (adjugate state.matrix) form ∈
      inputDecisionForms state := by
    exact List.mem_map.mpr ⟨form, member, rfl⟩
  have inputSign := sameSigns
    (pullbackForm (adjugate state.matrix) form) inputMember
  rw [eval_pullbackForm (adjugate state.matrix) form left leftDenominator,
    eval_pullbackForm (adjugate state.matrix) form right rightDenominator]
    at inputSign
  rcases inputSign with strict | ⟨leftZero, rightZero⟩
  · left
    have scalePositive : 0 <
        normSq ((adjugate state.matrix).c * left +
            (adjugate state.matrix).d) *
          normSq ((adjugate state.matrix).c * right +
            (adjugate state.matrix).d) :=
      mul_pos (normSq_pos leftDenominator) (normSq_pos rightDenominator)
    have rearranged : 0 <
        (form.eval (RatBox.homographic (adjugate state.matrix) left) *
          form.eval (RatBox.homographic (adjugate state.matrix) right)) *
        (normSq ((adjugate state.matrix).c * left +
            (adjugate state.matrix).d) *
          normSq ((adjugate state.matrix).c * right +
            (adjugate state.matrix).d)) := by
      nlinarith
    nlinarith
  · right
    constructor
    · exact (mul_eq_zero.mp leftZero).resolve_left
        (normSq_pos leftDenominator).ne'
    · exact (mul_eq_zero.mp rightZero).resolve_left
        (normSq_pos rightDenominator).ne'

/-- The complete lookahead input plan remains sufficient for current-bit
stability. -/
theorem inputLocalBit_eq_of_inputForms_sameSignOrBothZero
    (state : RawParser.State) (left right : QI)
    (leftDenominator :
      (adjugate state.matrix).c * left +
        (adjugate state.matrix).d ≠ 0)
    (rightDenominator :
      (adjugate state.matrix).c * right +
        (adjugate state.matrix).d ≠ 0)
    (sameSigns : ∀ form ∈ inputForms state,
      SameSignOrBothZero (form.eval left) (form.eval right)) :
    inputLocalBit state left = inputLocalBit state right := by
  apply localBit_eq_of_localForms_sameSignOrBothZero
  intro form member
  have inputMember : pullbackForm (adjugate state.matrix) form ∈
      inputForms state := by
    rw [inputForms_eq_map_pullback]
    exact List.mem_map.mpr ⟨form, member, rfl⟩
  have inputSign := sameSigns
    (pullbackForm (adjugate state.matrix) form) inputMember
  rw [eval_pullbackForm (adjugate state.matrix) form left leftDenominator,
    eval_pullbackForm (adjugate state.matrix) form right rightDenominator]
    at inputSign
  rcases inputSign with strict | ⟨leftZero, rightZero⟩
  · left
    have scalePositive : 0 <
        normSq ((adjugate state.matrix).c * left +
            (adjugate state.matrix).d) *
          normSq ((adjugate state.matrix).c * right +
            (adjugate state.matrix).d) :=
      mul_pos (normSq_pos leftDenominator) (normSq_pos rightDenominator)
    have rearranged : 0 <
        (form.eval (RatBox.homographic (adjugate state.matrix) left) *
          form.eval (RatBox.homographic (adjugate state.matrix) right)) *
        (normSq ((adjugate state.matrix).c * left +
            (adjugate state.matrix).d) *
          normSq ((adjugate state.matrix).c * right +
            (adjugate state.matrix).d)) := by
      nlinarith
    nlinarith
  · right
    constructor
    · exact (mul_eq_zero.mp leftZero).resolve_left
        (normSq_pos leftDenominator).ne'
    · exact (mul_eq_zero.mp rightZero).resolve_left
        (normSq_pos rightDenominator).ne'

/-- An admissible original-coordinate child agrees with the directly computed
local discriminator. -/
theorem inputAdvance_bit_eq_inputLocalBit
    (state : RawParser.State) (input : QI) (bit : Bool)
    (inverseDenominator :
      (adjugate state.matrix).c * input +
        (adjugate state.matrix).d ≠ 0)
    (holds : (inputAdvanceFormula state bit).Holds input) :
    bit = inputLocalBit state input := by
  apply canAdvanceAt_bit_eq_localBit state
    (RatBox.homographic (adjugate state.matrix) input) bit
  exact (inputAdvanceFormula_iff state bit input inverseDenominator).1 holds

/-- Two admissible children on the same closed local sign stratum have the
same bit.  Unlike the open-cell theorem, this permits a retained source form
to remain exact equality at both points. -/
theorem inputAdvance_bits_eq_of_inputForms_sameSignOrBothZero
    (state : RawParser.State) (leftPoint rightPoint : QI)
    (leftDenominator :
      (adjugate state.matrix).c * leftPoint +
        (adjugate state.matrix).d ≠ 0)
    (rightDenominator :
      (adjugate state.matrix).c * rightPoint +
        (adjugate state.matrix).d ≠ 0)
    {leftBit rightBit : Bool}
    (leftHolds : (inputAdvanceFormula state leftBit).Holds leftPoint)
    (rightHolds : (inputAdvanceFormula state rightBit).Holds rightPoint)
    (sameSigns : ∀ form ∈ inputForms state,
      SameSignOrBothZero (form.eval leftPoint) (form.eval rightPoint)) :
    leftBit = rightBit := by
  calc
    leftBit = inputLocalBit state leftPoint :=
      inputAdvance_bit_eq_inputLocalBit state leftPoint leftBit
        leftDenominator leftHolds
    _ = inputLocalBit state rightPoint :=
      inputLocalBit_eq_of_inputForms_sameSignOrBothZero state leftPoint
        rightPoint leftDenominator rightDenominator sameSigns
    _ = rightBit :=
      (inputAdvance_bit_eq_inputLocalBit state rightPoint rightBit
        rightDenominator rightHolds).symm

/-- Two admissible children need agree only on the comparison forms read by
the current discriminator; lookahead owner walls are irrelevant to this bit. -/
theorem inputAdvance_bits_eq_of_inputDecisionForms_sameSignOrBothZero
    (state : RawParser.State) (leftPoint rightPoint : QI)
    (leftDenominator :
      (adjugate state.matrix).c * leftPoint +
        (adjugate state.matrix).d ≠ 0)
    (rightDenominator :
      (adjugate state.matrix).c * rightPoint +
        (adjugate state.matrix).d ≠ 0)
    {leftBit rightBit : Bool}
    (leftHolds : (inputAdvanceFormula state leftBit).Holds leftPoint)
    (rightHolds : (inputAdvanceFormula state rightBit).Holds rightPoint)
    (sameSigns : ∀ form ∈ inputDecisionForms state,
      SameSignOrBothZero (form.eval leftPoint) (form.eval rightPoint)) :
    leftBit = rightBit := by
  calc
    leftBit = inputLocalBit state leftPoint :=
      inputAdvance_bit_eq_inputLocalBit state leftPoint leftBit
        leftDenominator leftHolds
    _ = inputLocalBit state rightPoint :=
      inputLocalBit_eq_of_inputDecisionForms_sameSignOrBothZero state
        leftPoint rightPoint leftDenominator rightDenominator sameSigns
    _ = rightBit :=
      (inputAdvance_bit_eq_inputLocalBit state rightPoint rightBit
        rightDenominator rightHolds).symm

/-- A strict planned box computes the only possible bit at every admissible
point in the box.  No represented rational reference point is involved. -/
theorem inputAdvance_bit_eq_inputLocalBit_center_of_inputPlan_strictSigns
    (state : RawParser.State) (box : RatBox)
    (strictSigns : ∀ source ∈ inputPlan state,
      strictSignCheck source.form box = true)
    (centerDenominator :
      (adjugate state.matrix).c * box.center +
        (adjugate state.matrix).d ≠ 0)
    {input : QI} (inside : box.Contains input)
    (inputDenominator :
      (adjugate state.matrix).c * input +
        (adjugate state.matrix).d ≠ 0)
    {bit : Bool} (holds : (inputAdvanceFormula state bit).Holds input) :
    bit = inputLocalBit state box.center := by
  have selected := inputAdvance_bit_eq_inputLocalBit state input bit
    inputDenominator holds
  rw [selected]
  apply inputLocalBit_eq_of_inputForms_sameSigns state input box.center
    inputDenominator centerDenominator
  intro form member
  rw [inputForms] at member
  rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
  have same := eval_center_mul_pos_of_strictSignCheck source.form
    (strictSigns source sourceMember) inside
  simpa only [_root_.mul_comm] using same

/-- Executable sample-free result of a strict local branch cell. -/
structure StrictCellDecision (state : RawParser.State) (box : RatBox) where
  bit : Bool
  selects : ∀ {input : QI}, box.Contains input →
    (adjugate state.matrix).c * input +
        (adjugate state.matrix).d ≠ 0 →
    ∀ {other : Bool}, (inputAdvanceFormula state other).Holds input →
      other = bit

/-- Read the strict cell at its rational center and certify that all admissible
children in the cell carry that same bit. -/
def decideStrictCell
    (state : RawParser.State) (box : RatBox)
    (strictSigns : ∀ source ∈ inputPlan state,
      strictSignCheck source.form box = true)
    (centerDenominator :
      (adjugate state.matrix).c * box.center +
        (adjugate state.matrix).d ≠ 0) :
    StrictCellDecision state box where
  bit := inputLocalBit state box.center
  selects := by
    intro input inside inputDenominator other holds
    exact inputAdvance_bit_eq_inputLocalBit_center_of_inputPlan_strictSigns
      state box strictSigns centerDenominator inside inputDenominator holds

/-- Opposite child predicates cannot hold at two points that have the same
strict sign for every comparison in the local branch plan.  Historical
constraints occur in both child states and play no role in this finite case
analysis. -/
theorem not_canAdvanceAt_false_true_of_localForms_sameSigns
    (state : RawParser.State) (left right : QI)
    (falseHolds : CanAdvanceAt state false left)
    (trueHolds : CanAdvanceAt state true right)
    (sameSigns : ∀ form ∈ localForms state.phase,
      0 < form.eval left * form.eval right) : False := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      have lower := falseHolds.2
      have upper := trueHolds.2
      have sign := sameSigns
        (CCLParserGeometry.affineNormComparisonForm 2) (by simp)
      simp only [CCLParserGeometry.eval_affineNormComparisonForm] at sign
      change normSq left < 2 at lower
      change (2 : ℚ) ^ 1 ≤ normSq right at upper
      norm_num at upper
      nlinarith
  | highUnary count =>
      have upper := falseHolds.2.1.2
      have lower := trueHolds.2
      have sign := sameSigns
        (CCLParserGeometry.affineNormComparisonForm
          ((2 : ℚ) ^ (count + 1))) (by simp)
      simp only [CCLParserGeometry.eval_affineNormComparisonForm] at sign
      change normSq left < (2 : ℚ) ^ (count + 1) at upper
      change (2 : ℚ) ^ (count + 1) ≤ normSq right at lower
      nlinarith
  | lowUnary count =>
      cases count with
      | zero =>
          have lower := falseHolds.2.1.1
          have upper := trueHolds.2
          have sign := sameSigns
            (CCLParserGeometry.affineNormComparisonForm 1) (by simp)
          simp only [CCLParserGeometry.eval_affineNormComparisonForm] at sign
          simp [RawParser.step, RawParser.activeHolds] at lower upper
          nlinarith
      | succ count =>
          have lower := falseHolds.2.1.1
          have upper := trueHolds.2
          have sign := sameSigns
            (CCLParserGeometry.affineNormComparisonForm
              (1 / (2 : ℚ) ^ (count + 1))) (by simp)
          simp only [CCLParserGeometry.eval_affineNormComparisonForm] at sign
          change 1 ≤ (2 : ℚ) ^ (count + 1) * normSq left at lower
          change (2 : ℚ) ^ (count + 1) * normSq right < 1 at upper
          have powerPositive : 0 < (2 : ℚ) ^ (count + 1) :=
            pow_pos (by norm_num) _
          have leftNonnegative :
              0 ≤ normSq left - 1 / (2 : ℚ) ^ (count + 1) := by
            rw [sub_nonneg]
            apply (div_le_iff₀ powerPositive).2
            nlinarith
          have rightNegative :
              normSq right - 1 / (2 : ℚ) ^ (count + 1) < 0 := by
            rw [sub_neg]
            apply (lt_div_iff₀ powerPositive).2
            nlinarith
          exact (not_lt_of_ge
            (mul_nonpos_of_nonneg_of_nonpos leftNonnegative
              rightNegative.le)) sign
  | loopUnary count =>
      have upper := falseHolds.2.1.2
      have lower := trueHolds.2
      have sign := sameSigns
        (CCLParserGeometry.affineNormComparisonForm
          ((2 : ℚ) ^ (count + 1))) (by simp)
      simp only [CCLParserGeometry.eval_affineNormComparisonForm] at sign
      change normSq left ≤ (2 : ℚ) ^ (count + 1) at upper
      change (2 : ℚ) ^ (count + 1) < normSq right at lower
      nlinarith
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          rcases falseHolds.2 with
            ⟨_, falseSector, falseMember, falseSectorHolds⟩
          rcases trueHolds.2 with
            ⟨_, trueSector, trueMember, trueSectorHolds⟩
          have realLow := sameSigns
            (realComparisonForm
              (CCLParserGeometry.normalizedMatrix kind exponent
                RawParser.identityMatrix) (-1 / 2)) (by simp)
          have imagHigh := sameSigns
            (imagComparisonForm
              (CCLParserGeometry.normalizedMatrix kind exponent
                RawParser.identityMatrix) (1 / 2)) (by simp)
          have imagLow := sameSigns
            (imagComparisonForm
              (CCLParserGeometry.normalizedMatrix kind exponent
                RawParser.identityMatrix) (-1 / 2)) (by simp)
          simp only [eval_normalizedRealComparisonForm] at realLow
          simp only [eval_normalizedImagComparisonForm] at imagHigh imagLow
          simp only [RawParser.sectorCandidates_one_false, List.mem_cons,
            List.not_mem_nil, or_false] at falseMember
          simp only [RawParser.sectorCandidates_one_true, List.mem_cons,
            List.not_mem_nil, or_false] at trueMember
          rcases falseMember with rfl | rfl | rfl | rfl <;>
            rcases trueMember with rfl | rfl | rfl | rfl <;>
            simp only [Sector.Holds] at falseSectorHolds trueSectorHolds <;>
            nlinarith
      | one first =>
          cases first with
          | false =>
              rcases falseHolds.2 with
                ⟨_, falseSector, falseMember, falseSectorHolds⟩
              rcases trueHolds.2 with
                ⟨_, trueSector, trueMember, trueSectorHolds⟩
              have realHigh := sameSigns
                (realComparisonForm
                  (CCLParserGeometry.normalizedMatrix kind exponent
                    RawParser.identityMatrix) (1 / 2)) (by simp)
              simp only [eval_normalizedRealComparisonForm] at realHigh
              simp only [RawParser.sectorCandidates_two_false_false,
                List.mem_cons, List.not_mem_nil, or_false] at falseMember
              simp only [RawParser.sectorCandidates_two_false_true,
                List.mem_cons, List.not_mem_nil, or_false] at trueMember
              rcases falseMember with rfl | rfl <;>
                rcases trueMember with rfl | rfl <;>
                simp only [Sector.Holds] at falseSectorHolds trueSectorHolds <;>
                nlinarith
          | true =>
              rcases falseHolds.2 with
                ⟨_, falseSector, falseMember, falseSectorHolds⟩
              rcases trueHolds.2 with
                ⟨_, trueSector, trueMember, trueSectorHolds⟩
              have realLow := sameSigns
                (realComparisonForm
                  (CCLParserGeometry.normalizedMatrix kind exponent
                    RawParser.identityMatrix) (-1 / 2)) (by simp)
              simp only [eval_normalizedRealComparisonForm] at realLow
              simp only [RawParser.sectorCandidates_two_true_false,
                List.mem_cons, List.not_mem_nil, or_false] at falseMember
              simp only [RawParser.sectorCandidates_two_true_true,
                List.mem_cons, List.not_mem_nil, or_false] at trueMember
              rcases falseMember with rfl | rfl <;>
                rcases trueMember with rfl | rfl <;>
                simp only [Sector.Holds] at falseSectorHolds trueSectorHolds <;>
                nlinarith
      | two first second =>
          cases first <;> cases second
          · have falseSector := falseHolds.1.2
            have trueSector := trueHolds.1.2
            have imagHigh := sameSigns
              (imagComparisonForm
                (CCLParserGeometry.normalizedMatrix kind exponent
                  RawParser.identityMatrix) (1 / 2)) (by simp)
            simp only [eval_normalizedImagComparisonForm] at imagHigh
            simp only [RawParser.sectorOfBits, Sector.Holds] at falseSector
            simp only [RawParser.sectorOfBits, Sector.Holds] at trueSector
            nlinarith
          · have falseSector := falseHolds.1.2
            have trueSector := trueHolds.1.2
            have realLow := sameSigns
              (realComparisonForm
                (CCLParserGeometry.normalizedMatrix kind exponent
                  RawParser.identityMatrix) (-1 / 2)) (by simp)
            simp only [eval_normalizedRealComparisonForm] at realLow
            simp only [RawParser.sectorOfBits, Sector.Holds] at falseSector
            simp only [RawParser.sectorOfBits, Sector.Holds] at trueSector
            nlinarith
          · have falseSector := falseHolds.1.2
            have trueSector := trueHolds.1.2
            have imagLow := sameSigns
              (imagComparisonForm
                (CCLParserGeometry.normalizedMatrix kind exponent
                  RawParser.identityMatrix) (-1 / 2)) (by simp)
            simp only [eval_normalizedImagComparisonForm] at imagLow
            simp only [RawParser.sectorOfBits, Sector.Holds] at falseSector
            simp only [RawParser.sectorOfBits, Sector.Holds] at trueSector
            nlinarith
          · have falseSector := falseHolds.1.2
            have trueSector := trueHolds.1.2
            have realHigh := sameSigns
              (realComparisonForm
                (CCLParserGeometry.normalizedMatrix kind exponent
                  RawParser.identityMatrix) (1 / 2)) (by simp)
            simp only [eval_normalizedRealComparisonForm] at realHigh
            simp only [RawParser.sectorOfBits, Sector.Holds] at falseSector
            simp only [RawParser.sectorOfBits, Sector.Holds] at trueSector
            nlinarith

theorem canAdvanceAt_eq_of_localForms_sameSigns
    (state : RawParser.State) (leftPoint rightPoint : QI)
    {leftBit rightBit : Bool}
    (leftHolds : CanAdvanceAt state leftBit leftPoint)
    (rightHolds : CanAdvanceAt state rightBit rightPoint)
    (sameSigns : ∀ form ∈ localForms state.phase,
      0 < form.eval leftPoint * form.eval rightPoint) :
    leftBit = rightBit := by
  cases leftBit <;> cases rightBit
  · rfl
  · exact (not_canAdvanceAt_false_true_of_localForms_sameSigns state
      leftPoint rightPoint leftHolds rightHolds sameSigns).elim
  · have reversedSigns : ∀ form ∈ localForms state.phase,
        0 < form.eval rightPoint * form.eval leftPoint := by
      intro form member
      have sign := sameSigns form member
      nlinarith
    exact (not_canAdvanceAt_false_true_of_localForms_sameSigns state
      rightPoint leftPoint rightHolds leftHolds reversedSigns).elim
  · rfl

/-- Pulling the plan through the inverse decoder preserves the cross-point
child uniqueness theorem.  The two positive denominator norms cancel from
the same-sign products constructively. -/
theorem inputAdvance_bits_eq_of_inputForms_sameSigns
    (state : RawParser.State) (leftPoint rightPoint : QI)
    (leftDenominator :
      (adjugate state.matrix).c * leftPoint +
        (adjugate state.matrix).d ≠ 0)
    (rightDenominator :
      (adjugate state.matrix).c * rightPoint +
        (adjugate state.matrix).d ≠ 0)
    {leftBit rightBit : Bool}
    (leftHolds : (inputAdvanceFormula state leftBit).Holds leftPoint)
    (rightHolds : (inputAdvanceFormula state rightBit).Holds rightPoint)
    (sameSigns : ∀ form ∈ inputForms state,
      0 < form.eval leftPoint * form.eval rightPoint) :
    leftBit = rightBit := by
  apply canAdvanceAt_eq_of_localForms_sameSigns state
    (RatBox.homographic (adjugate state.matrix) leftPoint)
    (RatBox.homographic (adjugate state.matrix) rightPoint)
  · exact (inputAdvanceFormula_iff state leftBit leftPoint
      leftDenominator).1 leftHolds
  · exact (inputAdvanceFormula_iff state rightBit rightPoint
      rightDenominator).1 rightHolds
  · intro form member
    have inputMember : pullbackForm (adjugate state.matrix) form ∈
        inputForms state := by
      rw [inputForms_eq_map_pullback]
      exact List.mem_map.mpr ⟨form, member, rfl⟩
    have inputSign := sameSigns
      (pullbackForm (adjugate state.matrix) form) inputMember
    rw [eval_pullbackForm (adjugate state.matrix) form leftPoint
        leftDenominator,
      eval_pullbackForm (adjugate state.matrix) form rightPoint
        rightDenominator] at inputSign
    have scalePositive : 0 <
        normSq ((adjugate state.matrix).c * leftPoint +
            (adjugate state.matrix).d) *
          normSq ((adjugate state.matrix).c * rightPoint +
            (adjugate state.matrix).d) :=
      mul_pos (normSq_pos leftDenominator) (normSq_pos rightDenominator)
    have rearranged : 0 <
        (form.eval (RatBox.homographic (adjugate state.matrix) leftPoint) *
          form.eval (RatBox.homographic (adjugate state.matrix) rightPoint)) *
        (normSq ((adjugate state.matrix).c * leftPoint +
            (adjugate state.matrix).d) *
          normSq ((adjugate state.matrix).c * rightPoint +
            (adjugate state.matrix).d)) := by
      nlinarith
    nlinarith

/-- Successful interval checks on every planned source provide the input-form
same-sign hypothesis automatically for any two points of the box. -/
theorem inputAdvance_bits_eq_of_inputPlan_strictSigns
    (state : RawParser.State) (box : RatBox)
    (strictSigns : ∀ source ∈ inputPlan state,
      strictSignCheck source.form box = true)
    {leftPoint rightPoint : QI}
    (leftInside : box.Contains leftPoint)
    (rightInside : box.Contains rightPoint)
    (leftDenominator :
      (adjugate state.matrix).c * leftPoint +
        (adjugate state.matrix).d ≠ 0)
    (rightDenominator :
      (adjugate state.matrix).c * rightPoint +
        (adjugate state.matrix).d ≠ 0)
    {leftBit rightBit : Bool}
    (leftHolds : (inputAdvanceFormula state leftBit).Holds leftPoint)
    (rightHolds : (inputAdvanceFormula state rightBit).Holds rightPoint) :
    leftBit = rightBit := by
  apply inputAdvance_bits_eq_of_inputForms_sameSigns state leftPoint rightPoint
    leftDenominator rightDenominator leftHolds rightHolds
  intro form member
  rw [inputForms] at member
  rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
  have leftSign := eval_center_mul_pos_of_strictSignCheck source.form
    (strictSigns source sourceMember) leftInside
  have rightSign := eval_center_mul_pos_of_strictSignCheck source.form
    (strictSigns source sourceMember) rightInside
  have centerNonzero : source.form.eval box.center ≠ 0 := by
    intro zero
    rw [zero] at leftSign
    norm_num at leftSign
  have centerSquarePositive :
      0 < source.form.eval box.center * source.form.eval box.center :=
    mul_self_pos.mpr centerNonzero
  have combined : 0 <
      (source.form.eval box.center * source.form.eval box.center) *
        (source.form.eval leftPoint * source.form.eval rightPoint) := by
    rw [← mul_mul_mul_comm]
    exact mul_pos leftSign rightSign
  exact pos_of_mul_pos_right combined centerSquarePositive.le

end CCLStrictChildSemantics
end FTA
