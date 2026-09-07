import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.RawParserSemantics

/-!
# Constructive one-bit raw-parser semantics

This module reduces semantic possibility of one more raw CCL bit to an
explicit predicate at the current affine tail.  The only nontrivial case is
the third sector bit: completing that bit subtracts the selected sector
representative and changes to a reciprocal coordinate.  All decisions and
inverse calculations below are finite and rational.
-/

namespace CCL.ParserStep

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Sector := CCL.Sectors.Sector
abbrev Mat2 := CCL.GaussianProjective.Mat2

open RFAP.ConstructiveGaussian.Gaussian
open CCL.Sectors
open CCL.RawParser
open CCL.RawParserSemantics

/-- A completed radial bracket normalizes into the common closed annulus. -/
theorem normalizedValue_band_of_radialBracket
    (kind : BlockKind) (exponent : Nat) (value : Gaussian)
    (radial : radialBracket kind exponent value) :
    Sector.Band (normalizedValue kind exponent value) := by
  have powerPositive : (0 : Coordinate) < (2 : Coordinate) ^ exponent :=
    RFAP.ConstructiveFraction.pow_pos_direct (by decide) exponent
  cases kind with
  | initialHigh =>
      rcases radial with ⟨lower, upper⟩
      have powerNonzero : natPow gamma exponent ≠ 0 :=
        natPow_ne_zero_direct gamma (by decide) exponent
      have normIdentity :
          normSq (normalizedValue .initialHigh exponent value) =
            normSq value / (2 : Coordinate) ^ exponent := by
        rw [normalizedValue, normSq_mul, inv_eq,
          normSq_inv _ powerNonzero,
          normSq_natPow, normSq_gamma]
        rfl
      rw [Sector.Band, normIdentity]
      constructor
      · apply (RFAP.ConstructiveFraction.le_div_iff_pos powerPositive).2
        simpa only [RFAP.ConstructiveFraction.one_mul] using lower
      · apply (RFAP.ConstructiveFraction.div_le_iff_pos powerPositive).2
        exact upper.le.trans_eq (by
          rw [pow_succ]
          ring1)
  | initialLow =>
      rcases radial with ⟨lower, upper⟩
      rw [Sector.Band, normalizedValue, normSq_mul, normSq_natPow,
        normSq_gamma]
      exact ⟨lower, upper.le⟩
  | loop =>
      rcases radial with ⟨lower, upper⟩
      have powerNonzero : natPow gamma exponent ≠ 0 :=
        natPow_ne_zero_direct gamma (by decide) exponent
      have normIdentity :
          normSq (normalizedValue .loop exponent value) =
            normSq value / (2 : Coordinate) ^ exponent := by
        rw [normalizedValue, normSq_mul, inv_eq,
          normSq_inv _ powerNonzero,
          normSq_natPow, normSq_gamma]
        rfl
      rw [Sector.Band, normIdentity]
      constructor
      · apply (RFAP.ConstructiveFraction.le_div_iff_pos powerPositive).2
        simpa only [RFAP.ConstructiveFraction.one_mul] using lower.le
      · apply (RFAP.ConstructiveFraction.div_le_iff_pos powerPositive).2
        exact upper.trans_eq (by
          rw [pow_succ]
          ring1)

/-- A completed block therefore supplies the annulus hypothesis of the
decoder's contraction theorem. -/
theorem normalizedValue_band_of_fullBlock
    (kind : BlockKind) (exponent : Nat) (sector : Sector)
    (value : Gaussian)
    (full : fullBlockHolds kind exponent sector value) :
    Sector.Band (normalizedValue kind exponent value) :=
  normalizedValue_band_of_radialBracket kind exponent value full.1

/-- A nonterminal completed sector has a reciprocal tail in the strict
outside region required by the loop parser. -/
theorem inverse_selected_loop_active
    (kind : BlockKind) (exponent : Nat) (sector : Sector)
    (value : Gaussian)
    (full : fullBlockHolds kind exponent sector value)
    (residual : normalizedValue kind exponent value - sector.rep ≠ 0) :
    activeHolds (.loopUnary 0)
      ((gamma * (normalizedValue kind exponent value - sector.rep))⁻¹) := by
  rw [activeHolds, pow_zero]
  exact CCL.Decoder.postInversion_norm_gt_one
    (normalizedValue_band_of_fullBlock kind exponent sector value full)
    sector full.2 residual

private theorem gamma_ne : gamma ≠ 0 := by decide

/-- Inverting the selected nonzero reciprocal tail recovers the normalized
residual. -/
theorem inverse_gamma_inverse_mul
    (residual : Gaussian) (residualNonzero : residual ≠ 0) :
    (gamma * (gamma * residual)⁻¹)⁻¹ = residual := by
  have productNonzero : gamma * residual ≠ 0 :=
    mul_ne_zero_direct gamma_ne residualNonzero
  have tailNonzero : (gamma * residual)⁻¹ ≠ 0 :=
    inv_ne_zero_direct productNonzero
  have gammaTailNonzero : gamma * (gamma * residual)⁻¹ ≠ 0 :=
    mul_ne_zero_direct gamma_ne tailNonzero
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    gammaTailNonzero
  calc
    (gamma * (gamma * residual)⁻¹)⁻¹ *
          (gamma * (gamma * residual)⁻¹) = 1 :=
      RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel _ gammaTailNonzero
    _ = residual * (gamma * (gamma * residual)⁻¹) := by
      calc
        1 = (gamma * residual) * (gamma * residual)⁻¹ :=
          (RFAP.CanonicalGaussian.Gaussian.mul_inv_cancel
            _ productNonzero).symm
        _ = residual * (gamma * (gamma * residual)⁻¹) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [mul_re, mul_im] <;>
            ring1

private theorem regularBlock_homographic_inverse
    (exponent : Nat) (sector : Sector) (value residual : Gaussian)
    (residualNonzero : residual ≠ 0)
    (decomposition :
      value = natPow gamma exponent * (sector.rep + residual)) :
    homographic (CCL.Decoder.regularBlock exponent sector)
        ((gamma * residual)⁻¹) = value := by
  let power := natPow gamma exponent
  let tail := (gamma * residual)⁻¹
  have inverseDenominator : (gamma * tail)⁻¹ = residual := by
    simpa only [tail] using inverse_gamma_inverse_mul residual residualNonzero
  have gammaResidualNonzero : gamma * residual ≠ 0 :=
    mul_ne_zero_direct gamma_ne residualNonzero
  have tailNonzero : tail ≠ 0 := inv_ne_zero_direct gammaResidualNonzero
  have denominatorNonzero : gamma * tail ≠ 0 :=
    mul_ne_zero_direct gamma_ne tailNonzero
  unfold homographic numerator denominator
  simp only [CCL.Decoder.regularBlock,
    RFAP.ConstructiveGaussian.Gaussian.add_zero]
  change (natPow gamma (exponent + 1) * sector.rep * tail + power) *
      (gamma * tail)⁻¹ = value
  rw [inverseDenominator, decomposition, natPow_succ]
  have cancellation : gamma * tail * residual = 1 := by
    calc
      gamma * tail * residual =
          (gamma * residual) * (gamma * residual)⁻¹ := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [tail, mul_re, mul_im] <;>
          ring1
      _ = 1 :=
        RFAP.CanonicalGaussian.Gaussian.mul_inv_cancel
          _ gammaResidualNonzero
  calc
    (power * gamma * sector.rep * tail + power) * residual =
        power * (sector.rep * (gamma * tail * residual) + residual) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [mul_re, mul_im, add_re, add_im] <;>
        ring1
    _ = power * (sector.rep + residual) := by
      rw [cancellation, RFAP.ConstructiveGaussian.Gaussian.mul_one]

private theorem lowBlock_homographic_inverse
    (exponent : Nat) (sector : Sector) (value residual : Gaussian)
    (residualNonzero : residual ≠ 0)
    (decomposition :
      natPow gamma exponent * value = sector.rep + residual) :
    homographic (CCL.Decoder.lowBlock exponent sector)
        ((gamma * residual)⁻¹) = value := by
  let power := natPow gamma exponent
  let tail := (gamma * residual)⁻¹
  have powerNonzero : power ≠ 0 :=
    natPow_ne_zero_direct gamma gamma_ne exponent
  have inverseGammaTail : (gamma * tail)⁻¹ = residual := by
    simpa only [tail] using inverse_gamma_inverse_mul residual residualNonzero
  have gammaResidualNonzero : gamma * residual ≠ 0 :=
    mul_ne_zero_direct gamma_ne residualNonzero
  have tailNonzero : tail ≠ 0 := inv_ne_zero_direct gammaResidualNonzero
  have gammaTailNonzero : gamma * tail ≠ 0 :=
    mul_ne_zero_direct gamma_ne tailNonzero
  have fullDenominatorNonzero :
      natPow gamma (exponent + 1) * tail ≠ 0 :=
    mul_ne_zero_direct
      (natPow_ne_zero_direct gamma gamma_ne (exponent + 1)) tailNonzero
  have residualCancellation : residual * (gamma * tail) = 1 := by
    calc
      residual * (gamma * tail) =
          (gamma * tail)⁻¹ * (gamma * tail) := by rw [inverseGammaTail]
      _ = 1 :=
        RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel _ gammaTailNonzero
  have inverseDenominator :
      (natPow gamma (exponent + 1) * tail)⁻¹ =
        residual * power⁻¹ := by
    apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
      fullDenominatorNonzero
    calc
      (natPow gamma (exponent + 1) * tail)⁻¹ *
          (natPow gamma (exponent + 1) * tail) = 1 :=
        RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel
          _ fullDenominatorNonzero
      _ = (residual * power⁻¹) *
          (natPow gamma (exponent + 1) * tail) := by
        rw [natPow_succ]
        have powerCancellation : power⁻¹ * power = 1 := by
          exact RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel
            power powerNonzero
        calc
          1 = (power⁻¹ * power) * (residual * (gamma * tail)) := by
            rw [powerCancellation, residualCancellation,
              RFAP.ConstructiveGaussian.Gaussian.one_mul]
          _ = (residual * power⁻¹) * (power * gamma * tail) := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [mul_re, mul_im] <;>
              ring1
  unfold homographic numerator denominator
  simp only [CCL.Decoder.lowBlock,
    RFAP.ConstructiveGaussian.Gaussian.add_zero]
  change (gamma * sector.rep * tail + 1) *
      (natPow gamma (exponent + 1) * tail)⁻¹ = value
  rw [inverseDenominator]
  have gammaTailResidual : gamma * tail * residual = 1 := by
    calc
      gamma * tail * residual = (gamma * tail) * (gamma * tail)⁻¹ := by
        rw [inverseGammaTail]
      _ = 1 :=
        RFAP.CanonicalGaussian.Gaussian.mul_inv_cancel _ gammaTailNonzero
  have powerCancellation : power⁻¹ * power = 1 := by
    exact RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel power powerNonzero
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne powerNonzero
  calc
    ((gamma * sector.rep * tail + 1) * (residual * power⁻¹)) *
          power =
        sector.rep * (gamma * tail * residual) *
            (power⁻¹ * power) + residual * (power⁻¹ * power) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [mul_re, mul_im, add_re, add_im, one_re, one_im] <;>
        ring1
    _ = sector.rep + residual := by
      rw [gammaTailResidual, powerCancellation,
        RFAP.ConstructiveGaussian.Gaussian.mul_one,
        RFAP.ConstructiveGaussian.Gaussian.mul_one]
      exact congrArg (fun item => sector.rep + item)
        (RFAP.ConstructiveGaussian.Gaussian.mul_one residual)
    _ = power * value := decomposition.symm
    _ = value * power := RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _

/-- The explicit reciprocal tail of a nonterminal completed block maps back
to its pre-normalization affine value. -/
theorem block_homographic_inverse
    (kind : BlockKind) (exponent : Nat) (sector : Sector)
    (value : Gaussian)
    (residualNonzero :
      normalizedValue kind exponent value - sector.rep ≠ 0) :
    homographic (blockMatrix kind exponent sector)
        ((gamma * (normalizedValue kind exponent value - sector.rep))⁻¹) =
      value := by
  cases kind with
  | initialHigh =>
      let residual := value * (natPow gamma exponent)⁻¹ - sector.rep
      apply regularBlock_homographic_inverse exponent sector value residual
        residualNonzero
      have powerNonzero :=
        natPow_ne_zero_direct gamma gamma_ne exponent
      have cancellation : (natPow gamma exponent)⁻¹ *
          natPow gamma exponent = 1 := by
        exact RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel
          (natPow gamma exponent) powerNonzero
      calc
        value = value * ((natPow gamma exponent)⁻¹ *
            natPow gamma exponent) := by
          rw [cancellation, RFAP.ConstructiveGaussian.Gaussian.mul_one]
        _ = natPow gamma exponent * (sector.rep + residual) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [residual, sub_re, sub_im,
              mul_re, mul_im, add_re, add_im] <;>
            ring1
  | initialLow =>
      let residual := natPow gamma exponent * value - sector.rep
      apply lowBlock_homographic_inverse exponent sector value residual
        residualNonzero
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [residual, sub_re, sub_im,
          mul_re, mul_im, add_re, add_im] <;>
        ring1
  | loop =>
      let residual := value * (natPow gamma exponent)⁻¹ - sector.rep
      apply regularBlock_homographic_inverse exponent sector value residual
        residualNonzero
      have powerNonzero :=
        natPow_ne_zero_direct gamma gamma_ne exponent
      have cancellation : (natPow gamma exponent)⁻¹ *
          natPow gamma exponent = 1 := by
        exact RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel
          (natPow gamma exponent) powerNonzero
      calc
        value = value * ((natPow gamma exponent)⁻¹ *
            natPow gamma exponent) := by
          rw [cancellation, RFAP.ConstructiveGaussian.Gaussian.mul_one]
        _ = natPow gamma exponent * (sector.rep + residual) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [residual, sub_re, sub_im,
              mul_re, mul_im, add_re, add_im] <;>
            ring1

/-- The explicit reciprocal tail lies in the affine chart of its completed
block. -/
theorem block_inverse_denominator_ne
    (kind : BlockKind) (exponent : Nat) (sector : Sector)
    (value : Gaussian)
    (residualNonzero :
      normalizedValue kind exponent value - sector.rep ≠ 0) :
    denominator (blockMatrix kind exponent sector)
      ((gamma * (normalizedValue kind exponent value - sector.rep))⁻¹) ≠
        0 := by
  let tail :=
    (gamma * (normalizedValue kind exponent value - sector.rep))⁻¹
  have tailNonzero : tail ≠ 0 :=
    inv_ne_zero_direct (mul_ne_zero_direct gamma_ne residualNonzero)
  cases kind with
  | initialHigh =>
      change gamma * tail + 0 ≠ 0
      rw [RFAP.ConstructiveGaussian.Gaussian.add_zero]
      exact mul_ne_zero_direct gamma_ne tailNonzero
  | initialLow =>
      change natPow gamma (exponent + 1) * tail + 0 ≠ 0
      rw [RFAP.ConstructiveGaussian.Gaussian.add_zero]
      exact mul_ne_zero_direct
        (natPow_ne_zero_direct gamma gamma_ne (exponent + 1)) tailNonzero
  | loop =>
      change gamma * tail + 0 ≠ 0
      rw [RFAP.ConstructiveGaussian.Gaussian.add_zero]
      exact mul_ne_zero_direct gamma_ne tailNonzero

/-- A completed block has a nonzero affine denominator only at a nonzero
tail. -/
theorem tail_ne_of_block_denominator
    (kind : BlockKind) (exponent : Nat) (sector : Sector)
    (tail : Gaussian)
    (denominatorNonzero :
      denominator (blockMatrix kind exponent sector) tail ≠ 0) :
    tail ≠ 0 := by
  intro tailZero
  subst tail
  apply denominatorNonzero
  cases kind <;>
    simp [denominator, blockMatrix, CCL.Decoder.regularBlock,
      CCL.Decoder.lowBlock]

/-- A completed block followed by an affine tail normalizes to the selected
representative plus its reciprocal correction. -/
theorem normalizedValue_block_homographic
    (kind : BlockKind) (exponent : Nat) (sector : Sector)
    (tail : Gaussian)
    (denominatorNonzero :
      denominator (blockMatrix kind exponent sector) tail ≠ 0) :
    normalizedValue kind exponent
        (homographic (blockMatrix kind exponent sector) tail) =
      sector.rep + (gamma * tail)⁻¹ := by
  have tailNonzero := tail_ne_of_block_denominator kind exponent sector tail
    denominatorNonzero
  have gammaTailNonzero : gamma * tail ≠ 0 :=
    mul_ne_zero_direct gamma_ne tailNonzero
  let power := natPow gamma exponent
  have powerNonzero : power ≠ 0 :=
    natPow_ne_zero_direct gamma gamma_ne exponent
  have powerCancellation : power * power⁻¹ = 1 := by
    exact RFAP.CanonicalGaussian.Gaussian.mul_inv_cancel power powerNonzero
  have denominatorCancellation :
      gamma * tail * (gamma * tail)⁻¹ = 1 := by
    exact RFAP.CanonicalGaussian.Gaussian.mul_inv_cancel _ gammaTailNonzero
  cases kind with
  | initialHigh | loop =>
      simp only [normalizedValue, blockMatrix,
        CCL.Decoder.regularBlock, homographic, numerator,
        denominator, RFAP.ConstructiveGaussian.Gaussian.add_zero, natPow_succ]
      change ((power * gamma * sector.rep * tail + power) *
          (gamma * tail)⁻¹) * power⁻¹ =
        sector.rep + (gamma * tail)⁻¹
      calc
        ((power * gamma * sector.rep * tail + power) *
            (gamma * tail)⁻¹) * power⁻¹ =
          sector.rep * (gamma * tail * (gamma * tail)⁻¹) *
              (power * power⁻¹) +
            (gamma * tail)⁻¹ * (power * power⁻¹) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [mul_re, mul_im, add_re, add_im] <;>
            ring1
        _ = sector.rep + (gamma * tail)⁻¹ := by
          rw [denominatorCancellation, powerCancellation,
            RFAP.ConstructiveGaussian.Gaussian.mul_one sector.rep,
            RFAP.ConstructiveGaussian.Gaussian.mul_one (gamma * tail)⁻¹]
          exact congrArg (fun item => item + (gamma * tail)⁻¹)
            (RFAP.ConstructiveGaussian.Gaussian.mul_one sector.rep)
  | initialLow =>
      have fullDenominatorNonzero : power * (gamma * tail) ≠ 0 :=
        mul_ne_zero_direct powerNonzero gammaTailNonzero
      have inverseDenominator :
          (power * (gamma * tail))⁻¹ =
            (gamma * tail)⁻¹ * power⁻¹ := by
        apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
          fullDenominatorNonzero
        calc
          (power * (gamma * tail))⁻¹ *
                (power * (gamma * tail)) = 1 := by
            exact RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel
              _ fullDenominatorNonzero
          _ = ((gamma * tail)⁻¹ * power⁻¹) *
                (power * (gamma * tail)) := by
            have inversePowerCancellation : power⁻¹ * power = 1 := by
              exact RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel
                power powerNonzero
            have inverseTailCancellation :
                (gamma * tail)⁻¹ * (gamma * tail) = 1 := by
              exact RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel
                _ gammaTailNonzero
            calc
              1 = (gamma * tail)⁻¹ * (gamma * tail) :=
                inverseTailCancellation.symm
              _ = ((gamma * tail)⁻¹ * 1) * (gamma * tail) := by
                rw [RFAP.ConstructiveGaussian.Gaussian.mul_one]
              _ = ((gamma * tail)⁻¹ * (power⁻¹ * power)) *
                    (gamma * tail) := by rw [inversePowerCancellation]
              _ = ((gamma * tail)⁻¹ * power⁻¹) *
                    (power * (gamma * tail)) := by
                apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                  simp only [mul_re, mul_im] <;>
                  ring1
      simp only [normalizedValue, blockMatrix,
        CCL.Decoder.lowBlock, homographic, numerator, denominator,
        RFAP.ConstructiveGaussian.Gaussian.add_zero]
      rw [show natPow gamma (exponent + 1) * tail =
          power * (gamma * tail) by
        rw [natPow_succ]
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [mul_re, mul_im] <;>
          ring1,
        inverseDenominator]
      change power * ((gamma * sector.rep * tail + 1) *
          ((gamma * tail)⁻¹ * power⁻¹)) =
        sector.rep + (gamma * tail)⁻¹
      calc
        power * ((gamma * sector.rep * tail + 1) *
            ((gamma * tail)⁻¹ * power⁻¹)) =
          sector.rep * (gamma * tail * (gamma * tail)⁻¹) *
              (power * power⁻¹) +
            (gamma * tail)⁻¹ * (power * power⁻¹) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [mul_re, mul_im, add_re, add_im, one_re, one_im] <;>
            ring1
        _ = sector.rep + (gamma * tail)⁻¹ := by
          rw [denominatorCancellation, powerCancellation,
            RFAP.ConstructiveGaussian.Gaussian.mul_one sector.rep,
            RFAP.ConstructiveGaussian.Gaussian.mul_one (gamma * tail)⁻¹]
          exact congrArg (fun item => item + (gamma * tail)⁻¹)
            (RFAP.ConstructiveGaussian.Gaussian.mul_one sector.rep)

/-- Finite predicate for a proposed next bit at the unique current affine
tail.  The third sector bit includes the nonzero residual needed to enter the
next affine chart. -/
def CanAdvanceAt (state : State) (bit : Bool) (before : Gaussian) : Prop :=
  match state.phase with
  | .sector kind exponent (.two first second) =>
      let sector := sectorOfBits first second bit
      fullBlockHolds kind exponent sector before ∧
        normalizedValue kind exponent before - sector.rep ≠ 0
  | _ => (step state bit).Holds before

instance canAdvanceAtDecidable
    (state : State) (bit : Bool) (before : Gaussian) :
    Decidable (CanAdvanceAt state bit before) := by
  unfold CanAdvanceAt
  split
  · infer_instance
  · exact decidable_of_iff
      ((step state bit).holdsBool before = true)
      (State.holdsBool_eq_true (step state bit) before)

/-- The two local child predicates are disjoint even without a represented
input: the weak/strict boundary convention assigns every equality to one
side. -/
theorem not_canAdvanceAt_false_and_true
    (state : State) (before : Gaussian) :
    ¬(CanAdvanceAt state false before ∧
      CanAdvanceAt state true before) := by
  rintro ⟨falseHolds, trueHolds⟩
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      have low := falseHolds.2
      have high := trueHolds.2
      change normSq before < 2 at low
      change (2 : Coordinate) ^ 1 ≤ normSq before at high
      rw [pow_one] at high
      exact (not_lt_of_ge high) low
  | highUnary count =>
      have upper := falseHolds.2.1.2
      have lower := trueHolds.2
      exact (not_lt_of_ge lower) upper
  | lowUnary count =>
      have lower := falseHolds.2.1.1
      have upper := trueHolds.2
      exact (not_lt_of_ge lower) upper
  | loopUnary count =>
      have upper := falseHolds.2.1.2
      have lower := trueHolds.2
      exact (not_lt_of_ge upper) lower
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
          have falsePrefix : isWordPrefix [false] falseSector.code = true :=
            (List.mem_filter.mp falseMember).2
          have truePrefix : isWordPrefix [true] falseSector.code = true :=
            (List.mem_filter.mp trueMember).2
          cases falseSector <;> simp_all
      | one first =>
          rcases falseHolds.2 with
            ⟨_, falseSector, falseMember, falseSectorHolds⟩
          rcases trueHolds.2 with
            ⟨_, trueSector, trueMember, trueSectorHolds⟩
          have sectorEqual := Sector.holds_unique falseSectorHolds
            trueSectorHolds
          subst trueSector
          have falsePrefix :
              isWordPrefix [first, false] falseSector.code = true :=
            (List.mem_filter.mp falseMember).2
          have truePrefix :
              isWordPrefix [first, true] falseSector.code = true :=
            (List.mem_filter.mp trueMember).2
          cases first <;> cases falseSector <;> simp_all
      | two first second =>
          have sectorEqual := Sector.holds_unique falseHolds.1.2
            trueHolds.1.2
          cases first <;> cases second <;>
            simp [sectorOfBits] at sectorEqual

/-- Any two locally admissible Boolean children carry the same bit. -/
theorem canAdvanceAt_unique
    {state : State} {before : Gaussian} {left right : Bool}
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

theorem gaussian_eq_of_sub_eq_zero
    {left right : Gaussian} (difference : left - right = 0) :
    left = right := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · have realDifference := congrArg
        RFAP.ConstructiveGaussian.Gaussian.re difference
    change left.re - right.re = 0 at realDifference
    exact sub_eq_zero.mp realDifference
  · have imaginaryDifference := congrArg
        RFAP.ConstructiveGaussian.Gaussian.im difference
    change left.im - right.im = 0 at imaginaryDifference
    exact sub_eq_zero.mp imaginaryDifference

/-- Semantic possibility of a child is exactly the explicit local rational
predicate at the unique represented tail. -/
theorem canStep_iff_canAdvanceAt
    (state : State) (input before : Gaussian)
    (determinantNonzero :
      CCL.Chordal.Mat2.det state.matrix ≠ 0)
    (beforeRepresents : Represents state input before)
    (bit : Bool) :
    CanStep state input bit ↔ CanAdvanceAt state bit before := by
  constructor
  · rintro ⟨after, afterRepresents⟩
    have previousRepresents := step_represents_previous state bit input after
      afterRepresents
    have previousEqual := Represents.tail_unique determinantNonzero
      beforeRepresents previousRepresents
    rcases state with ⟨phase, matrix, history⟩
    cases phase with
    | initial =>
        simp only [previousTail] at previousEqual
        subst before
        simpa [CanAdvanceAt] using afterRepresents.2.2
    | highUnary count =>
        simp only [previousTail] at previousEqual
        subst before
        simpa [CanAdvanceAt] using afterRepresents.2.2
    | lowUnary count =>
        simp only [previousTail] at previousEqual
        subst before
        simpa [CanAdvanceAt] using afterRepresents.2.2
    | loopUnary count =>
        simp only [previousTail] at previousEqual
        subst before
        simpa [CanAdvanceAt] using afterRepresents.2.2
    | sector kind exponent bits =>
        cases bits with
        | zero =>
            simp only [previousTail] at previousEqual
            subst before
            simpa [CanAdvanceAt] using afterRepresents.2.2
        | one first =>
            simp only [previousTail] at previousEqual
            subst before
            simpa [CanAdvanceAt] using afterRepresents.2.2
        | two first second =>
            let sector := sectorOfBits first second bit
            let block := blockMatrix kind exponent sector
            have newest :
                (Constraint.mk block kind exponent sector).Holds after := by
              apply afterRepresents.2.2.1
              change Constraint.mk block kind exponent sector ∈
                Constraint.mk block kind exponent sector ::
                  history.map (fun item => item.precompose block)
              exact List.mem_cons_self
            have previousEqual' :
                before = homographic block after := by
              simpa [previousTail, sector, block] using previousEqual
            have full : fullBlockHolds kind exponent sector before := by
              rw [previousEqual']
              exact newest.2
            have residual :
                normalizedValue kind exponent before - sector.rep ≠ 0 := by
              intro residualZero
              have terminal :
                  normalizedValue kind exponent before = sector.rep :=
                gaussian_eq_of_sub_eq_zero residualZero
              have normalizedTail := normalizedValue_block_homographic
                kind exponent sector after (by
                  simpa only [block] using newest.1)
              have terminalEquation :
                  sector.rep = sector.rep + (gamma * after)⁻¹ := by
                calc
                  sector.rep = normalizedValue kind exponent before :=
                    terminal.symm
                  _ = normalizedValue kind exponent
                      (homographic block after) := congrArg
                        (normalizedValue kind exponent) previousEqual'
                  _ = sector.rep + (gamma * after)⁻¹ := by
                    simpa only [block] using normalizedTail
              have inverseZero : (gamma * after)⁻¹ = 0 := by
                apply RFAP.ConstructiveGaussian.Gaussian.ext
                · have realEquation := congrArg
                      RFAP.ConstructiveGaussian.Gaussian.re terminalEquation
                  change sector.rep.re =
                    sector.rep.re + (gamma * after)⁻¹.re at realEquation
                  have cancelled : (0 : Coordinate) = (gamma * after)⁻¹.re :=
                    add_left_cancel (a := sector.rep.re)
                      ((_root_.add_zero sector.rep.re).trans realEquation)
                  exact cancelled.symm
                · have imaginaryEquation := congrArg
                      RFAP.ConstructiveGaussian.Gaussian.im terminalEquation
                  change sector.rep.im =
                    sector.rep.im + (gamma * after)⁻¹.im at imaginaryEquation
                  have cancelled : (0 : Coordinate) = (gamma * after)⁻¹.im :=
                    add_left_cancel (a := sector.rep.im)
                      ((_root_.add_zero sector.rep.im).trans imaginaryEquation)
                  exact cancelled.symm
              have afterNonzero := tail_ne_of_block_denominator kind exponent
                sector after (by simpa only [block] using newest.1)
              exact (inv_ne_zero_direct
                (mul_ne_zero_direct gamma_ne afterNonzero)) inverseZero
            exact ⟨full, residual⟩
  · intro advance
    rcases state with ⟨phase, matrix, history⟩
    cases phase with
    | initial =>
        refine ⟨before, ?_⟩
        apply step_represents_next
          ⟨.initial, matrix, history⟩ bit input before
        · simpa [previousTail] using beforeRepresents
        · simpa [CanAdvanceAt] using advance
    | highUnary count =>
        refine ⟨before, ?_⟩
        apply step_represents_next
          ⟨.highUnary count, matrix, history⟩ bit input before
        · simpa [previousTail] using beforeRepresents
        · simpa [CanAdvanceAt] using advance
    | lowUnary count =>
        refine ⟨before, ?_⟩
        apply step_represents_next
          ⟨.lowUnary count, matrix, history⟩ bit input before
        · simpa [previousTail] using beforeRepresents
        · simpa [CanAdvanceAt] using advance
    | loopUnary count =>
        refine ⟨before, ?_⟩
        apply step_represents_next
          ⟨.loopUnary count, matrix, history⟩ bit input before
        · simpa [previousTail] using beforeRepresents
        · simpa [CanAdvanceAt] using advance
    | sector kind exponent bits =>
        cases bits with
        | zero =>
            refine ⟨before, ?_⟩
            apply step_represents_next
              ⟨.sector kind exponent .zero, matrix, history⟩ bit input before
            · simpa [previousTail] using beforeRepresents
            · simpa [CanAdvanceAt] using advance
        | one first =>
            refine ⟨before, ?_⟩
            apply step_represents_next
              ⟨.sector kind exponent (.one first), matrix, history⟩ bit input
                before
            · simpa [previousTail] using beforeRepresents
            · simpa [CanAdvanceAt] using advance
        | two first second =>
            let sector := sectorOfBits first second bit
            let tail :=
              (gamma * (normalizedValue kind exponent before - sector.rep))⁻¹
            rcases advance with ⟨full, residual⟩
            refine ⟨tail, ?_⟩
            have completed := completeSector_represents_next
              ⟨.sector kind exponent (.two first second), matrix, history⟩
              kind exponent first second bit input before tail rfl
              beforeRepresents
              (by simpa only [tail, sector] using
                block_homographic_inverse kind exponent sector before residual)
              (by simpa only [tail, sector] using
                block_inverse_denominator_ne kind exponent sector before residual)
              (by simpa only [sector] using full)
              (by
                have loopActive := inverse_selected_loop_active kind exponent
                  sector before full residual
                simpa only [tail, sector] using loopActive)
            simpa only [step_eq_completeSector
              ⟨.sector kind exponent (.two first second), matrix, history⟩
              kind exponent first second bit rfl] using completed

/-- Total finite result of inspecting both Boolean children at a represented
rational input. -/
inductive LocalDecision (state : State) (input : Gaussian) where
  | terminal (none : ∀ bit, ¬CanStep state input bit)
  | next (bit : Bool) (possible : CanStep state input bit)
      (unique : ∀ other, CanStep state input other → other = bit)

/-- Decide the unique next bit, or certify that the current affine
representation is terminal. -/
def decideLocal
    (state : State) (input before : Gaussian)
    (determinantNonzero :
      CCL.Chordal.Mat2.det state.matrix ≠ 0)
    (beforeRepresents : Represents state input before) :
    LocalDecision state input := by
  by_cases falseAdvance : CanAdvanceAt state false before
  · have falsePossible : CanStep state input false :=
      (canStep_iff_canAdvanceAt state input before determinantNonzero
        beforeRepresents false).2 falseAdvance
    exact .next false falsePossible (by
      intro other otherPossible
      exact canStep_unique determinantNonzero otherPossible falsePossible)
  · by_cases trueAdvance : CanAdvanceAt state true before
    · have truePossible : CanStep state input true :=
        (canStep_iff_canAdvanceAt state input before determinantNonzero
          beforeRepresents true).2 trueAdvance
      exact .next true truePossible (by
        intro other otherPossible
        exact canStep_unique determinantNonzero otherPossible truePossible)
    · exact .terminal (by
        intro bit possible
        cases bit
        · exact falseAdvance
            ((canStep_iff_canAdvanceAt state input before determinantNonzero
              beforeRepresents false).1 possible)
        · exact trueAdvance
            ((canStep_iff_canAdvanceAt state input before determinantNonzero
              beforeRepresents true).1 possible))

end CCL.ParserStep
