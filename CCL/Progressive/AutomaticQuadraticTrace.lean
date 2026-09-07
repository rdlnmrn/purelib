import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Progressive.QuadraticTrace

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

namespace CCL.ProgressiveAutomaticQuadraticTrace

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Certificate := CCL.QuadraticJet.Certificate
abbrev Trace := CCL.ProgressiveQuadraticTrace.Trace

open RFAP.ConstructiveGaussian.Gaussian

/-- A single finite-stage channel with an explicit geometric modulus and
uniform rational centre bound. -/
structure Channel (sample : Nat → Gaussian) where
  errorScale : Coordinate
  errorScale_nonneg : 0 ≤ errorScale
  later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    normSq (sample later - sample earlier) ≤
      CCL.FiniteGeometric.quarterRadius errorScale earlier
  centerBound : Coordinate
  centerBound_nonneg : 0 ≤ centerBound
  bounded : ∀ index, normSq (sample index) ≤ centerBound

namespace Channel

private theorem quarterRadius_scale_mono {small large : Coordinate}
    (order : small ≤ large) (index : Nat) :
    CCL.FiniteGeometric.quarterRadius small index ≤
      CCL.FiniteGeometric.quarterRadius large index := by
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct order
    (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) index)

private theorem left_le_sum (left right : Coordinate)
    (rightNonnegative : 0 ≤ right) : left ≤ left + right :=
  le_add_of_nonneg_right rightNonnegative

private theorem right_le_sum (left right : Coordinate)
    (leftNonnegative : 0 ≤ left) : right ≤ left + right :=
  le_add_of_nonneg_left leftNonnegative

def exact (value : Gaussian) : Channel (fun _ => value) where
  errorScale := 0
  errorScale_nonneg := le_rfl
  later_close := by
    intro earlier later order
    rw [sub_self, normSq_zero,
      CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
      RFAP.ConstructiveFraction.zero_mul_direct]
  centerBound := normSq value
  centerBound_nonneg := normSq_nonneg value
  bounded := fun _ => le_rfl

def map {source target : Nat → Gaussian} (channel : Channel source)
    (same : ∀ index, target index = source index) : Channel target where
  errorScale := channel.errorScale
  errorScale_nonneg := channel.errorScale_nonneg
  later_close := by
    intro earlier later order
    rw [same later, same earlier]
    exact channel.later_close order
  centerBound := channel.centerBound
  centerBound_nonneg := channel.centerBound_nonneg
  bounded := by
    intro index
    rw [same index]
    exact channel.bounded index

def add {left right : Nat → Gaussian}
    (leftChannel : Channel left) (rightChannel : Channel right) :
    Channel (fun index => left index + right index) where
  errorScale := 2 * (leftChannel.errorScale + rightChannel.errorScale)
  errorScale_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg leftChannel.errorScale_nonneg
        rightChannel.errorScale_nonneg)
  later_close := by
    intro earlier later order
    have identity :
        (left later + right later) - (left earlier + right earlier) =
          (left later - left earlier) + (right later - right earlier) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, sub_re, sub_im] <;> ring1
    rw [identity]
    calc
      normSq ((left later - left earlier) +
          (right later - right earlier)) ≤
          2 * (normSq (left later - left earlier) +
            normSq (right later - right earlier)) :=
        normSq_add_le_two _ _
      _ ≤ 2 *
          (CCL.FiniteGeometric.quarterRadius
              leftChannel.errorScale earlier +
            CCL.FiniteGeometric.quarterRadius
              rightChannel.errorScale earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add (leftChannel.later_close order)
            (rightChannel.later_close order)) (by decide)
      _ = CCL.FiniteGeometric.quarterRadius
          (2 * (leftChannel.errorScale + rightChannel.errorScale)) earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        ring1
  centerBound := 2 * (leftChannel.centerBound + rightChannel.centerBound)
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg leftChannel.centerBound_nonneg
        rightChannel.centerBound_nonneg)
  bounded := by
    intro index
    calc
      normSq (left index + right index) ≤
          2 * (normSq (left index) + normSq (right index)) :=
        normSq_add_le_two _ _
      _ ≤ 2 * (leftChannel.centerBound + rightChannel.centerBound) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add (leftChannel.bounded index)
            (rightChannel.bounded index)) (by decide)

def neg {source : Nat → Gaussian} (channel : Channel source) :
    Channel (fun index => -source index) where
  errorScale := channel.errorScale
  errorScale_nonneg := channel.errorScale_nonneg
  later_close := by
    intro earlier later order
    have identity : -source later - -source earlier =
        -(source later - source earlier) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [neg_re, neg_im, sub_re, sub_im] <;> ring1
    rw [identity, normSq_neg]
    exact channel.later_close order
  centerBound := channel.centerBound
  centerBound_nonneg := channel.centerBound_nonneg
  bounded := by
    intro index
    rw [normSq_neg]
    exact channel.bounded index

def sub {left right : Nat → Gaussian}
    (leftChannel : Channel left) (rightChannel : Channel right) :
    Channel (fun index => left index - right index) :=
  (leftChannel.add rightChannel.neg).map (by
    intro index
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [add_re, add_im, sub_re, sub_im, neg_re, neg_im] <;> ring1)

def mul {left right : Nat → Gaussian}
    (leftChannel : Channel left) (rightChannel : Channel right) :
    Channel (fun index => left index * right index) where
  errorScale := 2 *
    (leftChannel.errorScale * rightChannel.centerBound +
      leftChannel.centerBound * rightChannel.errorScale)
  errorScale_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          leftChannel.errorScale_nonneg rightChannel.centerBound_nonneg)
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          leftChannel.centerBound_nonneg rightChannel.errorScale_nonneg))
  later_close := by
    intro earlier later order
    have identity :
        left later * right later - left earlier * right earlier =
          (left later - left earlier) * right later +
            left earlier * (right later - right earlier) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im] <;> ring1
    rw [identity]
    have first :
        normSq ((left later - left earlier) * right later) ≤
          CCL.FiniteGeometric.quarterRadius
              leftChannel.errorScale earlier * rightChannel.centerBound := by
      rw [normSq_mul]
      exact RFAP.ConstructiveFraction.mul_le_mul_direct
        (leftChannel.later_close order) (rightChannel.bounded later)
        (normSq_nonneg _) (CCL.FiniteGeometric.quarterRadius_nonneg
          leftChannel.errorScale_nonneg earlier)
    have second :
        normSq (left earlier * (right later - right earlier)) ≤
          leftChannel.centerBound *
            CCL.FiniteGeometric.quarterRadius
              rightChannel.errorScale earlier := by
      rw [normSq_mul]
      exact RFAP.ConstructiveFraction.mul_le_mul_direct
        (leftChannel.bounded earlier) (rightChannel.later_close order)
        (normSq_nonneg _) leftChannel.centerBound_nonneg
    calc
      normSq ((left later - left earlier) * right later +
          left earlier * (right later - right earlier)) ≤
          2 * (normSq ((left later - left earlier) * right later) +
            normSq (left earlier * (right later - right earlier))) :=
        normSq_add_le_two _ _
      _ ≤ 2 *
          (CCL.FiniteGeometric.quarterRadius
              leftChannel.errorScale earlier * rightChannel.centerBound +
            leftChannel.centerBound *
              CCL.FiniteGeometric.quarterRadius
                rightChannel.errorScale earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add first second) (by decide)
      _ = CCL.FiniteGeometric.quarterRadius
          (2 * (leftChannel.errorScale * rightChannel.centerBound +
            leftChannel.centerBound * rightChannel.errorScale)) earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        ring1
  centerBound := leftChannel.centerBound * rightChannel.centerBound
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      leftChannel.centerBound_nonneg rightChannel.centerBound_nonneg
  bounded := by
    intro index
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      (leftChannel.bounded index) (rightChannel.bounded index)
      (normSq_nonneg _) leftChannel.centerBound_nonneg

def scale (scalar : Gaussian) {source : Nat → Gaussian}
    (channel : Channel source) :
    Channel (fun index => scalar * source index) :=
  (Channel.exact scalar).mul channel

private theorem quarterRadius_succ_le (scale : Coordinate)
    (scaleNonnegative : 0 ≤ scale) (index : Nat) :
    CCL.FiniteGeometric.quarterRadius scale (index + 1) ≤
      CCL.FiniteGeometric.quarterRadius scale index := by
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_succ]
  calc
    scale * ((1 / 4 : Coordinate) ^ index * (1 / 4)) =
        (scale * (1 / 4 : Coordinate) ^ index) * (1 / 4) := by ring1
    _ ≤ (scale * (1 / 4 : Coordinate) ^ index) * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct (by decide)
        (RFAP.ConstructiveFraction.mul_nonneg_direct scaleNonnegative
          (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) index))
    _ = scale * (1 / 4 : Coordinate) ^ index :=
      RFAP.ConstructiveFraction.mul_one_direct _

/-- Apply the finite exponential Horner program at depth `index + 1` to a
geometrically coherent unit-disk channel. -/
def expSample {source : Nat → Gaussian} (channel : Channel source)
    (unit : ∀ index, normSq (source index) ≤ 1) :
    Channel (fun index =>
      CCL.FiniteExp.sample (source index) (index + 1)) where
  errorScale := 2 * (10 + 16 * channel.errorScale)
  errorScale_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg (by decide)
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          channel.errorScale_nonneg))
  later_close := by
    intro earlier later order
    have depthOrder : earlier + 1 ≤ later + 1 := by omega
    have truncationRaw := CCL.FiniteExp.sample_later_close
      (source later) (unit later) depthOrder
    have truncation :
        normSq
            (CCL.FiniteExp.sample (source later) (later + 1) -
              CCL.FiniteExp.sample (source later) (earlier + 1)) ≤
          CCL.FiniteGeometric.quarterRadius 10 earlier :=
      truncationRaw.trans (quarterRadius_succ_le 10 (by decide) earlier)
    have inputEffectRaw := CCL.FiniteExp.sample_input_close
      (source later) (source earlier) (unit later) (unit earlier)
        (earlier + 1)
    have inputEffect :
        normSq
            (CCL.FiniteExp.sample (source later) (earlier + 1) -
              CCL.FiniteExp.sample (source earlier) (earlier + 1)) ≤
          16 * CCL.FiniteGeometric.quarterRadius
            channel.errorScale earlier :=
      inputEffectRaw.trans
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (channel.later_close order) (by decide))
    calc
      normSq
          (CCL.FiniteExp.sample (source later) (later + 1) -
            CCL.FiniteExp.sample (source earlier) (earlier + 1)) ≤
        2 *
          (normSq
              (CCL.FiniteExp.sample (source later) (later + 1) -
                CCL.FiniteExp.sample (source later) (earlier + 1)) +
            normSq
              (CCL.FiniteExp.sample (source later) (earlier + 1) -
                CCL.FiniteExp.sample (source earlier)
                  (earlier + 1))) := normSq_sub_le_via _ _ _
      _ ≤ 2 * (CCL.FiniteGeometric.quarterRadius 10 earlier +
          16 * CCL.FiniteGeometric.quarterRadius
            channel.errorScale earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add truncation inputEffect) (by decide)
      _ = CCL.FiniteGeometric.quarterRadius
          (2 * (10 + 16 * channel.errorScale)) earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        ring1
  centerBound := 10
  centerBound_nonneg := by decide
  bounded := fun index =>
    CCL.FiniteExp.sample_bounded (source index) (unit index)
      (index + 1)

/-- Apply the finite reduced complex-log Horner program at depth `index + 1`
to a geometrically coherent channel in its displayed `1/9` disk. -/
def reducedLogSample {source : Nat → Gaussian} (channel : Channel source)
    (disk : ∀ index, normSq (source index) ≤ 1 / 9) :
    Channel (fun index =>
      CCL.FiniteComplexLog.sample (source index) (index + 1)) where
  errorScale := 2 *
    (5 + CCL.FiniteComplexLog.sampleInputScale *
      channel.errorScale)
  errorScale_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg (by decide)
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          CCL.FiniteComplexLog.sampleInputScale_nonneg
          channel.errorScale_nonneg))
  later_close := by
    intro earlier later order
    have depthOrder : earlier + 1 ≤ later + 1 := by omega
    have truncationRaw :=
      CCL.FiniteComplexLog.sample_later_close
        (disk later) depthOrder
    have truncation :
        normSq
            (CCL.FiniteComplexLog.sample (source later)
                (later + 1) -
              CCL.FiniteComplexLog.sample (source later)
                (earlier + 1)) ≤
          CCL.FiniteGeometric.quarterRadius 5 earlier := by
      calc
        _ ≤ 5 * (1 / 4 : Coordinate) ^ (earlier + 1) := truncationRaw
        _ = CCL.FiniteGeometric.quarterRadius 5 (earlier + 1) :=
          (CCL.FiniteGeometric.quarterRadius_eq_mul_pow
            5 (earlier + 1)).symm
        _ ≤ CCL.FiniteGeometric.quarterRadius 5 earlier :=
          quarterRadius_succ_le 5 (by decide) earlier
    have inputEffectRaw :=
      CCL.FiniteComplexLog.sample_input_close
        (disk later) (disk earlier) (earlier + 1)
    have inputEffect :
        normSq
            (CCL.FiniteComplexLog.sample (source later)
                (earlier + 1) -
              CCL.FiniteComplexLog.sample (source earlier)
                (earlier + 1)) ≤
          CCL.FiniteComplexLog.sampleInputScale *
            CCL.FiniteGeometric.quarterRadius
              channel.errorScale earlier :=
      inputEffectRaw.trans
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (channel.later_close order)
          CCL.FiniteComplexLog.sampleInputScale_nonneg)
    calc
      normSq
          (CCL.FiniteComplexLog.sample (source later)
              (later + 1) -
            CCL.FiniteComplexLog.sample (source earlier)
              (earlier + 1)) ≤
        2 *
          (normSq
              (CCL.FiniteComplexLog.sample (source later)
                  (later + 1) -
                CCL.FiniteComplexLog.sample (source later)
                  (earlier + 1)) +
            normSq
              (CCL.FiniteComplexLog.sample (source later)
                  (earlier + 1) -
                CCL.FiniteComplexLog.sample (source earlier)
                  (earlier + 1))) := normSq_sub_le_via _ _ _
      _ ≤ 2 *
          (CCL.FiniteGeometric.quarterRadius 5 earlier +
            CCL.FiniteComplexLog.sampleInputScale *
              CCL.FiniteGeometric.quarterRadius
                channel.errorScale earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add truncation inputEffect) (by decide)
      _ = CCL.FiniteGeometric.quarterRadius
          (2 * (5 + CCL.FiniteComplexLog.sampleInputScale *
            channel.errorScale)) earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        ring1
  centerBound := 1
  centerBound_nonneg := by decide
  bounded := fun index =>
    CCL.FiniteComplexLog.sample_bounded_one (disk index)
      (index + 1)

/-- A displayed positive lower quadrance is precisely the finite evidence
needed to transport a reciprocal channel. -/
def reciprocal {source : Nat → Gaussian} (channel : Channel source)
    (lower : Coordinate) (lowerPositive : 0 < lower)
    (lowerBound : ∀ index, lower ≤ normSq (source index)) :
    Channel (fun index => inv (source index)) where
  errorScale := channel.errorScale * (lower⁻¹ * lower⁻¹)
  errorScale_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct channel.errorScale_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.inv_pos_direct lowerPositive).le
        (RFAP.ConstructiveFraction.inv_pos_direct lowerPositive).le)
  later_close := by
    intro earlier later order
    have laterNonzero : source later ≠ 0 := by
      intro zero
      have bound := lowerBound later
      rw [zero, normSq_zero] at bound
      exact (not_le_of_gt lowerPositive) bound
    have earlierNonzero : source earlier ≠ 0 := by
      intro zero
      have bound := lowerBound earlier
      rw [zero, normSq_zero] at bound
      exact (not_le_of_gt lowerPositive) bound
    have laterInverseBound : normSq (inv (source later)) ≤ lower⁻¹ := by
      rw [normSq_inv _ laterNonzero]
      exact RFAP.ConstructiveFraction.inv_le_inv_of_pos_direct lowerPositive
        (lowerBound later)
    have earlierInverseBound : normSq (inv (source earlier)) ≤ lower⁻¹ := by
      rw [normSq_inv _ earlierNonzero]
      exact RFAP.ConstructiveFraction.inv_le_inv_of_pos_direct lowerPositive
        (lowerBound earlier)
    have reverseDistance :
        normSq (source earlier - source later) =
          normSq (source later - source earlier) := by
      have identity : source earlier - source later =
          -(source later - source earlier) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
      rw [identity, normSq_neg]
    change normSq (inv (source later) - inv (source earlier)) ≤ _
    rw [CCL.RedundantSectors.inverse_sub_inverse_direct
      laterNonzero earlierNonzero, normSq_mul, normSq_mul,
      normSq_inv _ laterNonzero, normSq_inv _ earlierNonzero,
      reverseDistance]
    have inverseProductBound :
        normSq (inv (source later)) * normSq (inv (source earlier)) ≤
          lower⁻¹ * lower⁻¹ :=
      RFAP.ConstructiveFraction.mul_le_mul_direct laterInverseBound
        earlierInverseBound (normSq_nonneg _)
        (RFAP.ConstructiveFraction.inv_pos_direct lowerPositive).le
    calc
      (normSq (source later))⁻¹ *
          normSq (source later - source earlier) *
            (normSq (source earlier))⁻¹ =
        normSq (source later - source earlier) *
          (normSq (inv (source later)) * normSq (inv (source earlier))) := by
            rw [normSq_inv _ laterNonzero, normSq_inv _ earlierNonzero]
            calc
              ((normSq (source later))⁻¹ *
                    normSq (source later - source earlier)) *
                  (normSq (source earlier))⁻¹ =
                (normSq (source later - source earlier) *
                    (normSq (source later))⁻¹) *
                  (normSq (source earlier))⁻¹ := by
                    rw [RFAP.ConstructiveFraction.mul_comm
                      (normSq (source later))⁻¹
                      (normSq (source later - source earlier))]
              _ = normSq (source later - source earlier) *
                  ((normSq (source later))⁻¹ *
                    (normSq (source earlier))⁻¹) :=
                RFAP.ConstructiveFraction.mul_assoc _ _ _
      _ ≤
        CCL.FiniteGeometric.quarterRadius
            channel.errorScale earlier * (lower⁻¹ * lower⁻¹) :=
          RFAP.ConstructiveFraction.mul_le_mul_direct
            (channel.later_close order) inverseProductBound
            (RFAP.ConstructiveFraction.mul_nonneg_direct (normSq_nonneg _)
              (normSq_nonneg _))
            (CCL.FiniteGeometric.quarterRadius_nonneg
              channel.errorScale_nonneg earlier)
      _ = CCL.FiniteGeometric.quarterRadius
          (channel.errorScale * (lower⁻¹ * lower⁻¹)) earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        calc
          (channel.errorScale * (1 / 4 : Coordinate) ^ earlier) *
                (lower⁻¹ * lower⁻¹) =
              channel.errorScale *
                ((1 / 4 : Coordinate) ^ earlier *
                  (lower⁻¹ * lower⁻¹)) :=
            RFAP.ConstructiveFraction.mul_assoc _ _ _
          _ = channel.errorScale *
                ((lower⁻¹ * lower⁻¹) *
                  (1 / 4 : Coordinate) ^ earlier) := by
            rw [RFAP.ConstructiveFraction.mul_comm
              ((1 / 4 : Coordinate) ^ earlier) (lower⁻¹ * lower⁻¹)]
          _ = (channel.errorScale * (lower⁻¹ * lower⁻¹)) *
                (1 / 4 : Coordinate) ^ earlier :=
            (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm
  centerBound := lower⁻¹
  centerBound_nonneg :=
    (RFAP.ConstructiveFraction.inv_pos_direct lowerPositive).le
  bounded := by
    intro index
    have nonzero : source index ≠ 0 := by
      intro zero
      have bound := lowerBound index
      rw [zero, normSq_zero] at bound
      exact (not_le_of_gt lowerPositive) bound
    change normSq (inv (source index)) ≤ lower⁻¹
    rw [normSq_inv _ nonzero]
    exact RFAP.ConstructiveFraction.inv_le_inv_of_pos_direct lowerPositive
      (lowerBound index)

end Channel

namespace Trace

def incrementField {increment : Nat → Gaussian} (trace : Trace increment) :
    Channel increment :=
  ⟨trace.errorScale, trace.errorScale_nonneg, trace.increment_later_close,
    trace.centerBound, trace.centerBound_nonneg, trace.increment_bounded⟩

def baseField {increment : Nat → Gaussian} (trace : Trace increment) :
    Channel (fun index => (trace.certificate index).base) :=
  ⟨trace.errorScale, trace.errorScale_nonneg, trace.base_later_close,
    trace.centerBound, trace.centerBound_nonneg, trace.base_bounded⟩

def outputField {increment : Nat → Gaussian} (trace : Trace increment) :
    Channel (fun index => (trace.certificate index).output) :=
  ⟨trace.errorScale, trace.errorScale_nonneg, trace.output_later_close,
    trace.centerBound, trace.centerBound_nonneg, trace.output_bounded⟩

def slopeField {increment : Nat → Gaussian} (trace : Trace increment) :
    Channel (fun index => (trace.certificate index).slope) :=
  ⟨trace.errorScale, trace.errorScale_nonneg, trace.slope_later_close,
    trace.centerBound, trace.centerBound_nonneg, trace.slope_bounded⟩

def remainderField {increment : Nat → Gaussian} (trace : Trace increment) :
    Channel (fun index => (trace.certificate index).remainder) :=
  ⟨trace.errorScale, trace.errorScale_nonneg, trace.remainder_later_close,
    trace.centerBound, trace.centerBound_nonneg, trace.remainder_bounded⟩

private def totalScale {increment : Nat → Gaussian}
    {certificates : (index : Nat) → Certificate (increment index)}
    (incrementField : Channel increment)
    (baseField : Channel (fun index => (certificates index).base))
    (outputField : Channel (fun index => (certificates index).output))
    (slopeField : Channel (fun index => (certificates index).slope))
    (remainderField : Channel (fun index => (certificates index).remainder)) :
    Coordinate :=
  incrementField.errorScale + baseField.errorScale + outputField.errorScale +
    slopeField.errorScale + remainderField.errorScale

private def totalBound {increment : Nat → Gaussian}
    {certificates : (index : Nat) → Certificate (increment index)}
    (incrementField : Channel increment)
    (baseField : Channel (fun index => (certificates index).base))
    (outputField : Channel (fun index => (certificates index).output))
    (slopeField : Channel (fun index => (certificates index).slope))
    (remainderField : Channel (fun index => (certificates index).remainder)) :
    Coordinate :=
  incrementField.centerBound + baseField.centerBound + outputField.centerBound +
    slopeField.centerBound + remainderField.centerBound

private theorem component_le_totalScale {increment : Nat → Gaussian}
    {certificates : (index : Nat) → Certificate (increment index)}
    (incrementField : Channel increment)
    (baseField : Channel (fun index => (certificates index).base))
    (outputField : Channel (fun index => (certificates index).output))
    (slopeField : Channel (fun index => (certificates index).slope))
    (remainderField : Channel (fun index => (certificates index).remainder)) :
    incrementField.errorScale ≤ totalScale incrementField baseField outputField
        slopeField remainderField ∧
      baseField.errorScale ≤ totalScale incrementField baseField outputField
        slopeField remainderField ∧
      outputField.errorScale ≤ totalScale incrementField baseField outputField
        slopeField remainderField ∧
      slopeField.errorScale ≤ totalScale incrementField baseField outputField
        slopeField remainderField ∧
      remainderField.errorScale ≤ totalScale incrementField baseField outputField
        slopeField remainderField := by
  unfold totalScale
  constructor
  · calc
      incrementField.errorScale ≤ incrementField.errorScale +
          baseField.errorScale :=
        le_add_of_nonneg_right baseField.errorScale_nonneg
      _ ≤ incrementField.errorScale + baseField.errorScale +
          outputField.errorScale :=
        le_add_of_nonneg_right outputField.errorScale_nonneg
      _ ≤ incrementField.errorScale + baseField.errorScale +
          outputField.errorScale + slopeField.errorScale :=
        le_add_of_nonneg_right slopeField.errorScale_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.errorScale_nonneg
  constructor
  · calc
      baseField.errorScale ≤ incrementField.errorScale +
          baseField.errorScale :=
        le_add_of_nonneg_left incrementField.errorScale_nonneg
      _ ≤ incrementField.errorScale + baseField.errorScale +
          outputField.errorScale :=
        le_add_of_nonneg_right outputField.errorScale_nonneg
      _ ≤ incrementField.errorScale + baseField.errorScale +
          outputField.errorScale + slopeField.errorScale :=
        le_add_of_nonneg_right slopeField.errorScale_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.errorScale_nonneg
  constructor
  · calc
      outputField.errorScale ≤ incrementField.errorScale +
          baseField.errorScale + outputField.errorScale :=
        le_add_of_nonneg_left (add_nonneg incrementField.errorScale_nonneg
          baseField.errorScale_nonneg)
      _ ≤ incrementField.errorScale + baseField.errorScale +
          outputField.errorScale + slopeField.errorScale :=
        le_add_of_nonneg_right slopeField.errorScale_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.errorScale_nonneg
  constructor
  · calc
      slopeField.errorScale ≤ incrementField.errorScale +
          baseField.errorScale + outputField.errorScale +
            slopeField.errorScale :=
        le_add_of_nonneg_left (add_nonneg (add_nonneg
          incrementField.errorScale_nonneg baseField.errorScale_nonneg)
          outputField.errorScale_nonneg)
      _ ≤ _ := le_add_of_nonneg_right remainderField.errorScale_nonneg
  · exact le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg
      incrementField.errorScale_nonneg baseField.errorScale_nonneg)
      outputField.errorScale_nonneg) slopeField.errorScale_nonneg)

private theorem component_le_totalBound {increment : Nat → Gaussian}
    {certificates : (index : Nat) → Certificate (increment index)}
    (incrementField : Channel increment)
    (baseField : Channel (fun index => (certificates index).base))
    (outputField : Channel (fun index => (certificates index).output))
    (slopeField : Channel (fun index => (certificates index).slope))
    (remainderField : Channel (fun index => (certificates index).remainder)) :
    incrementField.centerBound ≤ totalBound incrementField baseField outputField
        slopeField remainderField ∧
      baseField.centerBound ≤ totalBound incrementField baseField outputField
        slopeField remainderField ∧
      outputField.centerBound ≤ totalBound incrementField baseField outputField
        slopeField remainderField ∧
      slopeField.centerBound ≤ totalBound incrementField baseField outputField
        slopeField remainderField ∧
      remainderField.centerBound ≤ totalBound incrementField baseField outputField
        slopeField remainderField := by
  unfold totalBound
  constructor
  · calc
      incrementField.centerBound ≤ incrementField.centerBound +
          baseField.centerBound :=
        le_add_of_nonneg_right baseField.centerBound_nonneg
      _ ≤ incrementField.centerBound + baseField.centerBound +
          outputField.centerBound :=
        le_add_of_nonneg_right outputField.centerBound_nonneg
      _ ≤ incrementField.centerBound + baseField.centerBound +
          outputField.centerBound + slopeField.centerBound :=
        le_add_of_nonneg_right slopeField.centerBound_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.centerBound_nonneg
  constructor
  · calc
      baseField.centerBound ≤ incrementField.centerBound +
          baseField.centerBound :=
        le_add_of_nonneg_left incrementField.centerBound_nonneg
      _ ≤ incrementField.centerBound + baseField.centerBound +
          outputField.centerBound :=
        le_add_of_nonneg_right outputField.centerBound_nonneg
      _ ≤ incrementField.centerBound + baseField.centerBound +
          outputField.centerBound + slopeField.centerBound :=
        le_add_of_nonneg_right slopeField.centerBound_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.centerBound_nonneg
  constructor
  · calc
      outputField.centerBound ≤ incrementField.centerBound +
          baseField.centerBound + outputField.centerBound :=
        le_add_of_nonneg_left (add_nonneg incrementField.centerBound_nonneg
          baseField.centerBound_nonneg)
      _ ≤ incrementField.centerBound + baseField.centerBound +
          outputField.centerBound + slopeField.centerBound :=
        le_add_of_nonneg_right slopeField.centerBound_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.centerBound_nonneg
  constructor
  · calc
      slopeField.centerBound ≤ incrementField.centerBound +
          baseField.centerBound + outputField.centerBound +
            slopeField.centerBound :=
        le_add_of_nonneg_left (add_nonneg (add_nonneg
          incrementField.centerBound_nonneg baseField.centerBound_nonneg)
          outputField.centerBound_nonneg)
      _ ≤ _ := le_add_of_nonneg_right remainderField.centerBound_nonneg
  · exact le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg
      incrementField.centerBound_nonneg baseField.centerBound_nonneg)
      outputField.centerBound_nonneg) slopeField.centerBound_nonneg)

/-- Combine five independently calculated channels into the one common
transport record required by a semantic quadratic trace. -/
def transportOfChannels {increment : Nat → Gaussian}
    {certificates : (index : Nat) → Certificate (increment index)}
    (incrementField : Channel increment)
    (baseField : Channel (fun index => (certificates index).base))
    (outputField : Channel (fun index => (certificates index).output))
    (slopeField : Channel (fun index => (certificates index).slope))
    (remainderField : Channel (fun index => (certificates index).remainder)) :
    CCL.ProgressiveQuadraticTrace.Trace.Transport
      increment certificates := by
  let scale := totalScale incrementField baseField outputField slopeField
    remainderField
  let bound := totalBound incrementField baseField outputField slopeField
    remainderField
  have scaleNonnegative : 0 ≤ scale := by
    dsimp only [scale, totalScale]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg
      incrementField.errorScale_nonneg baseField.errorScale_nonneg)
      outputField.errorScale_nonneg) slopeField.errorScale_nonneg)
      remainderField.errorScale_nonneg
  have boundNonnegative : 0 ≤ bound := by
    dsimp only [bound, totalBound]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg
      incrementField.centerBound_nonneg baseField.centerBound_nonneg)
      outputField.centerBound_nonneg) slopeField.centerBound_nonneg)
      remainderField.centerBound_nonneg
  rcases component_le_totalScale incrementField baseField outputField
    slopeField remainderField with ⟨incrementScale, baseScale, outputScale,
      slopeScale, remainderScale⟩
  rcases component_le_totalBound incrementField baseField outputField
    slopeField remainderField with ⟨incrementBound, baseBound, outputBound,
      slopeBound, remainderBound⟩
  exact
    { errorScale := scale
      errorScale_nonneg := scaleNonnegative
      increment_later_close := fun order =>
        (incrementField.later_close order).trans
          (Channel.quarterRadius_scale_mono incrementScale _)
      base_later_close := fun order =>
        (baseField.later_close order).trans
          (Channel.quarterRadius_scale_mono baseScale _)
      output_later_close := fun order =>
        (outputField.later_close order).trans
          (Channel.quarterRadius_scale_mono outputScale _)
      slope_later_close := fun order =>
        (slopeField.later_close order).trans
          (Channel.quarterRadius_scale_mono slopeScale _)
      remainder_later_close := fun order =>
        (remainderField.later_close order).trans
          (Channel.quarterRadius_scale_mono remainderScale _)
      centerBound := bound
      centerBound_nonneg := boundNonnegative
      increment_bounded := fun index =>
        (incrementField.bounded index).trans incrementBound
      base_bounded := fun index => (baseField.bounded index).trans baseBound
      output_bounded := fun index =>
        (outputField.bounded index).trans outputBound
      slope_bounded := fun index => (slopeField.bounded index).trans slopeBound
      remainder_bounded := fun index =>
        (remainderField.bounded index).trans remainderBound }

/-- Scalar multiplication is another automatically transported trace
constructor. -/
def scaleAutomatic (scalar : Gaussian) {increment : Nat → Gaussian}
    (trace : Trace increment) : Trace increment := by
  let certificates := fun index =>
    (trace.certificate index).scale scalar
  let incrementChannel := trace.incrementField
  let baseChannel := trace.baseField.scale scalar
  let outputChannel := trace.outputField.scale scalar
  let slopeChannel := trace.slopeField.scale scalar
  let remainderChannel := trace.remainderField.scale scalar
  have baseChannel' : Channel (fun index => (certificates index).base) :=
    baseChannel.map (by intro index; rfl)
  have outputChannel' : Channel (fun index => (certificates index).output) :=
    outputChannel.map (by intro index; rfl)
  have slopeChannel' : Channel (fun index => (certificates index).slope) :=
    slopeChannel.map (by intro index; rfl)
  have remainderChannel' :
      Channel (fun index => (certificates index).remainder) :=
    remainderChannel.map (by intro index; rfl)
  exact CCL.ProgressiveQuadraticTrace.Trace.ofTransport
    (transportOfChannels incrementChannel baseChannel' outputChannel'
      slopeChannel' remainderChannel')

@[simp] theorem scaleAutomatic_certificate (scalar : Gaussian)
    {increment : Nat → Gaussian} (trace : Trace increment) (index : Nat) :
    (scaleAutomatic scalar trace).certificate index =
      (trace.certificate index).scale scalar := rfl

/-- Multiplication with a fully computed geometric transport record. -/
def mulAutomatic {increment : Nat → Gaussian}
    (left right : Trace increment) : Trace increment := by
  let certificates := fun index =>
    (left.certificate index).mul (right.certificate index)
  let incrementChannel := left.incrementField
  let baseChannel := left.baseField.mul right.baseField
  let outputChannel := left.outputField.mul right.outputField
  let slopeChannel :=
    (left.slopeField.mul right.baseField).add
      (left.baseField.mul right.slopeField)
  let remainderChannel :=
    (outputChannel.sub baseChannel).sub (incrementChannel.mul slopeChannel)
  have baseChannel' : Channel (fun index => (certificates index).base) :=
    baseChannel.map (by intro index; rfl)
  have outputChannel' : Channel (fun index => (certificates index).output) :=
    outputChannel.map (by intro index; rfl)
  have slopeChannel' : Channel (fun index => (certificates index).slope) :=
    slopeChannel.map (by intro index; rfl)
  have remainderChannel' :
      Channel (fun index => (certificates index).remainder) :=
    remainderChannel.map (by intro index; rfl)
  exact CCL.ProgressiveQuadraticTrace.Trace.ofTransport
    (transportOfChannels incrementChannel baseChannel' outputChannel'
      slopeChannel' remainderChannel')

@[simp] theorem mulAutomatic_certificate {increment : Nat → Gaussian}
    (left right : Trace increment) (index : Nat) :
    (mulAutomatic left right).certificate index =
      (left.certificate index).mul (right.certificate index) := rfl

/-- Composition consumes a semantic outer trace and automatically transports
all five fields back to the inner increment. -/
def composeAutomatic {increment : Nat → Gaussian} (inner : Trace increment)
    (outer : Trace (fun index =>
      (inner.certificate index).output - (inner.certificate index).base))
    (unit : ∀ index, normSq (increment index) ≤ 1) : Trace increment := by
  let certificates := fun index =>
    (inner.certificate index).compose (outer.certificate index) (unit index)
  let incrementChannel := inner.incrementField
  let baseChannel := outer.baseField
  let outputChannel := outer.outputField
  let slopeChannel := inner.slopeField.mul outer.slopeField
  let remainderChannel :=
    (inner.remainderField.mul outer.slopeField).add outer.remainderField
  have baseChannel' : Channel (fun index => (certificates index).base) :=
    baseChannel.map (by intro index; rfl)
  have outputChannel' : Channel (fun index => (certificates index).output) :=
    outputChannel.map (by intro index; rfl)
  have slopeChannel' : Channel (fun index => (certificates index).slope) :=
    slopeChannel.map (by intro index; rfl)
  have remainderChannel' :
      Channel (fun index => (certificates index).remainder) :=
    remainderChannel.map (by intro index; rfl)
  exact CCL.ProgressiveQuadraticTrace.Trace.ofTransport
    (transportOfChannels incrementChannel baseChannel' outputChannel'
      slopeChannel' remainderChannel')

@[simp] theorem composeAutomatic_certificate {increment : Nat → Gaussian}
    (inner : Trace increment)
    (outer : Trace (fun index =>
      (inner.certificate index).output - (inner.certificate index).base))
    (unit : ∀ index, normSq (increment index) ≤ 1) (index : Nat) :
    (composeAutomatic inner outer unit).certificate index =
      (inner.certificate index).compose (outer.certificate index)
        (unit index) := rfl

/-- The finite translated-exponential certificates themselves form a
semantic trace whenever their displayed base and displacement channels stay
inside the rational unit disk. -/
def exponentialOuterTrace {increment : Nat → Gaussian}
    (inner : Trace increment)
    (baseUnit : ∀ index, normSq (inner.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1) :
    Trace (fun index =>
      (inner.certificate index).output - (inner.certificate index).base) := by
  let movementChannel := inner.outputField.sub inner.baseField
  let certificates := fun index =>
    CCL.QuadraticJet.Certificate.exponential
      (baseUnit index) (movementUnit index) index
  let baseExp := inner.baseField.expSample baseUnit
  let movementExp := movementChannel.expSample movementUnit
  let outputExp := baseExp.mul movementExp
  let remainderChannel :=
    (outputExp.sub baseExp).sub (movementChannel.mul baseExp)
  have incrementChannel' : Channel (fun index =>
      (inner.certificate index).output -
        (inner.certificate index).base) :=
    movementChannel.map (by intro index; rfl)
  have baseChannel' : Channel (fun index => (certificates index).base) :=
    baseExp.map (by intro index; rfl)
  have outputChannel' : Channel (fun index => (certificates index).output) :=
    outputExp.map (by intro index; rfl)
  have slopeChannel' : Channel (fun index => (certificates index).slope) :=
    baseExp.map (by intro index; rfl)
  have remainderChannel' :
      Channel (fun index => (certificates index).remainder) :=
    remainderChannel.map (by intro index; rfl)
  exact CCL.ProgressiveQuadraticTrace.Trace.ofTransport
    (transportOfChannels incrementChannel' baseChannel' outputChannel'
      slopeChannel' remainderChannel')

@[simp] theorem exponentialOuterTrace_certificate
    {increment : Nat → Gaussian} (inner : Trace increment)
    (baseUnit : ∀ index, normSq (inner.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1)
    (index : Nat) :
    (exponentialOuterTrace inner baseUnit movementUnit).certificate index =
      CCL.QuadraticJet.Certificate.exponential
        (baseUnit index) (movementUnit index) index := rfl

/-- Local exponential with automatically synthesized quadratic transport. -/
def exponentialAutomatic {increment : Nat → Gaussian}
    (inner : Trace increment)
    (baseUnit : ∀ index, normSq (inner.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1) :
    Trace increment :=
  composeAutomatic inner
    (exponentialOuterTrace inner baseUnit movementUnit) incrementUnit

@[simp] theorem exponentialAutomatic_certificate
    {increment : Nat → Gaussian} (inner : Trace increment)
    (baseUnit : ∀ index, normSq (inner.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1)
    (index : Nat) :
    CCL.ProgressiveQuadraticTrace.Trace.certificate
        (exponentialAutomatic inner baseUnit movementUnit incrementUnit)
        index =
      (inner.certificate index).compose
        (CCL.QuadraticJet.Certificate.exponential
          (baseUnit index) (movementUnit index) index)
        (incrementUnit index) := rfl

theorem exponentialAutomatic_bitstream_and_quadratic_law
    {increment : Nat → Gaussian} (inner : Trace increment)
    (baseUnit : ∀ index, normSq (inner.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1)
    (current : Nat) (target : Coordinate) (positive : 0 < target)
    (count : Nat) :
    CCL.ProgressiveQuadraticTrace.Trace.RequestContract
      (exponentialAutomatic inner baseUnit movementUnit incrementUnit)
      current target positive count :=
  CCL.ProgressiveQuadraticTrace.Trace.bitstream_and_quadratic_law
    (exponentialAutomatic inner baseUnit movementUnit incrementUnit)
    current target positive count

private def reducedLogSlope : Gaussian :=
  CCL.FiniteComplexLog.scalar 2

private theorem reducedLogSample_zero (index : Nat) :
    CCL.FiniteComplexLog.sample 0 index = 0 := by
  rw [CCL.FiniteComplexLog.sample_eq,
    CCL.FiniteComplexLog.outputFactor_eq]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteComplexLog.scalar,
      mul_re, mul_im, zero_re, zero_im] <;> ring1

/-- One exact finite quadratic certificate for the reduced complex-log
sample.  The exact rational remainder ratio is recorded at every displayed
stage; no limiting derivative is postulated. -/
def reducedLogCertificate (increment : Gaussian)
    (_disk : normSq increment ≤ 1 / 9) (index : Nat) :
    Certificate increment :=
  CCL.QuadraticJet.Certificate.ofExpansion
    increment 0 reducedLogSlope
    (CCL.FiniteComplexLog.sample increment (index + 1))
    (CCL.FiniteComplexLog.sample increment (index + 1) -
      0 - increment * reducedLogSlope)
    rfl (by
      intro zero
      subst increment
      rw [reducedLogSample_zero, sub_self,
        RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.zero_sub]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [neg_re, neg_im, zero_re, zero_im] <;> ring1)

/-- The reduced complex-log primitive, including its finite input
sensitivity, is itself a semantic quadratic trace. -/
def reducedLogOuterTrace {source : Nat → Gaussian}
    (sourceChannel : Channel source)
    (disk : ∀ index, normSq (source index) ≤ 1 / 9) : Trace source := by
  let certificates := fun index =>
    reducedLogCertificate (source index) (disk index) index
  let baseChannel := Channel.exact 0
  let slopeChannel := Channel.exact reducedLogSlope
  let outputChannel := sourceChannel.reducedLogSample disk
  let remainderChannel :=
    (outputChannel.sub baseChannel).sub (sourceChannel.mul slopeChannel)
  have baseChannel' : Channel (fun index => (certificates index).base) :=
    baseChannel.map (by intro index; rfl)
  have outputChannel' : Channel (fun index => (certificates index).output) :=
    outputChannel.map (by intro index; rfl)
  have slopeChannel' : Channel (fun index => (certificates index).slope) :=
    slopeChannel.map (by intro index; rfl)
  have remainderChannel' :
      Channel (fun index => (certificates index).remainder) :=
    remainderChannel.map (by intro index; rfl)
  exact CCL.ProgressiveQuadraticTrace.Trace.ofTransport
    (transportOfChannels sourceChannel baseChannel' outputChannel'
      slopeChannel' remainderChannel')

@[simp] theorem reducedLogOuterTrace_certificate
    {source : Nat → Gaussian} (sourceChannel : Channel source)
    (disk : ∀ index, normSq (source index) ≤ 1 / 9) (index : Nat) :
    (reducedLogOuterTrace sourceChannel disk).certificate index =
      reducedLogCertificate (source index) (disk index) index := rfl

/-- Compose the reduced complex-log primitive with a semantic inner trace.
This is the local explicitly charted logarithm constructor; an anchored branch
correction may subsequently be added as a constant trace. -/
def reducedLogAutomatic {increment : Nat → Gaussian}
    (inner : Trace increment)
    (movementDisk : ∀ index,
      normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1 / 9)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1) :
    Trace increment :=
  let movementChannel := inner.outputField.sub inner.baseField
  composeAutomatic inner
    (reducedLogOuterTrace movementChannel movementDisk) incrementUnit

@[simp] theorem reducedLogAutomatic_certificate
    {increment : Nat → Gaussian} (inner : Trace increment)
    (movementDisk : ∀ index,
      normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1 / 9)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1)
    (index : Nat) :
    CCL.ProgressiveQuadraticTrace.Trace.certificate
        (reducedLogAutomatic inner movementDisk incrementUnit) index =
      (inner.certificate index).compose
        (reducedLogCertificate
          ((inner.certificate index).output -
            (inner.certificate index).base)
          (movementDisk index) index)
        (incrementUnit index) := rfl

theorem reducedLogAutomatic_bitstream_and_quadratic_law
    {increment : Nat → Gaussian} (inner : Trace increment)
    (movementDisk : ∀ index,
      normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1 / 9)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1)
    (current : Nat) (target : Coordinate) (positive : 0 < target)
    (count : Nat) :
    CCL.ProgressiveQuadraticTrace.Trace.RequestContract
      (reducedLogAutomatic inner movementDisk incrementUnit)
      current target positive count :=
  CCL.ProgressiveQuadraticTrace.Trace.bitstream_and_quadratic_law
    (reducedLogAutomatic inner movementDisk incrementUnit)
    current target positive count

/-- The semantic trace for multiplication of the represented calculation by
the displayed imaginary unit. -/
def rotateAutomatic {increment : Nat → Gaussian} (inner : Trace increment) :
    Trace increment :=
  scaleAutomatic CCL.Trigonometric.imaginaryUnit inner

/-- Local sine assembled from the two automatically transported exponential
traces.  The only premises are the explicit finite unit-disk certificates of
the local exponential chart. -/
def sineAutomatic {increment : Nat → Gaussian} (inner : Trace increment)
    (rotatedBaseUnit : ∀ index,
      normSq ((rotateAutomatic inner).certificate index).base ≤ 1)
    (rotatedMovementUnit : ∀ index,
      normSq (((rotateAutomatic inner).certificate index).output -
        ((rotateAutomatic inner).certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1) :
    Trace increment := by
  let rotated := rotateAutomatic inner
  let negativeRotated := CCL.ProgressiveQuadraticTrace.Trace.neg
    rotated
  have negativeBaseUnit : ∀ index,
      normSq (negativeRotated.certificate index).base ≤ 1 := by
    intro index
    change normSq (-(rotated.certificate index).base) ≤ 1
    rw [normSq_neg]
    exact rotatedBaseUnit index
  have negativeMovementUnit : ∀ index,
      normSq ((negativeRotated.certificate index).output -
        (negativeRotated.certificate index).base) ≤ 1 := by
    intro index
    change normSq
      (-(rotated.certificate index).output -
        -(rotated.certificate index).base) ≤ 1
    have identity :
        -(rotated.certificate index).output -
            -(rotated.certificate index).base =
          -((rotated.certificate index).output -
            (rotated.certificate index).base) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [neg_re, neg_im, sub_re, sub_im] <;> ring1
    rw [identity, normSq_neg]
    exact rotatedMovementUnit index
  let positivePhase := exponentialAutomatic rotated rotatedBaseUnit
    rotatedMovementUnit incrementUnit
  let negativePhase := exponentialAutomatic negativeRotated negativeBaseUnit
    negativeMovementUnit incrementUnit
  exact scaleAutomatic CCL.Trigonometric.inverseTwoI
    (CCL.ProgressiveQuadraticTrace.Trace.add positivePhase
      (CCL.ProgressiveQuadraticTrace.Trace.neg negativePhase))

/-- Local cosine assembled from the same two finite exponential traces. -/
def cosineAutomatic {increment : Nat → Gaussian} (inner : Trace increment)
    (rotatedBaseUnit : ∀ index,
      normSq ((rotateAutomatic inner).certificate index).base ≤ 1)
    (rotatedMovementUnit : ∀ index,
      normSq (((rotateAutomatic inner).certificate index).output -
        ((rotateAutomatic inner).certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1) :
    Trace increment := by
  let rotated := rotateAutomatic inner
  let negativeRotated := CCL.ProgressiveQuadraticTrace.Trace.neg
    rotated
  have negativeBaseUnit : ∀ index,
      normSq (negativeRotated.certificate index).base ≤ 1 := by
    intro index
    change normSq (-(rotated.certificate index).base) ≤ 1
    rw [normSq_neg]
    exact rotatedBaseUnit index
  have negativeMovementUnit : ∀ index,
      normSq ((negativeRotated.certificate index).output -
        (negativeRotated.certificate index).base) ≤ 1 := by
    intro index
    change normSq
      (-(rotated.certificate index).output -
        -(rotated.certificate index).base) ≤ 1
    have identity :
        -(rotated.certificate index).output -
            -(rotated.certificate index).base =
          -((rotated.certificate index).output -
            (rotated.certificate index).base) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [neg_re, neg_im, sub_re, sub_im] <;> ring1
    rw [identity, normSq_neg]
    exact rotatedMovementUnit index
  let positivePhase := exponentialAutomatic rotated rotatedBaseUnit
    rotatedMovementUnit incrementUnit
  let negativePhase := exponentialAutomatic negativeRotated negativeBaseUnit
    negativeMovementUnit incrementUnit
  exact scaleAutomatic CCL.Trigonometric.half
    (CCL.ProgressiveQuadraticTrace.Trace.add positivePhase
      negativePhase)

theorem sineAutomatic_bitstream_and_quadratic_law
    {increment : Nat → Gaussian} (inner : Trace increment)
    (rotatedBaseUnit : ∀ index,
      normSq ((rotateAutomatic inner).certificate index).base ≤ 1)
    (rotatedMovementUnit : ∀ index,
      normSq (((rotateAutomatic inner).certificate index).output -
        ((rotateAutomatic inner).certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1)
    (current : Nat) (target : Coordinate) (positive : 0 < target)
    (count : Nat) :
    CCL.ProgressiveQuadraticTrace.Trace.RequestContract
      (sineAutomatic inner rotatedBaseUnit rotatedMovementUnit incrementUnit)
      current target positive count :=
  CCL.ProgressiveQuadraticTrace.Trace.bitstream_and_quadratic_law
    (sineAutomatic inner rotatedBaseUnit rotatedMovementUnit incrementUnit)
    current target positive count

theorem cosineAutomatic_bitstream_and_quadratic_law
    {increment : Nat → Gaussian} (inner : Trace increment)
    (rotatedBaseUnit : ∀ index,
      normSq ((rotateAutomatic inner).certificate index).base ≤ 1)
    (rotatedMovementUnit : ∀ index,
      normSq (((rotateAutomatic inner).certificate index).output -
        ((rotateAutomatic inner).certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1)
    (current : Nat) (target : Coordinate) (positive : 0 < target)
    (count : Nat) :
    CCL.ProgressiveQuadraticTrace.Trace.RequestContract
      (cosineAutomatic inner rotatedBaseUnit rotatedMovementUnit incrementUnit)
      current target positive count :=
  CCL.ProgressiveQuadraticTrace.Trace.bitstream_and_quadratic_law
    (cosineAutomatic inner rotatedBaseUnit rotatedMovementUnit incrementUnit)
    current target positive count

/-- Reciprocal with all geometric transport synthesized from two displayed
positive lower quadrances, one for the base samples and one for the output
samples. -/
def reciprocalAutomatic {increment : Nat → Gaussian} (trace : Trace increment)
    (baseLower outputLower : Coordinate)
    (baseLowerPositive : 0 < baseLower)
    (outputLowerPositive : 0 < outputLower)
    (baseApart : ∀ index,
      baseLower ≤ normSq (trace.certificate index).base)
    (outputApart : ∀ index,
      outputLower ≤ normSq (trace.certificate index).output) :
    Trace increment := by
  let baseNonzero : ∀ index, (trace.certificate index).base ≠ 0 := by
    intro index zero
    have bound := baseApart index
    rw [zero, normSq_zero] at bound
    exact (not_le_of_gt baseLowerPositive) bound
  let outputNonzero : ∀ index, (trace.certificate index).output ≠ 0 := by
    intro index zero
    have bound := outputApart index
    rw [zero, normSq_zero] at bound
    exact (not_le_of_gt outputLowerPositive) bound
  let certificates := fun index =>
    (trace.certificate index).reciprocal (baseNonzero index)
      (outputNonzero index)
  let incrementChannel := trace.incrementField
  let baseInverse := trace.baseField.reciprocal baseLower baseLowerPositive
    baseApart
  let outputInverse := trace.outputField.reciprocal outputLower
    outputLowerPositive outputApart
  let slopeChannel :=
    (trace.slopeField.mul (baseInverse.mul baseInverse)).neg
  let remainderChannel :=
    (outputInverse.sub baseInverse).sub (incrementChannel.mul slopeChannel)
  have baseChannel' : Channel (fun index => (certificates index).base) :=
    baseInverse.map (by
      intro index
      change (trace.certificate index).base⁻¹ =
        inv (trace.certificate index).base
      exact inv_eq _)
  have outputChannel' : Channel (fun index => (certificates index).output) :=
    outputInverse.map (by
      intro index
      change (trace.certificate index).output⁻¹ =
        inv (trace.certificate index).output
      exact inv_eq _)
  have slopeChannel' : Channel (fun index => (certificates index).slope) :=
    slopeChannel.map (by
      intro index
      change
        -((trace.certificate index).slope *
            ((trace.certificate index).base⁻¹ *
              (trace.certificate index).base⁻¹)) =
          -((trace.certificate index).slope *
            (inv (trace.certificate index).base *
              inv (trace.certificate index).base))
      simp only [inv_eq])
  have remainderChannel' :
      Channel (fun index => (certificates index).remainder) :=
    remainderChannel.map (by
      intro index
      change
        (trace.certificate index).output⁻¹ -
            (trace.certificate index).base⁻¹ - increment index *
              -((trace.certificate index).slope *
                ((trace.certificate index).base⁻¹ *
                  (trace.certificate index).base⁻¹)) =
          inv (trace.certificate index).output -
            inv (trace.certificate index).base - increment index *
              -((trace.certificate index).slope *
                (inv (trace.certificate index).base *
                  inv (trace.certificate index).base))
      simp only [inv_eq])
  exact CCL.ProgressiveQuadraticTrace.Trace.ofTransport
    (transportOfChannels incrementChannel baseChannel' outputChannel'
      slopeChannel' remainderChannel')

@[simp] theorem reciprocalAutomatic_certificate
    {increment : Nat → Gaussian} (trace : Trace increment)
    (baseLower outputLower : Coordinate)
    (baseLowerPositive : 0 < baseLower)
    (outputLowerPositive : 0 < outputLower)
    (baseApart : ∀ index,
      baseLower ≤ normSq (trace.certificate index).base)
    (outputApart : ∀ index,
      outputLower ≤ normSq (trace.certificate index).output)
    (index : Nat) :
    (reciprocalAutomatic trace baseLower outputLower baseLowerPositive
      outputLowerPositive baseApart outputApart).certificate index =
      (trace.certificate index).reciprocal
        (by
          intro zero
          have bound := baseApart index
          rw [zero, normSq_zero] at bound
          exact (not_le_of_gt baseLowerPositive) bound)
        (by
          intro zero
          have bound := outputApart index
          rw [zero, normSq_zero] at bound
          exact (not_le_of_gt outputLowerPositive) bound) := rfl

/-- Division is automatic multiplication by the apartness-certified
automatic reciprocal. -/
def divAutomatic {increment : Nat → Gaussian}
    (numerator denominator : Trace increment)
    (baseLower outputLower : Coordinate)
    (baseLowerPositive : 0 < baseLower)
    (outputLowerPositive : 0 < outputLower)
    (baseApart : ∀ index,
      baseLower ≤ normSq (denominator.certificate index).base)
    (outputApart : ∀ index,
      outputLower ≤ normSq (denominator.certificate index).output) :
    Trace increment :=
  mulAutomatic numerator
    (reciprocalAutomatic denominator baseLower outputLower baseLowerPositive
      outputLowerPositive baseApart outputApart)

theorem divAutomatic_bitstream_and_quadratic_law
    {increment : Nat → Gaussian}
    (numerator denominator : Trace increment)
    (baseLower outputLower : Coordinate)
    (baseLowerPositive : 0 < baseLower)
    (outputLowerPositive : 0 < outputLower)
    (baseApart : ∀ index,
      baseLower ≤ normSq (denominator.certificate index).base)
    (outputApart : ∀ index,
      outputLower ≤ normSq (denominator.certificate index).output)
    (current : Nat) (target : Coordinate) (positive : 0 < target)
    (count : Nat) :
    CCL.ProgressiveQuadraticTrace.Trace.RequestContract
      (divAutomatic numerator denominator baseLower outputLower
        baseLowerPositive outputLowerPositive baseApart outputApart)
      current target positive count :=
  CCL.ProgressiveQuadraticTrace.Trace.bitstream_and_quadratic_law
    (divAutomatic numerator denominator baseLower outputLower
      baseLowerPositive outputLowerPositive baseApart outputApart)
    current target positive count

end Trace

abbrev FirstJet := CCL.ProgressiveQuadraticTrace.FirstJet

namespace FirstJet

def scaleAutomatic (scalar : Gaussian) {increment : Nat → Gaussian}
    (jet : FirstJet increment) : FirstJet increment :=
  ⟨Trace.scaleAutomatic scalar jet.trace⟩

def mulAutomatic {increment : Nat → Gaussian}
    (left right : FirstJet increment) : FirstJet increment :=
  ⟨Trace.mulAutomatic left.trace right.trace⟩

def reciprocalAutomatic {increment : Nat → Gaussian}
    (jet : FirstJet increment) (baseLower outputLower : Coordinate)
    (baseLowerPositive : 0 < baseLower)
    (outputLowerPositive : 0 < outputLower)
    (baseApart : ∀ index,
      baseLower ≤ normSq (jet.trace.certificate index).base)
    (outputApart : ∀ index,
      outputLower ≤ normSq (jet.trace.certificate index).output) :
    FirstJet increment :=
  ⟨Trace.reciprocalAutomatic jet.trace baseLower outputLower
    baseLowerPositive outputLowerPositive baseApart outputApart⟩

def divAutomatic {increment : Nat → Gaussian}
    (numerator denominator : FirstJet increment)
    (baseLower outputLower : Coordinate)
    (baseLowerPositive : 0 < baseLower)
    (outputLowerPositive : 0 < outputLower)
    (baseApart : ∀ index,
      baseLower ≤ normSq (denominator.trace.certificate index).base)
    (outputApart : ∀ index,
      outputLower ≤ normSq (denominator.trace.certificate index).output) :
    FirstJet increment :=
  ⟨Trace.divAutomatic numerator.trace denominator.trace baseLower outputLower
    baseLowerPositive outputLowerPositive baseApart outputApart⟩

def composeAutomatic {increment : Nat → Gaussian}
    (inner : FirstJet increment)
    (outer : FirstJet (fun index =>
      (inner.trace.certificate index).output -
        (inner.trace.certificate index).base))
    (unit : ∀ index, normSq (increment index) ≤ 1) : FirstJet increment :=
  ⟨Trace.composeAutomatic inner.trace outer.trace unit⟩

def exponentialAutomatic {increment : Nat → Gaussian}
    (inner : FirstJet increment)
    (baseUnit : ∀ index,
      normSq (inner.trace.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      normSq ((inner.trace.certificate index).output -
        (inner.trace.certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1) :
    FirstJet increment :=
  ⟨Trace.exponentialAutomatic inner.trace baseUnit movementUnit incrementUnit⟩

def reducedLogAutomatic {increment : Nat → Gaussian}
    (inner : FirstJet increment)
    (movementDisk : ∀ index,
      normSq ((inner.trace.certificate index).output -
        (inner.trace.certificate index).base) ≤ 1 / 9)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1) :
    FirstJet increment :=
  ⟨Trace.reducedLogAutomatic inner.trace movementDisk incrementUnit⟩

def sineAutomatic {increment : Nat → Gaussian}
    (inner : FirstJet increment)
    (rotatedBaseUnit : ∀ index,
      normSq ((Trace.rotateAutomatic inner.trace).certificate index).base ≤ 1)
    (rotatedMovementUnit : ∀ index,
      normSq (((Trace.rotateAutomatic inner.trace).certificate index).output -
        ((Trace.rotateAutomatic inner.trace).certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1) :
    FirstJet increment :=
  ⟨Trace.sineAutomatic inner.trace rotatedBaseUnit rotatedMovementUnit
    incrementUnit⟩

def cosineAutomatic {increment : Nat → Gaussian}
    (inner : FirstJet increment)
    (rotatedBaseUnit : ∀ index,
      normSq ((Trace.rotateAutomatic inner.trace).certificate index).base ≤ 1)
    (rotatedMovementUnit : ∀ index,
      normSq (((Trace.rotateAutomatic inner.trace).certificate index).output -
        ((Trace.rotateAutomatic inner.trace).certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1) :
    FirstJet increment :=
  ⟨Trace.cosineAutomatic inner.trace rotatedBaseUnit rotatedMovementUnit
    incrementUnit⟩

end FirstJet

end CCL.ProgressiveAutomaticQuadraticTrace
