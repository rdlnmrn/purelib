import mathlib.Tactic.QuotientFreeRing
import CCL.Progressive.PersistentTable

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

namespace CCL.ProgressiveQuadraticTrace

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Approximation :=
  CCL.ProgressiveApproximation.Approximation
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed
abbrev Certificate := CCL.QuadraticJet.Certificate
abbrev ChannelCursor :=
  CCL.ProgressivePersistentTable.ChannelCursor
abbrev TableCursor :=
  CCL.ProgressivePersistentTable.TableCursor

open RFAP.ConstructiveGaussian.Gaussian

/-- One common-modulus sequence of exact quadratic calculations. -/
structure Trace (increment : Nat → Gaussian) where
  certificate : (index : Nat) → Certificate (increment index)
  errorScale : Coordinate
  errorScale_nonneg : 0 ≤ errorScale
  increment_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    normSq (increment later - increment earlier) ≤
      CCL.FiniteGeometric.quarterRadius errorScale earlier
  base_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    normSq ((certificate later).base - (certificate earlier).base) ≤
      CCL.FiniteGeometric.quarterRadius errorScale earlier
  output_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    normSq ((certificate later).output - (certificate earlier).output) ≤
      CCL.FiniteGeometric.quarterRadius errorScale earlier
  slope_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    normSq ((certificate later).slope - (certificate earlier).slope) ≤
      CCL.FiniteGeometric.quarterRadius errorScale earlier
  remainder_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    normSq ((certificate later).remainder -
      (certificate earlier).remainder) ≤
        CCL.FiniteGeometric.quarterRadius errorScale earlier
  centerBound : Coordinate
  centerBound_nonneg : 0 ≤ centerBound
  increment_bounded : ∀ index, normSq (increment index) ≤ centerBound
  base_bounded : ∀ index, normSq (certificate index).base ≤ centerBound
  output_bounded : ∀ index, normSq (certificate index).output ≤ centerBound
  slope_bounded : ∀ index, normSq (certificate index).slope ≤ centerBound
  remainder_bounded : ∀ index,
    normSq (certificate index).remainder ≤ centerBound

namespace Trace

def projectionApproximation {increment : Nat → Gaussian}
    (trace : Trace increment) (sample : Nat → Gaussian)
    (later_close : ∀ {earlier later : Nat}, earlier ≤ later →
      normSq (sample later - sample earlier) ≤
        CCL.FiniteGeometric.quarterRadius trace.errorScale earlier)
    (bounded : ∀ index, normSq (sample index) ≤ trace.centerBound) :
    Approximation where
  sample := sample
  radiusSq := CCL.FiniteGeometric.quarterRadius trace.errorScale
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      trace.errorScale_nonneg
  later_close := later_close
  refineIndex current target _positive :=
    CCL.FiniteGeometric.firstQuarterBelow trace.errorScale
      current target
  refineIndex_ge := by
    intro current target _positive
    exact CCL.FiniteGeometric.firstQuarterBelow_ge
      trace.errorScale current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate
      trace.errorScale trace.errorScale_nonneg
  centerBound := trace.centerBound
  centerBound_nonneg := trace.centerBound_nonneg
  sample_bounded := bounded

def incrementApproximation {increment : Nat → Gaussian}
    (trace : Trace increment) : Approximation :=
  trace.projectionApproximation increment trace.increment_later_close
    trace.increment_bounded

def baseApproximation {increment : Nat → Gaussian}
    (trace : Trace increment) : Approximation :=
  trace.projectionApproximation (fun index => (trace.certificate index).base)
    trace.base_later_close trace.base_bounded

def outputApproximation {increment : Nat → Gaussian}
    (trace : Trace increment) : Approximation :=
  trace.projectionApproximation (fun index => (trace.certificate index).output)
    trace.output_later_close trace.output_bounded

def slopeApproximation {increment : Nat → Gaussian}
    (trace : Trace increment) : Approximation :=
  trace.projectionApproximation (fun index => (trace.certificate index).slope)
    trace.slope_later_close trace.slope_bounded

def remainderApproximation {increment : Nat → Gaussian}
    (trace : Trace increment) : Approximation :=
  trace.projectionApproximation
    (fun index => (trace.certificate index).remainder)
    trace.remainder_later_close trace.remainder_bounded

def incrementChannel {increment : Nat → Gaussian}
    (trace : Trace increment) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
    trace.incrementApproximation

def baseChannel {increment : Nat → Gaussian}
    (trace : Trace increment) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
    trace.baseApproximation

def outputChannel {increment : Nat → Gaussian}
    (trace : Trace increment) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
    trace.outputApproximation

def slopeChannel {increment : Nat → Gaussian}
    (trace : Trace increment) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
    trace.slopeApproximation

def remainderChannel {increment : Nat → Gaussian}
    (trace : Trace increment) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
    trace.remainderApproximation

def channels {increment : Nat → Gaussian}
    (trace : Trace increment) : List CoherentNamed :=
  [trace.incrementChannel, trace.baseChannel, trace.outputChannel,
    trace.slopeChannel, trace.remainderChannel]

def requestIndex {increment : Nat → Gaussian} (trace : Trace increment)
    (current : Nat) (target : Coordinate) : Nat :=
  CCL.FiniteGeometric.firstQuarterBelow trace.errorScale
    current target

theorem requestIndex_ge {increment : Nat → Gaussian}
    (trace : Trace increment) (current : Nat) (target : Coordinate) :
    current ≤ trace.requestIndex current target :=
  CCL.FiniteGeometric.firstQuarterBelow_ge
    trace.errorScale current target

theorem requestIndex_accurate {increment : Nat → Gaussian}
    (trace : Trace increment) (current : Nat) {target : Coordinate}
    (positive : 0 < target) :
    CCL.FiniteGeometric.quarterRadius trace.errorScale
      (trace.requestIndex current target) < target :=
  CCL.FiniteGeometric.firstQuarterBelow_accurate
    trace.errorScale trace.errorScale_nonneg current target positive

/-- Start every projected channel at the same trace index. -/
def incrementState {increment : Nat → Gaussian} (trace : Trace increment)
    (index : Nat) : trace.incrementChannel.name.process.State := by
  change Nat
  exact index

def baseState {increment : Nat → Gaussian} (trace : Trace increment)
    (index : Nat) : trace.baseChannel.name.process.State := by
  change Nat
  exact index

def outputState {increment : Nat → Gaussian} (trace : Trace increment)
    (index : Nat) : trace.outputChannel.name.process.State := by
  change Nat
  exact index

def slopeState {increment : Nat → Gaussian} (trace : Trace increment)
    (index : Nat) : trace.slopeChannel.name.process.State := by
  change Nat
  exact index

def remainderState {increment : Nat → Gaussian} (trace : Trace increment)
    (index : Nat) : trace.remainderChannel.name.process.State := by
  change Nat
  exact index

def cursorTableAt {increment : Nat → Gaussian} (trace : Trace increment)
    (index : Nat) : TableCursor :=
  ⟨[CCL.ProgressivePersistentTable.ChannelCursor.atState
      trace.incrementChannel (trace.incrementState index),
    CCL.ProgressivePersistentTable.ChannelCursor.atState
      trace.baseChannel (trace.baseState index),
    CCL.ProgressivePersistentTable.ChannelCursor.atState
      trace.outputChannel (trace.outputState index),
    CCL.ProgressivePersistentTable.ChannelCursor.atState
      trace.slopeChannel (trace.slopeState index),
    CCL.ProgressivePersistentTable.ChannelCursor.atState
      trace.remainderChannel (trace.remainderState index)]⟩

@[simp] theorem cursorTableAt_channels {increment : Nat → Gaussian}
    (trace : Trace increment) (index : Nat) :
    (trace.cursorTableAt index).channels = trace.channels := by
  simp only [cursorTableAt,
    CCL.ProgressivePersistentTable.TableCursor.channels,
    channels, List.map,
    CCL.ProgressivePersistentTable.ChannelCursor.atState]

/-- The five root enclosures at one common trace index all use the common
geometric allowance. -/
theorem root_radius_eq {increment : Nat → Gaussian}
    (trace : Trace increment) (index : Nat) :
    (trace.incrementApproximation.toProcess.ball index).radiusSq =
        CCL.FiniteGeometric.quarterRadius trace.errorScale index ∧
      (trace.baseApproximation.toProcess.ball index).radiusSq =
        CCL.FiniteGeometric.quarterRadius trace.errorScale index ∧
      (trace.outputApproximation.toProcess.ball index).radiusSq =
        CCL.FiniteGeometric.quarterRadius trace.errorScale index ∧
      (trace.slopeApproximation.toProcess.ball index).radiusSq =
        CCL.FiniteGeometric.quarterRadius trace.errorScale index ∧
      (trace.remainderApproximation.toProcess.ball index).radiusSq =
        CCL.FiniteGeometric.quarterRadius trace.errorScale index :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The five root centres are literally the fields of the exact certificate
at that common natural index. -/
theorem root_centers {increment : Nat → Gaussian}
    (trace : Trace increment) (index : Nat) :
    (trace.incrementApproximation.toProcess.ball index).center = increment index ∧
      (trace.baseApproximation.toProcess.ball index).center =
        (trace.certificate index).base ∧
      (trace.outputApproximation.toProcess.ball index).center =
        (trace.certificate index).output ∧
      (trace.slopeApproximation.toProcess.ball index).center =
        (trace.certificate index).slope ∧
      (trace.remainderApproximation.toProcess.ball index).center =
        (trace.certificate index).remainder :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- One finite common-index observation retains the exact quadratic identity. -/
theorem root_expansion {increment : Nat → Gaussian}
    (trace : Trace increment) (index : Nat) :
    (trace.outputApproximation.toProcess.ball index).center -
        (trace.baseApproximation.toProcess.ball index).center -
        (trace.incrementApproximation.toProcess.ball index).center *
          (trace.slopeApproximation.toProcess.ball index).center =
      (trace.remainderApproximation.toProcess.ball index).center :=
  (trace.certificate index).expansion

theorem root_remainder_le {increment : Nat → Gaussian}
    (trace : Trace increment) (index : Nat) :
    normSq (trace.remainderApproximation.toProcess.ball index).center ≤
      (trace.certificate index).factor *
        normSq (trace.incrementApproximation.toProcess.ball index).center ^ 2 :=
  (trace.certificate index).remainder_le

/-- Complete finite proposition returned by one common-index trace request. -/
def RequestContract {increment : Nat → Gaussian}
    (trace : Trace increment) (current : Nat) (target : Coordinate)
    (positive : 0 < target) (count : Nat) : Prop :=
    let index := trace.requestIndex current target
    let cursors := trace.cursorTableAt index
    (trace.incrementApproximation.toProcess.ball index).radiusSq < target ∧
      (trace.baseApproximation.toProcess.ball index).radiusSq < target ∧
      (trace.outputApproximation.toProcess.ball index).radiusSq < target ∧
      (trace.slopeApproximation.toProcess.ball index).radiusSq < target ∧
      (trace.remainderApproximation.toProcess.ball index).radiusSq < target ∧
      (trace.outputApproximation.toProcess.ball index).center -
          (trace.baseApproximation.toProcess.ball index).center -
          (trace.incrementApproximation.toProcess.ball index).center *
            (trace.slopeApproximation.toProcess.ball index).center =
        (trace.remainderApproximation.toProcess.ball index).center ∧
      normSq (trace.remainderApproximation.toProcess.ball index).center ≤
        (trace.certificate index).factor *
          normSq (trace.incrementApproximation.toProcess.ball index).center ^ 2 ∧
      ∀ entry, entry ∈ cursors.entries →
        (entry.request target positive count).cursor.machine.emitted.length =
          entry.cursor.machine.emitted.length + count

/-- End-to-end common-index request: all root enclosures lie below the same
positive rational target, the exact quadratic law holds at their displayed
centres, and every persistent CCL word grows by the requested bit count. -/
theorem bitstream_and_quadratic_law {increment : Nat → Gaussian}
    (trace : Trace increment) (current : Nat) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    RequestContract trace current target positive count := by
  let index := trace.requestIndex current target
  let cursors := trace.cursorTableAt index
  have accurate := trace.requestIndex_accurate current positive
  rcases trace.root_radius_eq index with
    ⟨incrementRadius, baseRadius, outputRadius, slopeRadius,
      remainderRadius⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, trace.root_expansion index,
    trace.root_remainder_le index, ?_⟩
  · rw [incrementRadius]
    exact accurate
  · rw [baseRadius]
    exact accurate
  · rw [outputRadius]
    exact accurate
  · rw [slopeRadius]
    exact accurate
  · rw [remainderRadius]
    exact accurate
  · intro entry member
    exact entry.request_word_length target positive count

/-! ## Exact specialization -/

def certificateBound {increment : Gaussian}
    (certificate : Certificate increment) : Coordinate :=
  normSq increment + normSq certificate.base + normSq certificate.output +
    normSq certificate.slope + normSq certificate.remainder

theorem certificateBound_nonneg {increment : Gaussian}
    (certificate : Certificate increment) :
    0 ≤ certificateBound certificate := by
  unfold certificateBound
  exact add_nonneg (add_nonneg (add_nonneg
    (add_nonneg (normSq_nonneg increment) (normSq_nonneg certificate.base))
      (normSq_nonneg certificate.output)) (normSq_nonneg certificate.slope))
    (normSq_nonneg certificate.remainder)

private theorem first_le_certificateBound {increment : Gaussian}
    (certificate : Certificate increment) :
    normSq increment ≤ certificateBound certificate := by
  unfold certificateBound
  let rest := normSq certificate.base + normSq certificate.output +
    normSq certificate.slope + normSq certificate.remainder
  have restNonnegative : 0 ≤ rest := by
    dsimp only [rest]
    exact add_nonneg (add_nonneg (add_nonneg
      (normSq_nonneg certificate.base) (normSq_nonneg certificate.output))
      (normSq_nonneg certificate.slope)) (normSq_nonneg certificate.remainder)
  calc
    normSq increment ≤ normSq increment + rest :=
      le_add_of_nonneg_right restNonnegative
    _ = normSq increment + normSq certificate.base +
        normSq certificate.output + normSq certificate.slope +
        normSq certificate.remainder := by
      dsimp only [rest]
      ring1

private theorem base_le_certificateBound {increment : Gaussian}
    (certificate : Certificate increment) :
    normSq certificate.base ≤ certificateBound certificate := by
  unfold certificateBound
  calc
    normSq certificate.base ≤ normSq increment + normSq certificate.base :=
      le_add_of_nonneg_left (normSq_nonneg increment)
    _ ≤ (normSq increment + normSq certificate.base) +
        (normSq certificate.output + normSq certificate.slope +
          normSq certificate.remainder) :=
      le_add_of_nonneg_right
        (add_nonneg (add_nonneg (normSq_nonneg certificate.output)
          (normSq_nonneg certificate.slope))
          (normSq_nonneg certificate.remainder))
    _ = _ := by ring1

private theorem output_le_certificateBound {increment : Gaussian}
    (certificate : Certificate increment) :
    normSq certificate.output ≤ certificateBound certificate := by
  unfold certificateBound
  calc
    normSq certificate.output ≤
        normSq increment + normSq certificate.base +
          normSq certificate.output :=
      le_add_of_nonneg_left
        (add_nonneg (normSq_nonneg increment) (normSq_nonneg certificate.base))
    _ ≤ (normSq increment + normSq certificate.base +
          normSq certificate.output) +
        (normSq certificate.slope + normSq certificate.remainder) :=
      le_add_of_nonneg_right
        (add_nonneg (normSq_nonneg certificate.slope)
          (normSq_nonneg certificate.remainder))
    _ = _ := by ring1

private theorem slope_le_certificateBound {increment : Gaussian}
    (certificate : Certificate increment) :
    normSq certificate.slope ≤ certificateBound certificate := by
  unfold certificateBound
  calc
    normSq certificate.slope ≤
        normSq increment + normSq certificate.base +
          normSq certificate.output + normSq certificate.slope :=
      le_add_of_nonneg_left (add_nonneg
        (add_nonneg (normSq_nonneg increment) (normSq_nonneg certificate.base))
        (normSq_nonneg certificate.output))
    _ ≤ _ := le_add_of_nonneg_right (normSq_nonneg certificate.remainder)

private theorem remainder_le_certificateBound {increment : Gaussian}
    (certificate : Certificate increment) :
    normSq certificate.remainder ≤ certificateBound certificate := by
  unfold certificateBound
  exact le_add_of_nonneg_left (add_nonneg
    (add_nonneg (add_nonneg (normSq_nonneg increment)
      (normSq_nonneg certificate.base)) (normSq_nonneg certificate.output))
    (normSq_nonneg certificate.slope))

/-- A displayed certificate becomes a constant common-modulus trace. -/
def exact {increment : Gaussian} (certificate : Certificate increment) :
    Trace (fun _ => increment) where
  certificate _ := certificate
  errorScale := 0
  errorScale_nonneg := le_rfl
  increment_later_close := by
    intro earlier later order
    rw [sub_self, normSq_zero,
      CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
      RFAP.ConstructiveFraction.zero_mul_direct]
  base_later_close := by
    intro earlier later order
    rw [sub_self, normSq_zero,
      CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
      RFAP.ConstructiveFraction.zero_mul_direct]
  output_later_close := by
    intro earlier later order
    rw [sub_self, normSq_zero,
      CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
      RFAP.ConstructiveFraction.zero_mul_direct]
  slope_later_close := by
    intro earlier later order
    rw [sub_self, normSq_zero,
      CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
      RFAP.ConstructiveFraction.zero_mul_direct]
  remainder_later_close := by
    intro earlier later order
    rw [sub_self, normSq_zero,
      CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
      RFAP.ConstructiveFraction.zero_mul_direct]
  centerBound := certificateBound certificate
  centerBound_nonneg := certificateBound_nonneg certificate
  increment_bounded _ := first_le_certificateBound certificate
  base_bounded _ := base_le_certificateBound certificate
  output_bounded _ := output_le_certificateBound certificate
  slope_bounded _ := slope_le_certificateBound certificate
  remainder_bounded _ := remainder_le_certificateBound certificate

@[simp] theorem exact_certificate {increment : Gaussian}
    (certificate : Certificate increment) (index : Nat) :
    (exact certificate).certificate index = certificate := rfl

/-! ## A genuinely changing progressive witness -/

/-- The identity calculation at one displayed increment, written with the
output field literally equal to that increment. -/
def identityCertificate (increment : Gaussian) : Certificate increment :=
  { base := 0
    slope := 1
    output := increment
    remainder := 0
    expansion := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im, zero_re, zero_im,
          one_re, one_im] <;> ring1
    factor := 0
    factor_nonneg := le_rfl
    remainder_le := by
      rw [normSq_zero, RFAP.ConstructiveFraction.zero_mul_direct] }

/-- Any approximation whose radius is one displayed geometric schedule gives
a semantic identity jet.  This constructor is useful for genuinely changing
inputs, not just terminating rational constants. -/
def identityOfGeometricApproximation (source : Approximation)
    (scale : Coordinate) (scaleNonnegative : 0 ≤ scale)
    (radius_eq : ∀ index, source.radiusSq index =
      CCL.FiniteGeometric.quarterRadius scale index) :
    Trace source.sample where
  certificate index := identityCertificate (source.sample index)
  errorScale := scale
  errorScale_nonneg := scaleNonnegative
  increment_later_close := by
    intro earlier later order
    rw [← radius_eq earlier]
    exact source.later_close order
  base_later_close := by
    intro earlier later order
    change normSq ((0 : Gaussian) - 0) ≤ _
    rw [RFAP.ConstructiveGaussian.Gaussian.sub_self, normSq_zero]
    exact CCL.FiniteGeometric.quarterRadius_nonneg
      scaleNonnegative earlier
  output_later_close := by
    intro earlier later order
    exact source.later_close order |>.trans_eq (radius_eq earlier)
  slope_later_close := by
    intro earlier later order
    change normSq ((1 : Gaussian) - 1) ≤ _
    rw [RFAP.ConstructiveGaussian.Gaussian.sub_self, normSq_zero]
    exact CCL.FiniteGeometric.quarterRadius_nonneg
      scaleNonnegative earlier
  remainder_later_close := by
    intro earlier later order
    change normSq ((0 : Gaussian) - 0) ≤ _
    rw [RFAP.ConstructiveGaussian.Gaussian.sub_self, normSq_zero]
    exact CCL.FiniteGeometric.quarterRadius_nonneg
      scaleNonnegative earlier
  centerBound := 1 + source.centerBound
  centerBound_nonneg := add_nonneg (by decide) source.centerBound_nonneg
  increment_bounded index := (source.sample_bounded index).trans
    (le_add_of_nonneg_left (by decide))
  base_bounded index := by
    change normSq (0 : Gaussian) ≤ 1 + source.centerBound
    rw [normSq_zero]
    exact add_nonneg (by decide) source.centerBound_nonneg
  output_bounded index := (source.sample_bounded index).trans
    (le_add_of_nonneg_left (by decide))
  slope_bounded index := by
    change normSq (1 : Gaussian) ≤ 1 + source.centerBound
    rw [normSq_one]
    exact le_add_of_nonneg_right source.centerBound_nonneg
  remainder_bounded index := by
    change normSq (0 : Gaussian) ≤ 1 + source.centerBound
    rw [normSq_zero]
    exact add_nonneg (by decide) source.centerBound_nonneg

def exponentialWitnessApproximation : Approximation :=
  CCL.FiniteExp.approximation ⟨1, 0⟩ (by decide)

/-- A small executable regression witness whose input observations are the
successive finite exponential Horner samples. -/
def nonterminatingIdentity :
    Trace exponentialWitnessApproximation.sample :=
  identityOfGeometricApproximation exponentialWitnessApproximation 10
    (by decide) (by intro index; rfl)

/-- The witness really changes between finite stages, so its productive CCL
contract is not merely an exact terminating rational specialization. -/
theorem nonterminatingIdentity_changes :
    exponentialWitnessApproximation.sample 0 ≠
      exponentialWitnessApproximation.sample 1 := by
  decide

theorem nonterminatingIdentity_bitstream (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    RequestContract nonterminatingIdentity 0 target positive count :=
  nonterminatingIdentity.bitstream_and_quadratic_law 0 target positive count

/-! ## Pointwise semantic closure with explicit finite transport -/

/-- The convergence and centre-bound side of a pointwise certificate
program.  Hard operations compute their exact certificates first and consume
one such finite transport record; no continuity premise is hidden. -/
structure Transport (increment : Nat → Gaussian)
    (certificates : (index : Nat) → Certificate (increment index)) where
  errorScale : Coordinate
  errorScale_nonneg : 0 ≤ errorScale
  increment_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    normSq (increment later - increment earlier) ≤
      CCL.FiniteGeometric.quarterRadius errorScale earlier
  base_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    normSq ((certificates later).base - (certificates earlier).base) ≤
      CCL.FiniteGeometric.quarterRadius errorScale earlier
  output_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    normSq ((certificates later).output - (certificates earlier).output) ≤
      CCL.FiniteGeometric.quarterRadius errorScale earlier
  slope_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    normSq ((certificates later).slope - (certificates earlier).slope) ≤
      CCL.FiniteGeometric.quarterRadius errorScale earlier
  remainder_later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    normSq ((certificates later).remainder -
      (certificates earlier).remainder) ≤
        CCL.FiniteGeometric.quarterRadius errorScale earlier
  centerBound : Coordinate
  centerBound_nonneg : 0 ≤ centerBound
  increment_bounded : ∀ index, normSq (increment index) ≤ centerBound
  base_bounded : ∀ index, normSq (certificates index).base ≤ centerBound
  output_bounded : ∀ index, normSq (certificates index).output ≤ centerBound
  slope_bounded : ∀ index, normSq (certificates index).slope ≤ centerBound
  remainder_bounded : ∀ index,
    normSq (certificates index).remainder ≤ centerBound

def ofTransport {increment : Nat → Gaussian}
    {certificates : (index : Nat) → Certificate (increment index)}
    (transport : Transport increment certificates) : Trace increment :=
  { certificate := certificates
    errorScale := transport.errorScale
    errorScale_nonneg := transport.errorScale_nonneg
    increment_later_close := transport.increment_later_close
    base_later_close := transport.base_later_close
    output_later_close := transport.output_later_close
    slope_later_close := transport.slope_later_close
    remainder_later_close := transport.remainder_later_close
    centerBound := transport.centerBound
    centerBound_nonneg := transport.centerBound_nonneg
    increment_bounded := transport.increment_bounded
    base_bounded := transport.base_bounded
    output_bounded := transport.output_bounded
    slope_bounded := transport.slope_bounded
    remainder_bounded := transport.remainder_bounded }

private theorem quarterRadius_sum_scale (left right : Coordinate)
    (index : Nat) :
    CCL.FiniteGeometric.quarterRadius
        (2 * (left + right)) index =
      2 * (CCL.FiniteGeometric.quarterRadius left index +
        CCL.FiniteGeometric.quarterRadius right index) := by
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
  ring1

private theorem sum_movement_le (laterLeft earlierLeft laterRight earlierRight :
    Gaussian) (leftRadius rightRadius : Coordinate)
    (leftClose : normSq (laterLeft - earlierLeft) ≤ leftRadius)
    (rightClose : normSq (laterRight - earlierRight) ≤ rightRadius) :
    normSq ((laterLeft + laterRight) - (earlierLeft + earlierRight)) ≤
      2 * (leftRadius + rightRadius) := by
  have identity :
      (laterLeft + laterRight) - (earlierLeft + earlierRight) =
        (laterLeft - earlierLeft) + (laterRight - earlierRight) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [add_re, add_im, sub_re, sub_im] <;> ring1
  rw [identity]
  exact (normSq_add_le_two _ _).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (add_le_add leftClose rightClose) (by decide))

private theorem sum_bounded (left right : Gaussian)
    (leftBound rightBound : Coordinate)
    (leftSmall : normSq left ≤ leftBound)
    (rightSmall : normSq right ≤ rightBound) :
    normSq (left + right) ≤ 2 * (leftBound + rightBound) :=
  (normSq_add_le_two _ _).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (add_le_add leftSmall rightSmall) (by decide))

private theorem componentRadius_le_sumScale
    (left right : Coordinate) (leftNonnegative : 0 ≤ left)
    (rightNonnegative : 0 ≤ right) :
    left ≤ 2 * (left + right) := by
  have sumNonnegative : 0 ≤ left + right :=
    add_nonneg leftNonnegative rightNonnegative
  calc
    left ≤ left + right := le_add_of_nonneg_right rightNonnegative
    _ = 1 * (left + right) :=
      (RFAP.ConstructiveFraction.one_mul _).symm
    _ ≤ 2 * (left + right) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (by decide) sumNonnegative

/-- Addition computes both the pointwise quadratic certificates and one
common geometric transport modulus. -/
def add {increment : Nat → Gaussian} (left right : Trace increment) :
    Trace increment :=
  { certificate := fun index =>
      (left.certificate index).add (right.certificate index)
    errorScale := 2 * (left.errorScale + right.errorScale)
    errorScale_nonneg :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg left.errorScale_nonneg right.errorScale_nonneg)
    increment_later_close := by
      intro earlier later order
      calc
        normSq (increment later - increment earlier) ≤
            CCL.FiniteGeometric.quarterRadius
              left.errorScale earlier := left.increment_later_close order
        _ ≤ 2 *
            (CCL.FiniteGeometric.quarterRadius
                left.errorScale earlier +
              CCL.FiniteGeometric.quarterRadius
                right.errorScale earlier) :=
          componentRadius_le_sumScale _ _
            (CCL.FiniteGeometric.quarterRadius_nonneg
              left.errorScale_nonneg earlier)
            (CCL.FiniteGeometric.quarterRadius_nonneg
              right.errorScale_nonneg earlier)
        _ = CCL.FiniteGeometric.quarterRadius
              (2 * (left.errorScale + right.errorScale)) earlier :=
          (quarterRadius_sum_scale _ _ _).symm
    base_later_close := by
      intro earlier later order
      exact (sum_movement_le _ _ _ _ _ _
        (left.base_later_close order) (right.base_later_close order)).trans_eq
          (quarterRadius_sum_scale _ _ _).symm
    output_later_close := by
      intro earlier later order
      exact (sum_movement_le _ _ _ _ _ _
        (left.output_later_close order)
        (right.output_later_close order)).trans_eq
          (quarterRadius_sum_scale _ _ _).symm
    slope_later_close := by
      intro earlier later order
      exact (sum_movement_le _ _ _ _ _ _
        (left.slope_later_close order) (right.slope_later_close order)).trans_eq
          (quarterRadius_sum_scale _ _ _).symm
    remainder_later_close := by
      intro earlier later order
      exact (sum_movement_le _ _ _ _ _ _
        (left.remainder_later_close order)
        (right.remainder_later_close order)).trans_eq
          (quarterRadius_sum_scale _ _ _).symm
    centerBound := 2 * (left.centerBound + right.centerBound)
    centerBound_nonneg :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg left.centerBound_nonneg right.centerBound_nonneg)
    increment_bounded := by
      intro index
      exact (left.increment_bounded index).trans
        (componentRadius_le_sumScale _ _ left.centerBound_nonneg
          right.centerBound_nonneg)
    base_bounded := by
      intro index
      exact sum_bounded _ _ _ _ (left.base_bounded index)
        (right.base_bounded index)
    output_bounded := by
      intro index
      exact sum_bounded _ _ _ _ (left.output_bounded index)
        (right.output_bounded index)
    slope_bounded := by
      intro index
      exact sum_bounded _ _ _ _ (left.slope_bounded index)
        (right.slope_bounded index)
    remainder_bounded := by
      intro index
      exact sum_bounded _ _ _ _ (left.remainder_bounded index)
        (right.remainder_bounded index) }

/-- Negation preserves the common modulus exactly. -/
def neg {increment : Nat → Gaussian} (trace : Trace increment) :
    Trace increment :=
  { certificate := fun index => (trace.certificate index).neg
    errorScale := trace.errorScale
    errorScale_nonneg := trace.errorScale_nonneg
    increment_later_close := trace.increment_later_close
    base_later_close := by
      intro earlier later order
      change normSq
        (-(trace.certificate later).base -
          -(trace.certificate earlier).base) ≤ _
      have identity :
          -(trace.certificate later).base -
              -(trace.certificate earlier).base =
            -((trace.certificate later).base -
              (trace.certificate earlier).base) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [neg_re, neg_im, sub_re, sub_im] <;> ring1
      rw [identity, normSq_neg]
      exact trace.base_later_close order
    output_later_close := by
      intro earlier later order
      change normSq
        (-(trace.certificate later).output -
          -(trace.certificate earlier).output) ≤ _
      have identity :
          -(trace.certificate later).output -
              -(trace.certificate earlier).output =
            -((trace.certificate later).output -
              (trace.certificate earlier).output) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [neg_re, neg_im, sub_re, sub_im] <;> ring1
      rw [identity, normSq_neg]
      exact trace.output_later_close order
    slope_later_close := by
      intro earlier later order
      change normSq
        (-(trace.certificate later).slope -
          -(trace.certificate earlier).slope) ≤ _
      have identity :
          -(trace.certificate later).slope -
              -(trace.certificate earlier).slope =
            -((trace.certificate later).slope -
              (trace.certificate earlier).slope) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [neg_re, neg_im, sub_re, sub_im] <;> ring1
      rw [identity, normSq_neg]
      exact trace.slope_later_close order
    remainder_later_close := by
      intro earlier later order
      change normSq
        (-(trace.certificate later).remainder -
          -(trace.certificate earlier).remainder) ≤ _
      have identity :
          -(trace.certificate later).remainder -
              -(trace.certificate earlier).remainder =
            -((trace.certificate later).remainder -
              (trace.certificate earlier).remainder) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [neg_re, neg_im, sub_re, sub_im] <;> ring1
      rw [identity, normSq_neg]
      exact trace.remainder_later_close order
    centerBound := trace.centerBound
    centerBound_nonneg := trace.centerBound_nonneg
    increment_bounded := trace.increment_bounded
    base_bounded := by
      intro index
      change normSq (-(trace.certificate index).base) ≤ trace.centerBound
      rw [normSq_neg]
      exact trace.base_bounded index
    output_bounded := by
      intro index
      change normSq (-(trace.certificate index).output) ≤ trace.centerBound
      rw [normSq_neg]
      exact trace.output_bounded index
    slope_bounded := by
      intro index
      change normSq (-(trace.certificate index).slope) ≤ trace.centerBound
      rw [normSq_neg]
      exact trace.slope_bounded index
    remainder_bounded := by
      intro index
      change normSq (-(trace.certificate index).remainder) ≤ trace.centerBound
      rw [normSq_neg]
      exact trace.remainder_bounded index }

def mul {increment : Nat → Gaussian} (left right : Trace increment)
    (transport : Transport increment
      (fun index => (left.certificate index).mul (right.certificate index))) :
    Trace increment :=
  ofTransport transport

def reciprocal {increment : Nat → Gaussian} (trace : Trace increment)
    (baseNonzero : ∀ index, (trace.certificate index).base ≠ 0)
    (outputNonzero : ∀ index, (trace.certificate index).output ≠ 0)
    (transport : Transport increment
      (fun index => (trace.certificate index).reciprocal
        (baseNonzero index) (outputNonzero index))) : Trace increment :=
  ofTransport transport

def div {increment : Nat → Gaussian} (numerator denominator : Trace increment)
    (baseNonzero : ∀ index, (denominator.certificate index).base ≠ 0)
    (outputNonzero : ∀ index, (denominator.certificate index).output ≠ 0)
    (transport : Transport increment
      (fun index => (numerator.certificate index).div
        (denominator.certificate index) (baseNonzero index)
          (outputNonzero index))) : Trace increment :=
  ofTransport transport

def compose {increment : Nat → Gaussian} (inner : Trace increment)
    (outer : (index : Nat) →
      Certificate ((inner.certificate index).output -
        (inner.certificate index).base))
    (unit : ∀ index, normSq (increment index) ≤ 1)
    (transport : Transport increment
      (fun index => (inner.certificate index).compose (outer index)
        (unit index))) : Trace increment :=
  ofTransport transport

def exponential {increment : Nat → Gaussian} (inner : Trace increment)
    (baseUnit : ∀ index, normSq (inner.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1)
    (transport : Transport increment
      (fun index => (inner.certificate index).compose
        (CCL.QuadraticJet.Certificate.exponential
          (baseUnit index) (movementUnit index) index)
        (incrementUnit index))) : Trace increment :=
  ofTransport transport

def logarithm1p {increment : Nat → Gaussian} (inner : Trace increment)
    (movementDisk : ∀ index,
      normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1 / 4)
    (incrementUnit : ∀ index, normSq (increment index) ≤ 1)
    (transport : Transport increment
      (fun index => (inner.certificate index).compose
        (CCL.QuadraticJet.Certificate.logarithm1p
          (movementDisk index) index)
        (incrementUnit index))) : Trace increment :=
  ofTransport transport

@[simp] theorem add_certificate {increment : Nat → Gaussian}
    (left right : Trace increment) (index : Nat) :
    (add left right).certificate index =
      (left.certificate index).add (right.certificate index) := rfl

@[simp] theorem mul_certificate {increment : Nat → Gaussian}
    (left right : Trace increment)
    (transport : Transport increment
      (fun index => (left.certificate index).mul (right.certificate index)))
    (index : Nat) :
    (mul left right transport).certificate index =
      (left.certificate index).mul (right.certificate index) := rfl

@[simp] theorem compose_certificate {increment : Nat → Gaussian}
    (inner : Trace increment)
    (outer : (index : Nat) →
      Certificate ((inner.certificate index).output -
        (inner.certificate index).base))
    (unit : ∀ index, normSq (increment index) ≤ 1)
    (transport : Transport increment
      (fun index => (inner.certificate index).compose (outer index)
        (unit index))) (index : Nat) :
    (compose inner outer unit transport).certificate index =
      (inner.certificate index).compose (outer index) (unit index) := rfl

end Trace

/-- A semantic first jet is a common-modulus quadratic trace.  Its value and
slope channels are projections of that trace; unlike the older provenance
pair, callers cannot insert two unrelated coherent names. -/
structure FirstJet (increment : Nat → Gaussian) where
  trace : Trace increment

namespace FirstJet

def value {increment : Nat → Gaussian} (jet : FirstJet increment) :
    CoherentNamed := jet.trace.outputChannel

def slope {increment : Nat → Gaussian} (jet : FirstJet increment) :
    CoherentNamed := jet.trace.slopeChannel

def remainder {increment : Nat → Gaussian} (jet : FirstJet increment) :
    CoherentNamed := jet.trace.remainderChannel

def exact {increment : Gaussian} (certificate : Certificate increment) :
    FirstJet (fun _ => increment) :=
  ⟨Trace.exact certificate⟩

def add {increment : Nat → Gaussian} (left right : FirstJet increment)
    : FirstJet increment :=
  ⟨Trace.add left.trace right.trace⟩

def neg {increment : Nat → Gaussian} (jet : FirstJet increment) :
    FirstJet increment :=
  ⟨Trace.neg jet.trace⟩

def mul {increment : Nat → Gaussian} (left right : FirstJet increment)
    (transport : Trace.Transport increment
      (fun index => (left.trace.certificate index).mul
        (right.trace.certificate index))) : FirstJet increment :=
  ⟨Trace.mul left.trace right.trace transport⟩

def compose {increment : Nat → Gaussian} (inner : FirstJet increment)
    (outer : (index : Nat) →
      Certificate ((inner.trace.certificate index).output -
        (inner.trace.certificate index).base))
    (unit : ∀ index, normSq (increment index) ≤ 1)
    (transport : Trace.Transport increment
      (fun index => (inner.trace.certificate index).compose (outer index)
        (unit index))) : FirstJet increment :=
  ⟨Trace.compose inner.trace outer unit transport⟩

/-- The public request theorem for a genuinely semantic progressive first
jet, including its persistent value, slope, and remainder digit emitters. -/
theorem bitstream_and_quadratic_law {increment : Nat → Gaussian}
    (jet : FirstJet increment) (current : Nat) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    Trace.RequestContract jet.trace current target positive count :=
  jet.trace.bitstream_and_quadratic_law current target positive count

end FirstJet

end CCL.ProgressiveQuadraticTrace
