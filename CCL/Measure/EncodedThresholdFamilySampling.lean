import mathlib.Data.ConstructiveList
import CCL.Measure.EncodedThresholdSampling
import CCL.Measure.EncodedSquaredStability
import FiniteMeasure.SamplingFamily

/-!
# Simultaneous finite CCL threshold-frequency estimation

One finite iid sample of a compatible realization table can estimate a
displayed list of chordal threshold probabilities simultaneously.  A common
positive witness margin identifies each encoded threshold probability with
the exact probability computed from the original affine Gaussian inputs.
The result is a finite survival-function grid certificate; no continuum of
thresholds or infinite sample stream is introduced.
-/

namespace CCL.FiniteMeasure

/-- Displayed family of chordal upper-threshold events for one compatible
realization table. -/
def encodedChordalOmegaThresholdEvents {index : Type}
    (points : index → Proj) (thresholds : List Coordinate) :
    List (index → Bool) :=
  thresholds.map fun threshold =>
    _root_.FiniteMeasure.atLeastEvent threshold fun item =>
      chordalOmegaProbe (points item)

/-- Shared sample count for every chordal threshold in a displayed grid. -/
def requiredEncodedChordalOmegaThresholdGridSampleCount {index : Type}
    (points : index → Proj) (thresholds : List Coordinate)
    (tolerance failure : Coordinate) : Nat :=
  _root_.FiniteMeasure.Distribution.requiredEventFamilyFrequencySampleCount
    (encodedChordalOmegaThresholdEvents points thresholds) tolerance failure

/-- One executable union records whether any displayed encoded threshold
frequency has squared error at least the requested squared tolerance. -/
def encodedChordalOmegaThresholdGridDeviation {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (points : index → Proj) (thresholds : List Coordinate)
    (count : Nat) (tolerance : Coordinate) : List index → Bool :=
  _root_.FiniteMeasure.Distribution.simultaneousEventFrequencyDeviation
    distribution (encodedChordalOmegaThresholdEvents points thresholds)
      count tolerance

/-- Pointwise target meaning of an accurate encoded threshold grid: every
sample frequency estimates the corresponding exact affine-input threshold
probability. -/
def EncodedChordalOmegaThresholdGridTargetAccurate {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac) (points : index → Proj)
    (thresholds : List Coordinate) (count : Nat)
    (tolerance : Coordinate) (sample : List index) : Prop :=
  ∀ threshold, threshold ∈ thresholds →
    (_root_.FiniteMeasure.Distribution.eventFrequency count
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          chordalOmegaProbe (points item)) sample -
      distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          chordalOmegaProbe
            (CCL.Proj.affine (fraction item).value))) ^ 2 < tolerance ^ 2

/-- Ordinary rational-separation form of simultaneous accuracy relative to
the exact affine-input threshold probabilities. -/
def EncodedChordalOmegaThresholdGridTargetWithin {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac) (points : index → Proj)
    (thresholds : List Coordinate) (count : Nat)
    (tolerance : Coordinate) (sample : List index) : Prop :=
  ∀ threshold, threshold ∈ thresholds →
    _root_.FiniteMeasure.rationalSeparation
      (_root_.FiniteMeasure.Distribution.eventFrequency count
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          chordalOmegaProbe (points item)) sample)
      (distribution.probability
        (_root_.FiniteMeasure.atLeastEvent threshold fun item =>
          chordalOmegaProbe
            (CCL.Proj.affine (fraction item).value))) < tolerance

/-- The constructive family sample request bounds the probability of any
encoded threshold-frequency error on the displayed grid. -/
theorem encodedChordalOmegaThresholdGrid_deviationProbability_lt_requested
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (points : index → Proj) (thresholds : List Coordinate)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (failure : Coordinate) (failurePositive : 0 < failure) :
    (distribution.iidSamples
      (requiredEncodedChordalOmegaThresholdGridSampleCount points thresholds
        tolerance failure)).probability
      (encodedChordalOmegaThresholdGridDeviation distribution points
        thresholds
        (requiredEncodedChordalOmegaThresholdGridSampleCount points thresholds
          tolerance failure)
        tolerance) < failure :=
  distribution
    |>.iidSamples_simultaneousEventFrequency_deviationProbability_lt_requested
      (encodedChordalOmegaThresholdEvents points thresholds)
      tolerance tolerancePositive failure failurePositive

/-- For the encoder's own computed homogeneous points, leaving the one
family deviation union already gives simultaneous squared-error accuracy
against the original affine-input threshold probabilities.  Exact encoder
reconstruction removes both the threshold-margin and prefix-length
hypotheses needed for arbitrary compatible realizations. -/
theorem encodedChordalOmegaThresholdGridTargetAccurate_of_outside_encoder
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (thresholds : List Coordinate) (count : Nat)
    (tolerance : Coordinate) (sample : List index)
    (outside : encodedChordalOmegaThresholdGridDeviation distribution
      (fun item => (CCL.Encoder.encodeBlocks
        (fraction item) (numeratorNonzero item)).point)
      thresholds count tolerance sample = false) :
    EncodedChordalOmegaThresholdGridTargetAccurate distribution fraction
      (fun item => (CCL.Encoder.encodeBlocks
        (fraction item) (numeratorNonzero item)).point)
      thresholds count tolerance sample := by
  have encodedAccurate :=
    distribution.eventFamilyFrequenciesAccurate_of_outside
      (encodedChordalOmegaThresholdEvents
        (fun item => (CCL.Encoder.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)
        thresholds) count tolerance sample outside
  intro threshold member
  let encodedEvent : index → Bool :=
    _root_.FiniteMeasure.atLeastEvent threshold fun item =>
      chordalOmegaProbe (CCL.Encoder.encodeBlocks
        (fraction item) (numeratorNonzero item)).point
  let exactEvent : index → Bool :=
    _root_.FiniteMeasure.atLeastEvent threshold fun item =>
      chordalOmegaProbe (CCL.Proj.affine (fraction item).value)
  have eventMember : encodedEvent ∈ encodedChordalOmegaThresholdEvents
      (fun item => (CCL.Encoder.encodeBlocks
        (fraction item) (numeratorNonzero item)).point) thresholds := by
    unfold encodedChordalOmegaThresholdEvents encodedEvent
    exact QuotientFreeList.mem_map.mpr ⟨threshold, member, rfl⟩
  have close := encodedAccurate encodedEvent eventMember
  have probabilityEqual : distribution.probability encodedEvent =
      distribution.probability exactEvent := by
    apply distribution.probability_congr
    intro item
    unfold encodedEvent exactEvent _root_.FiniteMeasure.atLeastEvent
    change decide (threshold ≤ chordalOmegaProbe
        (CCL.Encoder.encodeBlocks
          (fraction item) (numeratorNonzero item)).point) =
      decide (threshold ≤ chordalOmegaProbe
        (CCL.Proj.affine (fraction item).value))
    rw [encodedChordalOmegaProbe_eq_value]
  rw [probabilityEqual] at close
  exact close

/-- Ordinary rational-separation form of the margin-free exact-encoder grid
certificate. -/
theorem encodedChordalOmegaThresholdGridTargetWithin_of_outside_encoder
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (thresholds : List Coordinate) (count : Nat)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (sample : List index)
    (outside : encodedChordalOmegaThresholdGridDeviation distribution
      (fun item => (CCL.Encoder.encodeBlocks
        (fraction item) (numeratorNonzero item)).point)
      thresholds count tolerance sample = false) :
    EncodedChordalOmegaThresholdGridTargetWithin distribution fraction
      (fun item => (CCL.Encoder.encodeBlocks
        (fraction item) (numeratorNonzero item)).point)
      thresholds count tolerance sample := by
  have squared :=
    encodedChordalOmegaThresholdGridTargetAccurate_of_outside_encoder
      distribution fraction numeratorNonzero thresholds count tolerance
      sample outside
  intro threshold member
  apply _root_.FiniteMeasure.rationalSeparation_lt_of_sq_lt_sq
    tolerancePositive
  rw [_root_.FiniteMeasure.rationalSeparation_sq]
  exact squared threshold member

/-- End-to-end margin-free sampling certificate for the encoder's computed
points.  The returned finite request has failure probability below the
displayed budget, and every sample outside that one Boolean failure event is
simultaneously close to all exact affine-input threshold probabilities. -/
theorem encodedChordalOmegaThresholdGrid_encoderCertificate_requested
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (thresholds : List Coordinate)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (failure : Coordinate) (failurePositive : 0 < failure) :
    let points : index → Proj := fun item =>
      (CCL.Encoder.encodeBlocks
        (fraction item) (numeratorNonzero item)).point
    let count := requiredEncodedChordalOmegaThresholdGridSampleCount points
      thresholds tolerance failure
    (distribution.iidSamples count).probability
        (encodedChordalOmegaThresholdGridDeviation distribution points
          thresholds count tolerance) < failure ∧
      ∀ sample, encodedChordalOmegaThresholdGridDeviation distribution points
          thresholds count tolerance sample = false →
        EncodedChordalOmegaThresholdGridTargetWithin distribution fraction
          points thresholds count tolerance sample := by
  dsimp only
  constructor
  · exact encodedChordalOmegaThresholdGrid_deviationProbability_lt_requested
      distribution
      (fun item => (CCL.Encoder.encodeBlocks
        (fraction item) (numeratorNonzero item)).point)
      thresholds tolerance tolerancePositive failure failurePositive
  · intro sample outside
    exact encodedChordalOmegaThresholdGridTargetWithin_of_outside_encoder
      distribution fraction numeratorNonzero thresholds
      (requiredEncodedChordalOmegaThresholdGridSampleCount
        (fun item => (CCL.Encoder.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)
        thresholds tolerance failure)
      tolerance tolerancePositive sample outside

/-- Outside the single family deviation union, a common encoder margin turns
all displayed compatible-realization frequencies into simultaneous estimates
of the exact affine-input threshold probabilities. -/
theorem encodedChordalOmegaThresholdGridTargetAccurate_of_outside
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item))
    (thresholds : List Coordinate)
    (margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ threshold, threshold ∈ thresholds →
      ∀ atom, atom ∈ distribution.atoms →
        threshold + margin ≤ chordalOmegaProbe
            (CCL.Proj.affine (fraction atom.item).value) ∨
          chordalOmegaProbe
              (CCL.Proj.affine (fraction atom.item).value) + margin ≤
            threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredSquaredThresholdBlockCount margin 2 ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (count : Nat) (tolerance : Coordinate) (sample : List index)
    (outside : encodedChordalOmegaThresholdGridDeviation distribution points
      thresholds count tolerance sample = false) :
    EncodedChordalOmegaThresholdGridTargetAccurate distribution fraction
      points thresholds count tolerance sample := by
  have realizedAccurate :=
    distribution.eventFamilyFrequenciesAccurate_of_outside
      (encodedChordalOmegaThresholdEvents points thresholds)
      count tolerance sample outside
  intro threshold member
  let realizedEvent : index → Bool :=
    _root_.FiniteMeasure.atLeastEvent threshold fun item =>
      chordalOmegaProbe (points item)
  let exactEvent : index → Bool :=
    _root_.FiniteMeasure.atLeastEvent threshold fun item =>
      chordalOmegaProbe (CCL.Proj.affine (fraction item).value)
  have eventMember : realizedEvent ∈
      encodedChordalOmegaThresholdEvents points thresholds := by
    unfold encodedChordalOmegaThresholdEvents realizedEvent
    exact QuotientFreeList.mem_map.mpr ⟨threshold, member, rfl⟩
  have close := realizedAccurate realizedEvent eventMember
  have probabilityEqual : distribution.probability realizedEvent =
      distribution.probability exactEvent :=
    encodedChordalOmegaProbe_thresholdProbability_eq_values_of_margin
      distribution fraction numeratorNonzero threshold margin marginPositive
      (separated threshold member) enough points pointsRealize
  rw [probabilityEqual] at close
  exact close

/-- Positive tolerance converts the simultaneous squared-error certificate
into ordinary strict rational separation from every exact affine-input
threshold probability on the displayed grid. -/
theorem encodedChordalOmegaThresholdGridTargetWithin_of_outside
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item))
    (thresholds : List Coordinate)
    (margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ threshold, threshold ∈ thresholds →
      ∀ atom, atom ∈ distribution.atoms →
        threshold + margin ≤ chordalOmegaProbe
            (CCL.Proj.affine (fraction atom.item).value) ∨
          chordalOmegaProbe
              (CCL.Proj.affine (fraction atom.item).value) + margin ≤
            threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredSquaredThresholdBlockCount margin 2 ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (count : Nat) (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (sample : List index)
    (outside : encodedChordalOmegaThresholdGridDeviation distribution points
      thresholds count tolerance sample = false) :
    EncodedChordalOmegaThresholdGridTargetWithin distribution fraction points
      thresholds count tolerance sample := by
  have squared :=
    encodedChordalOmegaThresholdGridTargetAccurate_of_outside distribution
      fraction numeratorNonzero points pointsRealize thresholds margin
      marginPositive separated enough count tolerance sample outside
  intro threshold member
  apply _root_.FiniteMeasure.rationalSeparation_lt_of_sq_lt_sq
    tolerancePositive
  rw [_root_.FiniteMeasure.rationalSeparation_sq]
  exact squared threshold member

end CCL.FiniteMeasure
