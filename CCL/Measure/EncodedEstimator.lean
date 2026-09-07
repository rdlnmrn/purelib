import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.EncodedSampling
import CCL.Measure.EncodedSquaredStability

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

namespace CCL.FiniteMeasure

/-- Exact finite expectation of the concrete probe on the original affine
Gaussian fractions. -/
def encodedChordalOmegaExactExpectation {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac) : Coordinate :=
  distribution.expectation fun item =>
    chordalOmegaProbe (CCL.Proj.affine (fraction item).value)

/-- Executable completed-block request assigning half of the desired estimator
error to CCL representation bias. -/
def encodedChordalOmegaEstimatorBlockCount (epsilon : Coordinate) : Nat :=
  requiredSquaredProbeBlockCount (epsilon / 2) 2

/-- Executable sample count assigning half of the desired estimator error to
sampling fluctuation, using the global variance budget `1`. -/
def encodedChordalOmegaEstimatorSampleCount
    (epsilon failure : Coordinate) : Nat :=
  _root_.FiniteMeasure.Distribution.requiredChebyshevSampleCount
    1 (epsilon / 2) failure

/-- Deviation of a finite sample mean from the exact affine-input expectation,
rather than from the expectation of the supplied compatible realizations. -/
def encodedChordalOmegaSampleMeanTargetDeviation {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (count : Nat) (points : index → Proj)
    (epsilon : Coordinate) : List index → Bool :=
  fun sample => decide (epsilon ≤
    _root_.FiniteMeasure.rationalSeparation
      (_root_.FiniteMeasure.Distribution.sampleMean count
        (fun item => chordalOmegaProbe (points item)) sample)
      (encodedChordalOmegaExactExpectation distribution fraction))

private theorem half_positive {epsilon : Coordinate} (positive : 0 < epsilon) :
    0 < epsilon / 2 :=
  RFAP.ConstructiveFraction.div_pos_direct positive (by decide)

private theorem half_add_half (epsilon : Coordinate) :
    epsilon / 2 + epsilon / 2 = epsilon := by
  calc
    epsilon / 2 + epsilon / 2 = (epsilon / 2) * 2 := by ring1
    _ = epsilon :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne epsilon 2 (by decide)

/-- End-to-end finite estimator theorem for an actual heterogeneous encoder
table.  Sufficient CCL blocks make representation bias smaller than half the
requested error; the computed finite iid sample count makes the remaining
sample-mean failure probability strictly smaller than `failure`. -/
theorem encodedChordalOmegaSampleMean_targetDeviationProbability_lt_requested
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
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      encodedChordalOmegaEstimatorBlockCount epsilon ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (failure : Coordinate) (failurePositive : 0 < failure) :
    (distribution.iidSamples
        (encodedChordalOmegaEstimatorSampleCount epsilon failure)).probability
      (encodedChordalOmegaSampleMeanTargetDeviation distribution fraction
        (encodedChordalOmegaEstimatorSampleCount epsilon failure)
        points epsilon) < failure := by
  let value : index → Coordinate := fun item => chordalOmegaProbe (points item)
  let observedMean := distribution.expectation value
  let exactMean := encodedChordalOmegaExactExpectation distribution fraction
  let half := epsilon / 2
  let count := encodedChordalOmegaEstimatorSampleCount epsilon failure
  have halfPositive : 0 < half := half_positive epsilonPositive
  have biasSmall :
      _root_.FiniteMeasure.rationalSeparation observedMean exactMean < half := by
    exact encodedChordalOmegaProbe_expectation_separation_lt_requested
      distribution fraction numeratorNonzero half halfPositive
      (by
        intro atom member
        exact enough atom member)
      points pointsRealize
  have varianceLe : distribution.variance value ≤ 1 :=
    chordalOmegaProbe_variance_le_one distribution points (by
      intro atom member
      exact (pointsRealize atom member).valid)
  have samplingSmall :
      (distribution.iidSamples count).probability
          (distribution.sampleMeanDeviation count value half) < failure := by
    exact distribution.iidSamples_sampleMean_deviationProbability_lt_requested
      value 1 (by decide) varianceLe half halfPositive failure failurePositive
  calc
    (distribution.iidSamples count).probability
          (encodedChordalOmegaSampleMeanTargetDeviation distribution fraction
            count points epsilon) ≤
        (distribution.iidSamples count).probability
          (distribution.sampleMeanDeviation count value half) := by
      unfold _root_.FiniteMeasure.Distribution.probability
      apply _root_.FiniteMeasure.eventWeight_mono
      intro atom member selected
      have targetFar : epsilon ≤
          _root_.FiniteMeasure.rationalSeparation
            (_root_.FiniteMeasure.Distribution.sampleMean count value atom.item)
            exactMean := of_decide_eq_true selected
      apply decide_eq_true_eq.mpr
      rw [← _root_.FiniteMeasure.rationalSeparation_sq]
      have halfLe : half ≤ _root_.FiniteMeasure.rationalSeparation
          (_root_.FiniteMeasure.Distribution.sampleMean count value atom.item)
          observedMean := by
        apply RFAP.ConstructiveFraction.le_of_not_gt_direct
        intro sampleClose
        have totalSmall : _root_.FiniteMeasure.rationalSeparation
            (_root_.FiniteMeasure.Distribution.sampleMean count value atom.item)
            exactMean < epsilon := by
          calc
            _root_.FiniteMeasure.rationalSeparation
                (_root_.FiniteMeasure.Distribution.sampleMean count value
                  atom.item) exactMean ≤
                _root_.FiniteMeasure.rationalSeparation
                    (_root_.FiniteMeasure.Distribution.sampleMean count value
                      atom.item) observedMean +
                  _root_.FiniteMeasure.rationalSeparation observedMean
                    exactMean :=
              _root_.FiniteMeasure.rationalSeparation_triangle _ _ _
            _ < half + half :=
              RFAP.ConstructiveFraction.add_lt_add_direct sampleClose biasSmall
            _ = epsilon := half_add_half epsilon
        exact (not_lt_of_ge targetFar) totalSmall
      exact RFAP.ConstructiveFraction.pow_le_pow_direct halfPositive.le halfLe 2
    _ < failure := samplingSmall

end CCL.FiniteMeasure
