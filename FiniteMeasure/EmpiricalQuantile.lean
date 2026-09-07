import FiniteMeasure.Empirical
import FiniteMeasure.QuantileLawStability
import FiniteMeasure.SamplingFamily

/-!
# Finite empirical quantile certificates

Two empirical cumulative frequencies, at explicitly supplied lower and upper
cuts, certify a bracket for an executable empirical lower quantile.  A shared
finite sampling request controls those cuts together with any other displayed
thresholds.  There is no infinite empirical process and no convergence of a
sequence of quantiles.
-/

namespace FiniteMeasure

namespace Distribution

/-- The cumulative probability of an empirical distribution is exactly the
finite event-frequency computation at the same rational cut. -/
theorem empiricalDistribution_cumulative_eq_eventFrequency
    (samples : List Coordinate) (positiveLength : 0 < samples.length)
    (threshold : Coordinate) :
    (empiricalDistribution samples positiveLength).cumulative threshold =
      eventFrequency samples.length (atMostEvent threshold) samples := by
  unfold cumulative
  exact empiricalDistribution_probability_eq_eventFrequency samples
    positiveLength (atMostEvent threshold)

/-- Empirical gridwise frequency accuracy is exactly a strict bound on the
computed finite-grid CDF distance between the empirical and source laws. -/
theorem empiricalCumulativeGridWithin_iff_cumulativeGridDistance_lt
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (samples : List Coordinate) (positiveLength : 0 < samples.length)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance) :
    EmpiricalCumulativeGridWithin source thresholds samples.length tolerance
        samples ↔
      (empiricalDistribution samples positiveLength).cumulativeGridDistance
        source thresholds < tolerance := by
  rw [(empiricalDistribution samples positiveLength)
    |>.cumulativeGridDistance_lt_iff source thresholds tolerance
      tolerancePositive]
  constructor
  · intro within threshold member
    rw [empiricalDistribution_cumulative_eq_eventFrequency]
    exact within threshold member
  · intro close threshold member
    rw [← empiricalDistribution_cumulative_eq_eventFrequency]
    exact close threshold member

/-- Outside the simultaneous empirical-CDF failure union, the exact computed
finite-grid CDF distance is below the requested tolerance. -/
theorem empiricalCumulativeGridDistance_lt_of_outside
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (samples : List Coordinate) (positiveLength : 0 < samples.length)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (outside : empiricalCumulativeGridDeviation source thresholds
      samples.length tolerance samples = false) :
    (empiricalDistribution samples positiveLength).cumulativeGridDistance
      source thresholds < tolerance := by
  apply (source.empiricalCumulativeGridWithin_iff_cumulativeGridDistance_lt
    thresholds samples positiveLength tolerance tolerancePositive).1
  exact source.empiricalCumulativeGridWithin_of_outside thresholds
    samples.length tolerance tolerancePositive samples outside

/-- Total executable CDF distance between a nonempty sample's empirical law
and a supplied source law on one displayed grid.  The empty sample returns
zero. -/
def sampleCumulativeGridDistance
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (samples : List Coordinate) : Coordinate :=
  if positiveLength : 0 < samples.length then
    (empiricalDistribution samples positiveLength).cumulativeGridDistance
      source thresholds
  else 0

theorem sampleCumulativeGridDistance_eq_of_positive
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (samples : List Coordinate) (positiveLength : 0 < samples.length) :
    sampleCumulativeGridDistance source thresholds samples =
      (empiricalDistribution samples positiveLength).cumulativeGridDistance
        source thresholds := by
  unfold sampleCumulativeGridDistance
  rw [dif_pos positiveLength]

/-- Executable event that a sample has the requested length and its computed
finite-grid CDF distance reaches the displayed tolerance. -/
def empiricalCumulativeGridDistanceDeviation
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (count : Nat) (tolerance : Coordinate) : List Coordinate → Bool :=
  fun samples => decide (samples.length = count ∧
    tolerance ≤ sampleCumulativeGridDistance source thresholds samples)

/-- Finite-grid CDF-distance failure is contained in the simultaneous
pointwise empirical-CDF deviation union. -/
theorem empiricalCumulativeGridDistanceDeviation_probability_le
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (count : Nat) (countPositive : 0 < count)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance) :
    (source.iidSamples count).probability
        (empiricalCumulativeGridDistanceDeviation source thresholds count
          tolerance) ≤
      (source.iidSamples count).probability
        (empiricalCumulativeGridDeviation source thresholds count
          tolerance) := by
  unfold probability
  apply eventWeight_mono
  intro atom member selected
  have failure := of_decide_eq_true selected
  rcases failure with ⟨lengthEqual, distanceLarge⟩
  have samplePositive : 0 < atom.item.length := by
    rw [lengthEqual]
    exact countPositive
  cases deviationSelected :
      empiricalCumulativeGridDeviation source thresholds count tolerance
        atom.item with
  | true => rfl
  | false =>
      have outside : empiricalCumulativeGridDeviation source thresholds
          atom.item.length tolerance atom.item = false := by
        simpa only [lengthEqual] using deviationSelected
      have distanceSmall := source.empiricalCumulativeGridDistance_lt_of_outside
        thresholds atom.item samplePositive tolerance tolerancePositive outside
      have distanceEqual := sampleCumulativeGridDistance_eq_of_positive source
        thresholds atom.item samplePositive
      rw [distanceEqual] at distanceLarge
      exact (not_le_of_gt distanceSmall distanceLarge).elim

/-- One computed finite sample request makes the probability that the exact
displayed-grid CDF distance reaches the requested tolerance strictly smaller
than the supplied failure budget. -/
theorem iidSamples_empiricalCumulativeGridDistanceDeviation_lt_requested
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (failure : Coordinate) (failurePositive : 0 < failure) :
    (source.iidSamples
        (requiredCumulativeGridSampleCount
          thresholds tolerance failure)).probability
      (empiricalCumulativeGridDistanceDeviation source thresholds
        (requiredCumulativeGridSampleCount thresholds tolerance failure)
        tolerance) < failure := by
  let count := requiredCumulativeGridSampleCount thresholds tolerance failure
  have countPositive : 0 < count := by
    unfold count requiredCumulativeGridSampleCount
      requiredEventFamilyFrequencySampleCount
      requiredEventFrequencySampleCount requiredChebyshevSampleCount
    exact Nat.zero_lt_succ _
  exact (source.empiricalCumulativeGridDistanceDeviation_probability_le
    thresholds count countPositive tolerance tolerancePositive).trans_lt
      (source.iidSamples_empiricalCumulativeGrid_deviationProbability_lt_requested
        thresholds tolerance tolerancePositive failure failurePositive)

/-! ## Global finite Kolmogorov confidence -/

/-- Every empirical atom of a source-supported sample belongs to the
source's displayed rational payload grid. -/
theorem empiricalDistribution_atom_item_mem_atomPayloadGrid
    (source : Distribution Coordinate)
    (samples : List Coordinate) (positiveLength : 0 < samples.length)
    (supported : SampleSupportedBy source samples)
    (atom : Weighted Coordinate)
    (member : atom ∈ (empiricalDistribution samples positiveLength).atoms) :
    atom.item ∈ source.atomPayloadGrid := by
  have contains := empiricalDistribution_atom_sampleContains samples
    positiveLength atom member
  have sampleMember := sampleContains_mem atom.item contains
  rcases source.sampleSupportedBy_source_of_mem atom.item supported sampleMember
      with ⟨sourceAtom, sourceMember, itemEqual⟩
  rw [← itemEqual]
  exact source.atom_item_mem_atomPayloadGrid sourceAtom sourceMember

/-- On a sample supported by the source law, the source payload grid covers
both the empirical and source tables.  Its computed CDF maximum therefore
controls the global finite Kolmogorov distance. -/
theorem empiricalDistribution_finiteKolmogorovDistance_le_sourceGridDistance
    (source : Distribution Coordinate)
    (samples : List Coordinate) (positiveLength : 0 < samples.length)
    (supported : SampleSupportedBy source samples) :
    (empiricalDistribution samples positiveLength).finiteKolmogorovDistance
        source ≤
      (empiricalDistribution samples positiveLength).cumulativeGridDistance
        source source.atomPayloadGrid := by
  apply (empiricalDistribution samples positiveLength)
    |>.finiteKolmogorovDistance_le_cumulativeGridDistance_of_support_covered
      source source.atomPayloadGrid
  · intro atom member
    exact source.empiricalDistribution_atom_item_mem_atomPayloadGrid samples
      positiveLength supported atom member
  · intro atom member
    exact source.atom_item_mem_atomPayloadGrid atom member

/-- Outside the source-support-grid empirical-CDF deviation event, a
source-supported sample has globally small finite Kolmogorov distance. -/
theorem empiricalFiniteKolmogorovDistance_lt_of_outside_sourceGridDeviation
    (source : Distribution Coordinate)
    (samples : List Coordinate) (positiveLength : 0 < samples.length)
    (supported : SampleSupportedBy source samples)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (outside : empiricalCumulativeGridDeviation source source.atomPayloadGrid
      samples.length tolerance samples = false) :
    (empiricalDistribution samples positiveLength).finiteKolmogorovDistance
      source < tolerance :=
  (source.empiricalDistribution_finiteKolmogorovDistance_le_sourceGridDistance
      samples positiveLength supported).trans_lt
    (source.empiricalCumulativeGridDistance_lt_of_outside
      source.atomPayloadGrid samples positiveLength tolerance
        tolerancePositive outside)

/-- Total executable global CDF distance of one displayed sample from its
source law.  The empty sample returns zero. -/
def sampleFiniteKolmogorovDistance
    (source : Distribution Coordinate) (samples : List Coordinate) :
    Coordinate :=
  if positiveLength : 0 < samples.length then
    (empiricalDistribution samples positiveLength).finiteKolmogorovDistance
      source
  else 0

theorem sampleFiniteKolmogorovDistance_eq_of_positive
    (source : Distribution Coordinate) (samples : List Coordinate)
    (positiveLength : 0 < samples.length) :
    sampleFiniteKolmogorovDistance source samples =
      (empiricalDistribution samples positiveLength).finiteKolmogorovDistance
        source := by
  unfold sampleFiniteKolmogorovDistance
  rw [dif_pos positiveLength]

/-- Executable failure event that the empirical law reaches the supplied
global finite Kolmogorov tolerance. -/
def empiricalFiniteKolmogorovDistanceDeviation
    (source : Distribution Coordinate) (count : Nat)
    (tolerance : Coordinate) : List Coordinate → Bool :=
  fun samples => decide (samples.length = count ∧
    tolerance ≤ sampleFiniteKolmogorovDistance source samples)

/-- Explicit sample request for global finite Kolmogorov accuracy, obtained
from the finite source payload grid. -/
def requiredFiniteKolmogorovSampleCount
    (source : Distribution Coordinate)
    (tolerance failure : Coordinate) : Nat :=
  requiredCumulativeGridSampleCount source.atomPayloadGrid tolerance failure

/-- Global empirical-CDF failure is contained in the simultaneous deviation
union on the finite source payload grid. -/
theorem empiricalFiniteKolmogorovDistanceDeviation_probability_le_gridDeviation
    (source : Distribution Coordinate)
    (count : Nat) (countPositive : 0 < count)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance) :
    (source.iidSamples count).probability
        (empiricalFiniteKolmogorovDistanceDeviation source count tolerance) ≤
      (source.iidSamples count).probability
        (empiricalCumulativeGridDeviation source source.atomPayloadGrid count
          tolerance) := by
  unfold probability
  apply eventWeight_mono
  intro atom member selected
  have failure := of_decide_eq_true selected
  rcases failure with ⟨lengthEqual, distanceLarge⟩
  have samplePositive : 0 < atom.item.length := by
    rw [lengthEqual]
    exact countPositive
  have supported := source.iidSamples_atom_sampleSupportedBy count atom member
  cases deviationSelected : empiricalCumulativeGridDeviation source
      source.atomPayloadGrid count tolerance atom.item with
  | true => rfl
  | false =>
      have outside : empiricalCumulativeGridDeviation source
          source.atomPayloadGrid atom.item.length tolerance atom.item = false := by
        simpa only [lengthEqual] using deviationSelected
      have distanceSmall :=
        source.empiricalFiniteKolmogorovDistance_lt_of_outside_sourceGridDeviation
          atom.item samplePositive supported tolerance tolerancePositive outside
      have distanceEqual := sampleFiniteKolmogorovDistance_eq_of_positive
        source atom.item samplePositive
      rw [distanceEqual] at distanceLarge
      exact (not_le_of_gt distanceSmall distanceLarge).elim

/-- A single executable finite request makes the probability of global
finite Kolmogorov error at least `tolerance` strictly smaller than the
supplied positive rational failure budget. -/
theorem iidSamples_empiricalFiniteKolmogorovDistanceDeviation_lt_requested
    (source : Distribution Coordinate)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (failure : Coordinate) (failurePositive : 0 < failure) :
    (source.iidSamples
        (requiredFiniteKolmogorovSampleCount source tolerance failure)).probability
      (empiricalFiniteKolmogorovDistanceDeviation source
        (requiredFiniteKolmogorovSampleCount source tolerance failure)
        tolerance) < failure := by
  let count := requiredFiniteKolmogorovSampleCount source tolerance failure
  have countPositive : 0 < count := by
    unfold count requiredFiniteKolmogorovSampleCount
      requiredCumulativeGridSampleCount
      requiredEventFamilyFrequencySampleCount
      requiredEventFrequencySampleCount requiredChebyshevSampleCount
    exact Nat.zero_lt_succ _
  exact (source.empiricalFiniteKolmogorovDistanceDeviation_probability_le_gridDeviation
    count countPositive tolerance tolerancePositive).trans_lt
      (source.iidSamples_empiricalCumulativeGrid_deviationProbability_lt_requested
        source.atomPayloadGrid tolerance tolerancePositive failure
          failurePositive)

/-- Total executable sample lower quantile.  A nonempty sample uses its exact
empirical distribution; the empty sample returns `0`.  Statistical theorems
below explicitly require a positive displayed sample count. -/
def sampleLowerQuantile (samples : List Coordinate)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) : Coordinate :=
  if positiveLength : 0 < samples.length then
    (empiricalDistribution samples positiveLength).lowerQuantile
      level levelPositive levelAtMostOne
  else 0

theorem sampleLowerQuantile_eq_of_positive
    (samples : List Coordinate) (positiveLength : 0 < samples.length)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    sampleLowerQuantile samples level levelPositive levelAtMostOne =
      (empiricalDistribution samples positiveLength).lowerQuantile
        level levelPositive levelAtMostOne := by
  unfold sampleLowerQuantile
  rw [dif_pos positiveLength]

/-- A nonempty sample's executable lower quantile is one of the payloads
actually occurring in that finite sample. -/
theorem sampleLowerQuantile_sampleContains
    (samples : List Coordinate) (positiveLength : 0 < samples.length)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    SampleContains
      (sampleLowerQuantile samples level levelPositive levelAtMostOne)
      samples := by
  have quantileEqual := sampleLowerQuantile_eq_of_positive samples
    positiveLength level levelPositive levelAtMostOne
  rcases (empiricalDistribution samples positiveLength)
      |>.lowerQuantile_eq_atom_of_mem level levelPositive levelAtMostOne with
    ⟨atom, member, valueEqual⟩
  have contains := empiricalDistribution_atom_sampleContains samples
    positiveLength atom member
  rw [quantileEqual]
  simpa only [valueEqual] using contains

/-- Executable failure event saying that a sample has the requested length
but its empirical lower quantile lies outside `(lower, upper]`. -/
def empiricalLowerQuantileBracketDeviation
    (count : Nat) (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) (lower upper : Coordinate) :
    List Coordinate → Bool :=
  fun samples => decide
    (samples.length = count ∧
      (sampleLowerQuantile samples level levelPositive levelAtMostOne ≤ lower ∨
        upper < sampleLowerQuantile samples level levelPositive
          levelAtMostOne))

/-- Executable lower-median escape event, specialized from the empirical
lower-quantile bracket event at level `1 / 2`. -/
def empiricalMedianBracketDeviation
    (count : Nat) (lower upper : Coordinate) : List Coordinate → Bool :=
  empiricalLowerQuantileBracketDeviation count (1 / 2)
    (by decide) (by decide) lower upper

/-- Pointwise empirical-CDF accuracy at two members of a displayed grid,
together with explicit reference-CDF margins, places the empirical lower
quantile in the supplied rational bracket. -/
theorem empiricalLowerQuantile_mem_bracket_of_gridWithin
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (samples : List Coordinate) (positiveLength : 0 < samples.length)
    (tolerance : Coordinate)
    (within : EmpiricalCumulativeGridWithin source thresholds samples.length
      tolerance samples)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Coordinate)
    (lowerMember : lower ∈ thresholds) (upperMember : upper ∈ thresholds)
    (lowerMargin : source.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ source.cumulative upper) :
    lower < (empiricalDistribution samples positiveLength).lowerQuantile
        level levelPositive levelAtMostOne ∧
      (empiricalDistribution samples positiveLength).lowerQuantile
        level levelPositive levelAtMostOne ≤ upper := by
  apply (empiricalDistribution samples positiveLength)
    |>.lowerQuantile_mem_bracket_of_cumulative_separations_lt source
      level levelPositive levelAtMostOne lower upper tolerance
  · rw [empiricalDistribution_cumulative_eq_eventFrequency]
    exact within lower lowerMember
  · rw [empiricalDistribution_cumulative_eq_eventFrequency]
    exact within upper upperMember
  · exact lowerMargin
  · exact upperMargin

/-- Outside the single simultaneous empirical-CDF deviation event, the same
two reference margins yield a certified empirical lower-quantile bracket. -/
theorem empiricalLowerQuantile_mem_bracket_of_outside_gridDeviation
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (samples : List Coordinate) (positiveLength : 0 < samples.length)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (outside : empiricalCumulativeGridDeviation source thresholds
      samples.length tolerance samples = false)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Coordinate)
    (lowerMember : lower ∈ thresholds) (upperMember : upper ∈ thresholds)
    (lowerMargin : source.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ source.cumulative upper) :
    lower < (empiricalDistribution samples positiveLength).lowerQuantile
        level levelPositive levelAtMostOne ∧
      (empiricalDistribution samples positiveLength).lowerQuantile
        level levelPositive levelAtMostOne ≤ upper := by
  apply source.empiricalLowerQuantile_mem_bracket_of_gridWithin thresholds
    samples positiveLength tolerance
  · exact source.empiricalCumulativeGridWithin_of_outside thresholds
      samples.length tolerance tolerancePositive samples outside
  · exact lowerMember
  · exact upperMember
  · exact lowerMargin
  · exact upperMargin

/-- A strict global finite Kolmogorov bound directly gives a lower-quantile
bracket, with no caller-supplied threshold grid or membership proofs. -/
theorem empiricalLowerQuantile_mem_bracket_of_finiteKolmogorovDistance_lt
    (source : Distribution Coordinate)
    (samples : List Coordinate) (positiveLength : 0 < samples.length)
    (tolerance : Coordinate)
    (distanceSmall :
      (empiricalDistribution samples positiveLength).finiteKolmogorovDistance
        source < tolerance)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Coordinate)
    (lowerMargin : source.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ source.cumulative upper) :
    lower < (empiricalDistribution samples positiveLength).lowerQuantile
        level levelPositive levelAtMostOne ∧
      (empiricalDistribution samples positiveLength).lowerQuantile
        level levelPositive levelAtMostOne ≤ upper :=
  (empiricalDistribution samples positiveLength)
    |>.lowerQuantile_mem_bracket_of_finiteKolmogorovDistance_lt source
      level levelPositive levelAtMostOne lower upper tolerance distanceSmall
        lowerMargin upperMargin

/-- Empirical quantile-bracket failure is contained in the executable global
finite Kolmogorov failure event. -/
theorem empiricalLowerQuantileBracketDeviation_probability_le_finiteKolmogorovDeviation
    (source : Distribution Coordinate)
    (count : Nat) (countPositive : 0 < count)
    (tolerance : Coordinate)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Coordinate)
    (lowerMargin : source.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ source.cumulative upper) :
    (source.iidSamples count).probability
        (empiricalLowerQuantileBracketDeviation count level levelPositive
          levelAtMostOne lower upper) ≤
      (source.iidSamples count).probability
        (empiricalFiniteKolmogorovDistanceDeviation source count tolerance) := by
  unfold probability
  apply eventWeight_mono
  intro atom member selected
  have bracketFailure := of_decide_eq_true selected
  rcases bracketFailure with ⟨lengthEqual, escaped⟩
  have samplePositive : 0 < atom.item.length := by
    rw [lengthEqual]
    exact countPositive
  cases distanceSelected : empiricalFiniteKolmogorovDistanceDeviation source
      count tolerance atom.item with
  | true => rfl
  | false =>
      have noDistanceFailure : ¬(atom.item.length = count ∧
          tolerance ≤ sampleFiniteKolmogorovDistance source atom.item) := by
        unfold empiricalFiniteKolmogorovDistanceDeviation at distanceSelected
        exact decide_eq_false_iff_not.mp distanceSelected
      have distanceNotLarge : ¬tolerance ≤
          sampleFiniteKolmogorovDistance source atom.item := by
        intro distanceLarge
        exact noDistanceFailure ⟨lengthEqual, distanceLarge⟩
      have sampleDistanceSmall :
          sampleFiniteKolmogorovDistance source atom.item < tolerance :=
        RFAP.ConstructiveFraction.lt_of_not_ge_direct distanceNotLarge
      have distanceEqual := sampleFiniteKolmogorovDistance_eq_of_positive
        source atom.item samplePositive
      rw [distanceEqual] at sampleDistanceSmall
      have bracket :=
        source.empiricalLowerQuantile_mem_bracket_of_finiteKolmogorovDistance_lt
          atom.item samplePositive tolerance sampleDistanceSmall level
          levelPositive levelAtMostOne lower upper lowerMargin upperMargin
      have quantileEqual := sampleLowerQuantile_eq_of_positive atom.item
        samplePositive level levelPositive levelAtMostOne
      rcases escaped with lowerFailure | upperFailure
      · rw [quantileEqual] at lowerFailure
        exact (not_le_of_gt bracket.1 lowerFailure).elim
      · rw [quantileEqual] at upperFailure
        exact (not_lt_of_ge bracket.2 upperFailure).elim

/-- The global finite Kolmogorov request gives an explicit confidence bound
for any empirical lower-quantile bracket with certified source-CDF margins. -/
theorem iidSamples_empiricalLowerQuantileBracketDeviation_lt_requested_global
    (source : Distribution Coordinate)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (failure : Coordinate) (failurePositive : 0 < failure)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Coordinate)
    (lowerMargin : source.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ source.cumulative upper) :
    (source.iidSamples
        (requiredFiniteKolmogorovSampleCount source tolerance failure)).probability
      (empiricalLowerQuantileBracketDeviation
        (requiredFiniteKolmogorovSampleCount source tolerance failure)
        level levelPositive levelAtMostOne lower upper) < failure := by
  let count := requiredFiniteKolmogorovSampleCount source tolerance failure
  have countPositive : 0 < count := by
    unfold count requiredFiniteKolmogorovSampleCount
      requiredCumulativeGridSampleCount
      requiredEventFamilyFrequencySampleCount
      requiredEventFrequencySampleCount requiredChebyshevSampleCount
    exact Nat.zero_lt_succ _
  exact (source
    |>.empiricalLowerQuantileBracketDeviation_probability_le_finiteKolmogorovDeviation
      count countPositive tolerance level levelPositive levelAtMostOne lower
        upper lowerMargin upperMargin).trans_lt
    (source.iidSamples_empiricalFiniteKolmogorovDistanceDeviation_lt_requested
      tolerance tolerancePositive failure failurePositive)

/-- Median specialization of the global finite Kolmogorov confidence
request. -/
theorem iidSamples_empiricalMedianBracketDeviation_lt_requested_global
    (source : Distribution Coordinate)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (failure : Coordinate) (failurePositive : 0 < failure)
    (lower upper : Coordinate)
    (lowerMargin : source.cumulative lower + tolerance < 1 / 2)
    (upperMargin : 1 / 2 + tolerance ≤ source.cumulative upper) :
    (source.iidSamples
        (requiredFiniteKolmogorovSampleCount source tolerance failure)).probability
      (empiricalMedianBracketDeviation
        (requiredFiniteKolmogorovSampleCount source tolerance failure)
        lower upper) < failure :=
  source.iidSamples_empiricalLowerQuantileBracketDeviation_lt_requested_global
    tolerance tolerancePositive failure failurePositive
      (1 / 2) (by decide) (by decide) lower upper lowerMargin upperMargin

/-- Whenever the displayed sample count is positive, failure of the empirical
quantile bracket is contained in the simultaneous empirical-CDF deviation
event.  Samples of any other length are explicitly excluded from the bracket
failure event. -/
theorem empiricalLowerQuantileBracketDeviation_probability_le_gridDeviation
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (count : Nat) (countPositive : 0 < count)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Coordinate)
    (lowerMember : lower ∈ thresholds) (upperMember : upper ∈ thresholds)
    (lowerMargin : source.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ source.cumulative upper) :
    (source.iidSamples count).probability
        (empiricalLowerQuantileBracketDeviation count level levelPositive
          levelAtMostOne lower upper) ≤
      (source.iidSamples count).probability
        (empiricalCumulativeGridDeviation source thresholds count
          tolerance) := by
  unfold probability
  apply eventWeight_mono
  intro atom member selected
  have failure := of_decide_eq_true selected
  rcases failure with ⟨lengthEqual, lowerFailure | upperFailure⟩
  · have samplePositive : 0 < atom.item.length := by
      rw [lengthEqual]
      exact countPositive
    cases deviationSelected :
        empiricalCumulativeGridDeviation source thresholds count tolerance
          atom.item with
    | true => rfl
    | false =>
        have outside : empiricalCumulativeGridDeviation source thresholds
            atom.item.length tolerance atom.item = false := by
          simpa only [lengthEqual] using deviationSelected
        have bracket :=
          source.empiricalLowerQuantile_mem_bracket_of_outside_gridDeviation
            thresholds atom.item samplePositive tolerance tolerancePositive
            outside level levelPositive levelAtMostOne lower upper lowerMember
            upperMember lowerMargin upperMargin
        have quantileEqual := sampleLowerQuantile_eq_of_positive atom.item
          samplePositive level levelPositive levelAtMostOne
        rw [quantileEqual] at lowerFailure
        exact (not_le_of_gt bracket.1 lowerFailure).elim
  · have samplePositive : 0 < atom.item.length := by
      rw [lengthEqual]
      exact countPositive
    cases deviationSelected :
        empiricalCumulativeGridDeviation source thresholds count tolerance
          atom.item with
    | true => rfl
    | false =>
        have outside : empiricalCumulativeGridDeviation source thresholds
            atom.item.length tolerance atom.item = false := by
          simpa only [lengthEqual] using deviationSelected
        have bracket :=
          source.empiricalLowerQuantile_mem_bracket_of_outside_gridDeviation
            thresholds atom.item samplePositive tolerance tolerancePositive
            outside level levelPositive levelAtMostOne lower upper lowerMember
            upperMember lowerMargin upperMargin
        have quantileEqual := sampleLowerQuantile_eq_of_positive atom.item
          samplePositive level levelPositive levelAtMostOne
        rw [quantileEqual] at upperFailure
        exact (not_lt_of_ge bracket.2 upperFailure).elim

/-- The shared finite empirical-CDF sample request therefore gives an
explicit strict failure-probability guarantee for every quantile bracket
whose two cuts occur in the displayed grid and satisfy the supplied margins. -/
theorem iidSamples_empiricalLowerQuantileBracketDeviation_lt_requested
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (failure : Coordinate) (failurePositive : 0 < failure)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Coordinate)
    (lowerMember : lower ∈ thresholds) (upperMember : upper ∈ thresholds)
    (lowerMargin : source.cumulative lower + tolerance < level)
    (upperMargin : level + tolerance ≤ source.cumulative upper) :
    (source.iidSamples
        (requiredCumulativeGridSampleCount
          thresholds tolerance failure)).probability
      (empiricalLowerQuantileBracketDeviation
        (requiredCumulativeGridSampleCount thresholds tolerance failure)
        level levelPositive levelAtMostOne lower upper) < failure := by
  let count := requiredCumulativeGridSampleCount thresholds tolerance failure
  have countPositive : 0 < count := by
    unfold count requiredCumulativeGridSampleCount
      requiredEventFamilyFrequencySampleCount
      requiredEventFrequencySampleCount requiredChebyshevSampleCount
    exact Nat.zero_lt_succ _
  exact (source.empiricalLowerQuantileBracketDeviation_probability_le_gridDeviation
    thresholds count countPositive tolerance tolerancePositive level
    levelPositive levelAtMostOne lower upper lowerMember upperMember
    lowerMargin upperMargin).trans_lt
      (source.iidSamples_empiricalCumulativeGrid_deviationProbability_lt_requested
        thresholds tolerance tolerancePositive failure failurePositive)

/-- Median specialization of the finite empirical-quantile confidence
request. -/
theorem iidSamples_empiricalMedianBracketDeviation_lt_requested
    (source : Distribution Coordinate) (thresholds : List Coordinate)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (failure : Coordinate) (failurePositive : 0 < failure)
    (lower upper : Coordinate)
    (lowerMember : lower ∈ thresholds) (upperMember : upper ∈ thresholds)
    (lowerMargin : source.cumulative lower + tolerance < 1 / 2)
    (upperMargin : 1 / 2 + tolerance ≤ source.cumulative upper) :
    (source.iidSamples
        (requiredCumulativeGridSampleCount
          thresholds tolerance failure)).probability
      (empiricalMedianBracketDeviation
        (requiredCumulativeGridSampleCount thresholds tolerance failure)
        lower upper) < failure := by
  exact source.iidSamples_empiricalLowerQuantileBracketDeviation_lt_requested
    thresholds tolerance tolerancePositive failure failurePositive
    (1 / 2) (by decide) (by decide) lower upper lowerMember upperMember
    lowerMargin upperMargin

end Distribution

end FiniteMeasure
