module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Cumulative.Support
import Purelib.Measure.Distribution.Sampling.Basic
import Purelib.Measure.Distribution.Sampling.Request
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.Fraction

import Purelib.Approximation.Rational.Budget.FiniteFamily
import Purelib.Data.List.Multiplicity
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Cumulative.Grid
public import Purelib.Measure.Distribution.Empirical.Basic
import Purelib.Measure.Distribution.Empirical.GridConfidence
public import Purelib.Measure.Distribution.Sampling.Cumulative
import Purelib.Measure.Distribution.Sampling.Family
import Purelib.Measure.Event.RationalGrid
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
public import Purelib.Measure.Distribution.Kolmogorov.Basic
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Approximation.Rational.Budget.ReciprocalSquare
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Finite empirical quantile certificates

Two empirical cumulative frequencies, at explicitly supplied lower and upper
cuts, certify a bracket for an executable empirical lower quantile.  A shared
finite sampling request controls those cuts together with any other displayed
thresholds.  There is no infinite empirical process and no convergence of a
sequence of quantiles.
-/

namespace Purelib.Measure

namespace Distribution

/-! ## Global finite Kolmogorov confidence -/

section
open Purelib
open Purelib.Data.Rat
/-- Every empirical atom of a source-supported sample belongs to the exact original source payload grid. -/
theorem empiricalDistribution_atom_item_mem_atomPayloadGrid
    (source : Measure.Distribution Fraction.Rational)
    (samples : List Fraction.Rational) (positiveLength : 0 < samples.length)
    (supported : SampleSupportedBy source samples)
    (atom : Weighted Fraction.Rational)
    (member : atom ∈ (empiricalDistribution samples positiveLength).atoms) :
    atom.item ∈ source.atomPayloadGrid := by
  have contains := empiricalDistribution_atom_sampleContains samples
    positiveLength atom member
  have sampleMember := Data.List.sampleContains_mem atom.item contains
  rcases source.sampleSupportedBy_source_of_mem atom.item supported sampleMember
      with ⟨sourceAtom, sourceMember, itemEqual⟩
  rw [← itemEqual]
  exact source.atom_item_mem_atomPayloadGrid sourceAtom sourceMember

/-- For a source-supported nonempty sample, Kolmogorov distance is bounded by cumulative distance on the original source
grid. -/
theorem empiricalDistributionKolmogorovDistance_le_sourceGridDistance
    (source : Measure.Distribution Fraction.Rational)
    (samples : List Fraction.Rational) (positiveLength : 0 < samples.length)
    (supported : SampleSupportedBy source samples) :
    (empiricalDistribution samples positiveLength).kolmogorovDistance
        source ≤
      (empiricalDistribution samples positiveLength).cumulativeGridDistance
        source source.atomPayloadGrid := by
  apply (empiricalDistribution samples positiveLength)
    |>.kolmogorovDistance_le_cumulativeGridDistance_of_support_covered
      source source.atomPayloadGrid
  · intro atom member
    exact source.empiricalDistribution_atom_item_mem_atomPayloadGrid samples
      positiveLength supported atom member
  · intro atom member
    exact source.atom_item_mem_atomPayloadGrid atom member

/-- A source-supported sample outside the original grid deviation event has empirical Kolmogorov distance below the
positive tolerance. -/
theorem empiricalKolmogorovDistance_lt_of_outside_sourceGridDeviation
    (source : Measure.Distribution Fraction.Rational)
    (samples : List Fraction.Rational) (positiveLength : 0 < samples.length)
    (supported : SampleSupportedBy source samples)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (outside : empiricalCumulativeGridDeviation source source.atomPayloadGrid
      samples.length tolerance samples = false) :
    (empiricalDistribution samples positiveLength).kolmogorovDistance
      source < tolerance :=
  (source.empiricalDistributionKolmogorovDistance_le_sourceGridDistance
      samples positiveLength supported).trans_lt
    (source.empiricalCumulativeGridDistance_lt_of_outside
      source.atomPayloadGrid samples positiveLength tolerance
        tolerancePositive outside)

/-- Compute empirical-to-source Kolmogorov distance for nonempty samples, returning zero on the empty list. -/
def sampleKolmogorovDistance
    (source : Measure.Distribution Fraction.Rational) (samples : List Fraction.Rational) :
    Fraction.Rational :=
  if positiveLength : 0 < samples.length then
    (empiricalDistribution samples positiveLength).kolmogorovDistance
      source
  else 0

/-- For a nonempty original sample list, the total sample-distance function equals its exact empirical Kolmogorov
distance. -/
theorem sampleKolmogorovDistance_eq_of_positive
    (source : Measure.Distribution Fraction.Rational) (samples : List Fraction.Rational)
    (positiveLength : 0 < samples.length) :
    sampleKolmogorovDistance source samples =
      (empiricalDistribution samples positiveLength).kolmogorovDistance
        source := by
  unfold sampleKolmogorovDistance
  rw [dif_pos positiveLength]

/-- Select samples of the requested length whose empirical Kolmogorov distance reaches the tolerance. -/
def empiricalKolmogorovDistanceDeviation
    (source : Measure.Distribution Fraction.Rational) (count : Nat)
    (tolerance : Fraction.Rational) : List Fraction.Rational → Bool :=
  fun samples => decide (samples.length = count ∧
    tolerance ≤ sampleKolmogorovDistance source samples)

/-- Compute the cumulative-grid sample request on the exact source's retained payload grid. -/
def requiredKolmogorovSampleCount
    (source : Measure.Distribution Fraction.Rational)
    (tolerance failure : Fraction.Rational) : Nat :=
  requiredCumulativeGridSampleCount source.atomPayloadGrid tolerance failure

/-- At positive count and tolerance, empirical Kolmogorov deviation probability is bounded by the exact source-grid
frequency deviation probability. -/
theorem empiricalKolmogorovDistanceDeviation_probability_le_gridDeviation
    (source : Measure.Distribution Fraction.Rational)
    (count : Nat) (countPositive : 0 < count)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance) :
    (source.iidSamples count).probability
        (empiricalKolmogorovDistanceDeviation source count tolerance) ≤
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
        source.empiricalKolmogorovDistance_lt_of_outside_sourceGridDeviation
          atom.item samplePositive supported tolerance tolerancePositive outside
      have distanceEqual := sampleKolmogorovDistance_eq_of_positive
        source atom.item samplePositive
      rw [distanceEqual] at distanceLarge
      exact (not_le_of_gt distanceSmall distanceLarge).elim

/-- The computed source-grid request makes empirical Kolmogorov deviation probability smaller than the positive failure
tolerance. -/
theorem iidSamples_empiricalKolmogorovDistanceDeviation_lt_requested
    (source : Measure.Distribution Fraction.Rational)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (failure : Fraction.Rational) (failurePositive : 0 < failure) :
    (source.iidSamples
        (requiredKolmogorovSampleCount source tolerance failure)).probability
      (empiricalKolmogorovDistanceDeviation source
        (requiredKolmogorovSampleCount source tolerance failure)
        tolerance) < failure := by
  let count := requiredKolmogorovSampleCount source tolerance failure
  have countPositive : 0 < count := by
    unfold count requiredKolmogorovSampleCount
      requiredCumulativeGridSampleCount
      requiredEventFamilyFrequencySampleCount
      requiredEventFrequencySampleCount requiredChebyshevSampleCount
    exact Nat.zero_lt_succ _
  exact (source.empiricalKolmogorovDistanceDeviation_probability_le_gridDeviation
    count countPositive tolerance tolerancePositive).trans_lt
      (source.iidSamples_empiricalCumulativeGrid_deviationProbability_lt_requested
        source.atomPayloadGrid tolerance tolerancePositive failure
          failurePositive)
end

end Distribution

end Purelib.Measure

end
