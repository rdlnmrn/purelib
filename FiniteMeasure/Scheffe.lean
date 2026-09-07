import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.TotalVariationDistance

/-!
# Finite Scheffé identities

Two nonnegative rational densities of expectation one define finite
reweighted probability laws.  The executable event where the first density
dominates the second attains their event-probability discrepancy.  Its mass is
the integral of the positive density difference, which equals the negative
part because both densities normalise.  Consequently atomic total variation
is exactly half the original-law L1 density separation.
-/

namespace FiniteMeasure

/-- Executable positive-difference event for two rational densities. -/
def densityDominanceEvent {α : Type}
    (first second : α → Coordinate) : α → Bool :=
  fun item => decide (second item ≤ first item)

namespace Distribution

private theorem reweight_probability_sub
    {α : Type} (source : Distribution α)
    (first second : α → Coordinate)
    (firstNonnegative : ∀ item, 0 ≤ first item)
    (secondNonnegative : ∀ item, 0 ≤ second item)
    (firstNormalizes : source.expectation first = 1)
    (secondNormalizes : source.expectation second = 1)
    (event : α → Bool) :
    (source.reweight first firstNonnegative firstNormalizes).probability event -
        (source.reweight second secondNonnegative secondNormalizes).probability
          event =
      source.expectation (fun item =>
        (first item - second item) * indicator event item) := by
  rw [source.reweight_probability first firstNonnegative firstNormalizes,
    source.reweight_probability second secondNonnegative secondNormalizes,
    ← source.expectation_sub]
  exact source.expectation_congr _ _ (fun item => by ring1)

/-- Every directed event discrepancy is bounded by the integral of the
positive density difference. -/
theorem reweight_probability_sub_le_positivePart
    {α : Type} (source : Distribution α)
    (first second : α → Coordinate)
    (firstNonnegative : ∀ item, 0 ≤ first item)
    (secondNonnegative : ∀ item, 0 ≤ second item)
    (firstNormalizes : source.expectation first = 1)
    (secondNormalizes : source.expectation second = 1)
    (event : α → Bool) :
    (source.reweight first firstNonnegative firstNormalizes).probability event -
        (source.reweight second secondNonnegative secondNormalizes).probability
          event ≤
      source.expectation (fun item =>
        positiveWeight (first item - second item)) := by
  rw [source.reweight_probability_sub first second firstNonnegative
    secondNonnegative firstNormalizes secondNormalizes event]
  apply source.expectation_mono
  intro atom member
  cases selected : event atom.item
  · simp only [indicator, selected, mul_zero]
    exact positiveWeight_nonneg _
  · simp only [indicator, selected, mul_one]
    exact le_max_left _ _

/-- The density-dominance event attains the entire positive-part integral. -/
theorem reweight_probability_sub_densityDominanceEvent
    {α : Type} (source : Distribution α)
    (first second : α → Coordinate)
    (firstNonnegative : ∀ item, 0 ≤ first item)
    (secondNonnegative : ∀ item, 0 ≤ second item)
    (firstNormalizes : source.expectation first = 1)
    (secondNormalizes : source.expectation second = 1) :
    (source.reweight first firstNonnegative firstNormalizes).probability
          (densityDominanceEvent first second) -
        (source.reweight second secondNonnegative secondNormalizes).probability
          (densityDominanceEvent first second) =
      source.expectation (fun item =>
        positiveWeight (first item - second item)) := by
  rw [source.reweight_probability_sub first second firstNonnegative
    secondNonnegative firstNormalizes secondNormalizes]
  exact source.expectation_congr _ _ (fun item => by
    by_cases order : second item ≤ first item
    · simp only [densityDominanceEvent, order, decide_true, indicator, mul_one,
        positiveWeight_eq_self_of_nonneg (sub_nonneg.mpr order)]
    · have reverse : first item ≤ second item :=
        (RFAP.ConstructiveFraction.lt_of_not_ge_direct order).le
      simp only [densityDominanceEvent, order, decide_false, indicator, mul_zero,
        positiveWeight_eq_zero_of_nonpos (sub_nonpos.mpr reverse)])

/-- Normalised densities have equal positive- and negative-difference
integrals. -/
theorem expectation_positivePart_eq_negativePart_of_normalized
    {α : Type} (source : Distribution α)
    (first second : α → Coordinate)
    (firstNormalizes : source.expectation first = 1)
    (secondNormalizes : source.expectation second = 1) :
    source.expectation (fun item =>
        positiveWeight (first item - second item)) =
      source.expectation (fun item =>
        negativeWeight (first item - second item)) := by
  have differenceZero : source.expectation
      (fun item => first item - second item) = 0 := by
    rw [source.expectation_sub, firstNormalizes, secondNormalizes]
    ring1
  have decomposition : source.expectation
      (fun item => first item - second item) =
      source.expectation (fun item => positiveWeight (first item - second item) -
        negativeWeight (first item - second item)) :=
    source.expectation_congr _ _ (fun item =>
      (positiveWeight_sub_negativeWeight
        (first item - second item)).symm)
  rw [decomposition, source.expectation_sub] at differenceZero
  exact sub_eq_zero.mp differenceZero

/-- L1 density separation is the sum of its positive and negative parts. -/
theorem l1Distance_eq_expectation_positivePart_add_negativePart
    {α : Type} (source : Distribution α)
    (first second : α → Coordinate) :
    source.l1Distance first second =
      source.expectation (fun item =>
        positiveWeight (first item - second item)) +
      source.expectation (fun item =>
        negativeWeight (first item - second item)) := by
  unfold l1Distance
  calc
    source.expectation (fun item => rationalSeparation
        (first item) (second item)) =
        source.expectation (fun item =>
          positiveWeight (first item - second item) +
            negativeWeight (first item - second item)) :=
      source.expectation_congr _ _ (fun item => by
        calc
          rationalSeparation (first item) (second item) =
              rationalSeparation (first item - second item) 0 := by
            unfold rationalSeparation
            congr 1 <;> ring1
          _ = positiveWeight (first item - second item) +
              negativeWeight (first item - second item) :=
            rationalSeparation_zero_eq_parts _)
    _ = source.expectation (fun item =>
          positiveWeight (first item - second item)) +
        source.expectation (fun item =>
          negativeWeight (first item - second item)) :=
      source.expectation_add _ _

/-- Finite Scheffé positive-part formula for total variation. -/
theorem totalVariationDistance_reweight_eq_positivePart
    {α : Type} [DecidableEq α] (source : Distribution α)
    (first second : α → Coordinate)
    (firstNonnegative : ∀ item, 0 ≤ first item)
    (secondNonnegative : ∀ item, 0 ≤ second item)
    (firstNormalizes : source.expectation first = 1)
    (secondNormalizes : source.expectation second = 1) :
    (source.reweight first firstNonnegative firstNormalizes).totalVariationDistance
          (source.reweight second secondNonnegative secondNormalizes) =
      source.expectation (fun item =>
        positiveWeight (first item - second item)) := by
  let firstLaw := source.reweight first firstNonnegative firstNormalizes
  let secondLaw := source.reweight second secondNonnegative secondNormalizes
  apply RFAP.ConstructiveFraction.le_antisymm
  · let event := firstLaw.totalVariationEvent secondLaw
    calc
      firstLaw.totalVariationDistance secondLaw =
          firstLaw.probability event - secondLaw.probability event :=
        (firstLaw.probability_sub_at_totalVariationEvent secondLaw).symm
      _ ≤ source.expectation (fun item =>
          positiveWeight (first item - second item)) :=
        source.reweight_probability_sub_le_positivePart first second
          firstNonnegative secondNonnegative firstNormalizes secondNormalizes
          event
  · let event := densityDominanceEvent first second
    calc
      source.expectation (fun item =>
            positiveWeight (first item - second item)) =
          firstLaw.probability event - secondLaw.probability event :=
        (source.reweight_probability_sub_densityDominanceEvent first second
          firstNonnegative secondNonnegative firstNormalizes
          secondNormalizes).symm
      _ ≤ rationalSeparation (firstLaw.probability event)
          (secondLaw.probability event) := le_max_left _ _
      _ ≤ firstLaw.totalVariationDistance secondLaw :=
        firstLaw.probability_separation_le_totalVariationDistance
          secondLaw event

/-- Finite Scheffé identity: the original-law L1 density separation is
exactly twice total variation of the two reweighted laws. -/
theorem l1Distance_eq_two_mul_totalVariationDistance_reweight
    {α : Type} [DecidableEq α] (source : Distribution α)
    (first second : α → Coordinate)
    (firstNonnegative : ∀ item, 0 ≤ first item)
    (secondNonnegative : ∀ item, 0 ≤ second item)
    (firstNormalizes : source.expectation first = 1)
    (secondNormalizes : source.expectation second = 1) :
    source.l1Distance first second =
      2 * (source.reweight first firstNonnegative firstNormalizes).totalVariationDistance
          (source.reweight second secondNonnegative secondNormalizes) := by
  rw [source.l1Distance_eq_expectation_positivePart_add_negativePart
      first second,
    ← source.expectation_positivePart_eq_negativePart_of_normalized
      first second firstNormalizes secondNormalizes,
    source.totalVariationDistance_reweight_eq_positivePart first second
      firstNonnegative secondNonnegative firstNormalizes secondNormalizes]
  ring1

end Distribution

end FiniteMeasure
