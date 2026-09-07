import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.RadonNikodymExistence
import FiniteMeasure.SignedContent
import FiniteMeasure.LawCoupling

/-!
# Total variation distance between finite rational laws

The duplicate-free union of two displayed atom catalogues supports their
signed difference.  A decidable comparison of the two singleton masses gives
an executable Hahn event.  For probability distributions this event attains
the largest possible event-probability discrepancy, because the positive and
negative Jordan masses agree.

Thus total variation is an exact rational computation here.  The development
proves its sharp event bound, half-L1 formula, metric laws modulo evaluation
equivalence, contraction under pushforward, and the coupling inequality.
-/

namespace FiniteMeasure

namespace FiniteContent

/-- Signed singleton-mass difference on the consolidated union of two finite
content catalogues. -/
def signedDifference {α : Type} [DecidableEq α]
    (left right : FiniteContent α) : SignedContent α where
  atoms := (left.radonNikodymKeys right).map fun key =>
    { item := key.item
      weight := left.measure (atomEvent key.item) -
        right.measure (atomEvent key.item) }

private theorem signedEventWeight_differenceKeys {α : Type}
    [DecidableEq α] (left right : FiniteContent α)
    (event : α → Bool) :
    ∀ keys : List (Weighted α),
      signedEventWeight
          (keys.map fun key =>
            { item := key.item
              weight := left.measure (atomEvent key.item) -
                right.measure (atomEvent key.item) : SignedWeighted α })
          event =
        left.atomMassSum keys (Distribution.indicator event) -
          right.atomMassSum keys (Distribution.indicator event)
  | [] => by
      change (0 : Coordinate) = 0 - 0
      ring1
  | key :: remaining => by
      simp only [List.map_cons, signedEventWeight, atomMassSum]
      cases selected : event key.item
      · simp only [selected, Bool.false_eq_true, ↓reduceIte,
          Distribution.indicator,
          signedEventWeight_differenceKeys left right event remaining]
        ring1
      · simp only [selected, ↓reduceIte, Distribution.indicator, mul_one,
          signedEventWeight_differenceKeys left right event remaining]
        ring1

/-- Singleton-mass differences reconstruct arbitrary rational observables as
well as Boolean events. -/
private theorem signedIntegralWeight_differenceKeys {α : Type}
    [DecidableEq α] (left right : FiniteContent α)
    (value : α → Coordinate) :
    ∀ keys : List (Weighted α),
      signedIntegralWeight
          (keys.map fun key =>
            { item := key.item
              weight := left.measure (atomEvent key.item) -
                right.measure (atomEvent key.item) : SignedWeighted α })
          value =
        left.atomMassSum keys value - right.atomMassSum keys value
  | [] => by
      change (0 : Coordinate) = 0 - 0
      ring1
  | key :: remaining => by
      simp only [List.map_cons, signedIntegralWeight, atomMassSum,
        signedIntegralWeight_differenceKeys left right value remaining]
      ring1

/-- The computed signed table evaluates every event as left mass minus right
mass. -/
theorem signedDifference_measure {α : Type} [DecidableEq α]
    (left right : FiniteContent α) (event : α → Bool) :
    (left.signedDifference right).measure event =
      left.measure event - right.measure event := by
  unfold signedDifference SignedContent.measure
  rw [signedEventWeight_differenceKeys]
  rw [left.atomMassSum_eq_integral (Distribution.indicator event)
      (left.radonNikodymKeys right)
      (left.radonNikodymKeys_noRepeated right)
      (left.payloadsCovered_radonNikodymKeys_left right),
    right.atomMassSum_eq_integral (Distribution.indicator event)
      (left.radonNikodymKeys right)
      (left.radonNikodymKeys_noRepeated right)
      (left.payloadsCovered_radonNikodymKeys_right right),
    left.integral_indicator, right.integral_indicator]

/-- The computed signed table integrates every rational observable as the
left integral minus the right integral. -/
theorem signedDifference_integral {α : Type} [DecidableEq α]
    (left right : FiniteContent α) (value : α → Coordinate) :
    (left.signedDifference right).integral value =
      left.integral value - right.integral value := by
  unfold signedDifference SignedContent.integral
  rw [signedIntegralWeight_differenceKeys]
  rw [left.atomMassSum_eq_integral value
      (left.radonNikodymKeys right)
      (left.radonNikodymKeys_noRepeated right)
      (left.payloadsCovered_radonNikodymKeys_left right),
    right.atomMassSum_eq_integral value
      (left.radonNikodymKeys right)
      (left.radonNikodymKeys_noRepeated right)
      (left.payloadsCovered_radonNikodymKeys_right right)]

/-- The total signed mass is the difference of the two total masses. -/
theorem signedDifference_total {α : Type} [DecidableEq α]
    (left right : FiniteContent α) :
    (left.signedDifference right).total = left.total - right.total := by
  calc
    (left.signedDifference right).total =
        (left.signedDifference right).measure (fun _ => true) :=
      ((left.signedDifference right).measure_univ).symm
    _ = left.measure (fun _ => true) - right.measure (fun _ => true) :=
      left.signedDifference_measure right (fun _ => true)
    _ = left.total - right.total := by
      rw [left.measure_univ, right.measure_univ]

/-- Comparison of exact singleton masses is an executable Hahn
classification for the signed difference. -/
def signedDifferenceHahnCertificate {α : Type} [DecidableEq α]
    (left right : FiniteContent α) :
    SignedContent.HahnCertificate (left.signedDifference right) where
  positiveEvent := fun item =>
    decide (right.measure (atomEvent item) ≤
      left.measure (atomEvent item))
  selected_nonnegative := by
    intro atom member selected
    unfold signedDifference at member
    rcases QuotientFreeList.mem_map.mp member with ⟨key, keyMember, equal⟩
    subst atom
    exact sub_nonneg.mpr (of_decide_eq_true selected)
  unselected_nonpositive := by
    intro atom member unselected
    unfold signedDifference at member
    rcases QuotientFreeList.mem_map.mp member with ⟨key, keyMember, equal⟩
    subst atom
    apply sub_nonpos.mpr
    apply (RFAP.ConstructiveFraction.lt_of_not_ge_direct ?_).le
    intro order
    have selected : decide
        (right.measure (atomEvent key.item) ≤
          left.measure (atomEvent key.item)) = true :=
      decide_eq_true_eq.mpr order
    rw [selected] at unselected
    exact Bool.noConfusion unselected

end FiniteContent

namespace Distribution

/-- Signed difference of two finite probability laws. -/
def signedDifference {α : Type} [DecidableEq α]
    (left right : Distribution α) : SignedContent α :=
  left.toFiniteContent.signedDifference right.toFiniteContent

/-- The executable event on which the left singleton mass is at least the
right singleton mass. -/
def totalVariationEvent {α : Type} [DecidableEq α]
    (left right : Distribution α) : α → Bool :=
  (left.toFiniteContent.signedDifferenceHahnCertificate
    right.toFiniteContent).positiveEvent

/-- Exact total variation distance, computed as the positive Jordan mass of
the signed difference. -/
def totalVariationDistance {α : Type} [DecidableEq α]
    (left right : Distribution α) : Coordinate :=
  (left.signedDifference right).positiveContent.total

/-- Full atomic L1 separation of two finite probability laws. -/
def atomMassL1Distance {α : Type} [DecidableEq α]
    (left right : Distribution α) : Coordinate :=
  (left.signedDifference right).variationContent.total

theorem signedDifference_total_eq_zero {α : Type} [DecidableEq α]
    (left right : Distribution α) :
    (left.signedDifference right).total = 0 := by
  unfold signedDifference
  rw [FiniteContent.signedDifference_total,
    left.toFiniteContent_total, right.toFiniteContent_total]
  ring1

/-- Equal total mass makes the positive and negative Jordan masses equal. -/
theorem signedDifference_positiveTotal_eq_negativeTotal
    {α : Type} [DecidableEq α] (left right : Distribution α) :
    (left.signedDifference right).positiveContent.total =
      (left.signedDifference right).negativeContent.total := by
  have decomposition :=
    (left.signedDifference right).measure_eq_positive_sub_negative
      (fun _ => true)
  rw [(left.signedDifference right).measure_univ,
    (left.signedDifference right).positiveContent.measure_univ,
    (left.signedDifference right).negativeContent.measure_univ,
    left.signedDifference_total_eq_zero right] at decomposition
  exact sub_eq_zero.mp decomposition.symm

theorem totalVariationDistance_nonnegative {α : Type} [DecidableEq α]
    (left right : Distribution α) :
    0 ≤ left.totalVariationDistance right := by
  unfold totalVariationDistance
  rw [← (left.signedDifference right).positiveContent.measure_univ]
  exact (left.signedDifference right).positiveContent.measure_nonneg _

/-- The computed Hahn event exactly attains total variation. -/
theorem probability_sub_at_totalVariationEvent
    {α : Type} [DecidableEq α] (left right : Distribution α) :
    left.probability (left.totalVariationEvent right) -
        right.probability (left.totalVariationEvent right) =
      left.totalVariationDistance right := by
  let certificate :=
    left.toFiniteContent.signedDifferenceHahnCertificate
      right.toFiniteContent
  calc
    left.probability (left.totalVariationEvent right) -
          right.probability (left.totalVariationEvent right) =
        (left.signedDifference right).measure
          (left.totalVariationEvent right) :=
      (left.toFiniteContent.signedDifference_measure right.toFiniteContent
        (left.totalVariationEvent right)).symm
    _ = (left.signedDifference right).positiveContent.total := by
      change (left.signedDifference right).measure
          certificate.positiveEvent =
        (left.signedDifference right).positiveContent.total
      exact certificate.measure_positiveEvent_eq_positiveTotal
    _ = left.totalVariationDistance right := rfl

/-- Every executable event discrepancy is sharply bounded by total
variation. -/
theorem probability_separation_le_totalVariationDistance
    {α : Type} [DecidableEq α] (left right : Distribution α)
    (event : α → Bool) :
    rationalSeparation (left.probability event) (right.probability event) ≤
      left.totalVariationDistance right := by
  let difference := left.signedDifference right
  let certificate :=
    left.toFiniteContent.signedDifferenceHahnCertificate
      right.toFiniteContent
  have measured : difference.measure event =
      left.probability event - right.probability event :=
    left.toFiniteContent.signedDifference_measure right.toFiniteContent event
  have upper : difference.measure event ≤
      difference.positiveContent.total := by
    calc
      difference.measure event ≤
          difference.measure certificate.positiveEvent :=
        certificate.measure_le_positiveEvent event
      _ = difference.positiveContent.total :=
        certificate.measure_positiveEvent_eq_positiveTotal
  have lower : -difference.positiveContent.total ≤
      difference.measure event := by
    calc
      -difference.positiveContent.total =
          -difference.negativeContent.total := by
        rw [left.signedDifference_positiveTotal_eq_negativeTotal right]
      _ = difference.measure
          (fun item => !(certificate.positiveEvent item)) :=
        certificate.measure_complement_eq_neg_negativeTotal.symm
      _ ≤ difference.measure event :=
        certificate.complement_measure_le event
  have negativeUpper : -difference.measure event ≤
      difference.positiveContent.total := by
    have reversed := RFAP.ConstructiveFraction.neg_le_neg_direct lower
    simpa only [neg_neg] using reversed
  unfold rationalSeparation totalVariationDistance
  apply max_le
  · rw [← measured]
    exact upper
  · calc
      right.probability event - left.probability event =
          -(left.probability event - right.probability event) := by ring1
      _ = -difference.measure event := by rw [measured]
      _ ≤ difference.positiveContent.total := negativeUpper

/-- Total variation of probability laws is at most one. -/
theorem totalVariationDistance_le_one {α : Type} [DecidableEq α]
    (left right : Distribution α) :
    left.totalVariationDistance right ≤ 1 := by
  rw [← left.probability_sub_at_totalVariationEvent right]
  exact (sub_le_self _
    (right.probability_nonneg (left.totalVariationEvent right))).trans
      (left.probability_le_one (left.totalVariationEvent right))

/-- A nonnegative observable with a displayed global upper bound has
expectation discrepancy at most that bound times total variation. -/
theorem expectation_separation_le_bound_mul_totalVariationDistance
    {α : Type} [DecidableEq α] (left right : Distribution α)
    (value : α → Coordinate) (bound : Coordinate)
    (_boundNonnegative : 0 ≤ bound)
    (nonnegative : ∀ item, 0 ≤ value item)
    (bounded : ∀ item, value item ≤ bound) :
    rationalSeparation (left.expectation value) (right.expectation value) ≤
      bound * left.totalVariationDistance right := by
  let difference := left.signedDifference right
  have measured : difference.integral value =
      left.expectation value - right.expectation value :=
    left.toFiniteContent.signedDifference_integral
      right.toFiniteContent value
  have positiveNonnegative :
      0 ≤ difference.positiveContent.integral value := by
    apply difference.positiveContent.integral_nonneg
    intro atom member
    exact nonnegative atom.item
  have negativeNonnegative :
      0 ≤ difference.negativeContent.integral value := by
    apply difference.negativeContent.integral_nonneg
    intro atom member
    exact nonnegative atom.item
  have positiveBound : difference.positiveContent.integral value ≤
      difference.positiveContent.total * bound := by
    calc
      difference.positiveContent.integral value ≤
          difference.positiveContent.integral (fun _ => bound) := by
        apply difference.positiveContent.integral_mono
        intro atom member
        exact bounded atom.item
      _ = difference.positiveContent.total * bound :=
        difference.positiveContent.integral_constant bound
  have negativeBound : difference.negativeContent.integral value ≤
      difference.negativeContent.total * bound := by
    calc
      difference.negativeContent.integral value ≤
          difference.negativeContent.integral (fun _ => bound) := by
        apply difference.negativeContent.integral_mono
        intro atom member
        exact bounded atom.item
      _ = difference.negativeContent.total * bound :=
        difference.negativeContent.integral_constant bound
  have upper : difference.integral value ≤
      bound * difference.positiveContent.total := by
    rw [difference.integral_eq_positive_sub_negative]
    calc
      difference.positiveContent.integral value -
            difference.negativeContent.integral value ≤
          difference.positiveContent.integral value :=
        sub_le_self _ negativeNonnegative
      _ ≤ difference.positiveContent.total * bound := positiveBound
      _ = bound * difference.positiveContent.total := by ring1
  have negativeUpper : -difference.integral value ≤
      bound * difference.positiveContent.total := by
    rw [difference.integral_eq_positive_sub_negative]
    calc
      -(difference.positiveContent.integral value -
            difference.negativeContent.integral value) =
          difference.negativeContent.integral value -
            difference.positiveContent.integral value := by ring1
      _ ≤ difference.negativeContent.integral value :=
        sub_le_self _ positiveNonnegative
      _ ≤ difference.negativeContent.total * bound := negativeBound
      _ = bound * difference.positiveContent.total := by
        rw [← left.signedDifference_positiveTotal_eq_negativeTotal right]
        ring1
  unfold rationalSeparation totalVariationDistance
  apply max_le
  · rw [← measured]
    exact upper
  · calc
      right.expectation value - left.expectation value =
          -(left.expectation value - right.expectation value) := by ring1
      _ = -difference.integral value := by rw [measured]
      _ ≤ bound * difference.positiveContent.total := negativeUpper

/-- In particular, every rational test taking values in `[0,1]` is
controlled sharply by total variation. -/
theorem expectation_separation_le_totalVariationDistance_of_unitInterval
    {α : Type} [DecidableEq α] (left right : Distribution α)
    (value : α → Coordinate)
    (nonnegative : ∀ item, 0 ≤ value item)
    (atMostOne : ∀ item, value item ≤ 1) :
    rationalSeparation (left.expectation value) (right.expectation value) ≤
      left.totalVariationDistance right := by
  have bounded :=
    left.expectation_separation_le_bound_mul_totalVariationDistance right
      value 1 (by decide) nonnegative atMostOne
  simpa only [one_mul] using bounded

/-- A rational observable confined to `[lower, upper]` has expectation
discrepancy bounded by its oscillation times total variation. -/
theorem expectation_separation_le_oscillation_mul_totalVariationDistance
    {α : Type} [DecidableEq α] (left right : Distribution α)
    (value : α → Coordinate) (lower upper : Coordinate)
    (order : lower ≤ upper)
    (lowerBound : ∀ item, lower ≤ value item)
    (upperBound : ∀ item, value item ≤ upper) :
    rationalSeparation (left.expectation value) (right.expectation value) ≤
      (upper - lower) * left.totalVariationDistance right := by
  let shifted := fun item => value item - lower
  have shiftedNonnegative : ∀ item, 0 ≤ shifted item :=
    fun item => sub_nonneg.mpr (lowerBound item)
  have shiftedBounded : ∀ item, shifted item ≤ upper - lower :=
    fun item => RFAP.ConstructiveFraction.sub_le_sub_right_direct (upperBound item) lower
  have estimate :=
    left.expectation_separation_le_bound_mul_totalVariationDistance right
      shifted (upper - lower) (sub_nonneg.mpr order)
      shiftedNonnegative shiftedBounded
  have leftShift : left.expectation shifted =
      left.expectation value - lower := by
    unfold shifted
    rw [left.expectation_sub, left.expectation_constant]
  have rightShift : right.expectation shifted =
      right.expectation value - lower := by
    unfold shifted
    rw [right.expectation_sub, right.expectation_constant]
  rw [leftShift, rightShift] at estimate
  have separationShift : rationalSeparation
      (left.expectation value - lower) (right.expectation value - lower) =
      rationalSeparation (left.expectation value)
        (right.expectation value) := by
    unfold rationalSeparation
    congr 1 <;> ring1
  rw [separationShift] at estimate
  exact estimate

/-- Atomic L1 separation is exactly twice total variation. -/
theorem atomMassL1Distance_eq_two_mul_totalVariationDistance
    {α : Type} [DecidableEq α] (left right : Distribution α) :
    left.atomMassL1Distance right =
      2 * left.totalVariationDistance right := by
  have variationDecomposition :
      (left.signedDifference right).variationContent.total =
        (left.signedDifference right).positiveContent.total +
          (left.signedDifference right).negativeContent.total := by
    simpa only [FiniteContent.measure_univ] using
      (left.signedDifference right).variation_measure_eq_add
        (fun _ => true)
  unfold atomMassL1Distance totalVariationDistance
  rw [variationDecomposition,
    ← left.signedDifference_positiveTotal_eq_negativeTotal right]
  ring1

/-- Swapping the laws leaves total variation unchanged. -/
theorem totalVariationDistance_symm {α : Type} [DecidableEq α]
    (left right : Distribution α) :
    left.totalVariationDistance right =
      right.totalVariationDistance left := by
  apply RFAP.ConstructiveFraction.le_antisymm
  · calc
      left.totalVariationDistance right =
          left.probability (left.totalVariationEvent right) -
            right.probability (left.totalVariationEvent right) :=
        (left.probability_sub_at_totalVariationEvent right).symm
      _ ≤ rationalSeparation
          (right.probability (left.totalVariationEvent right))
          (left.probability (left.totalVariationEvent right)) :=
        le_max_right _ _
      _ ≤ right.totalVariationDistance left :=
        right.probability_separation_le_totalVariationDistance left _
  · calc
      right.totalVariationDistance left =
          right.probability (right.totalVariationEvent left) -
            left.probability (right.totalVariationEvent left) :=
        (right.probability_sub_at_totalVariationEvent left).symm
      _ ≤ rationalSeparation
          (left.probability (right.totalVariationEvent left))
          (right.probability (right.totalVariationEvent left)) :=
        le_max_right _ _
      _ ≤ left.totalVariationDistance right :=
        left.probability_separation_le_totalVariationDistance right _

/-- Total variation satisfies the triangle inequality by testing the Hahn
event for the two endpoints. -/
theorem totalVariationDistance_triangle {α : Type} [DecidableEq α]
    (left middle right : Distribution α) :
    left.totalVariationDistance right ≤
      left.totalVariationDistance middle +
        middle.totalVariationDistance right := by
  let event := left.totalVariationEvent right
  calc
    left.totalVariationDistance right =
        left.probability event - right.probability event :=
      (left.probability_sub_at_totalVariationEvent right).symm
    _ = (left.probability event - middle.probability event) +
        (middle.probability event - right.probability event) := by ring1
    _ ≤ rationalSeparation (left.probability event)
          (middle.probability event) +
        rationalSeparation (middle.probability event)
          (right.probability event) :=
      add_le_add (le_max_left _ _) (le_max_left _ _)
    _ ≤ left.totalVariationDistance middle +
        middle.totalVariationDistance right :=
      add_le_add
        (left.probability_separation_le_totalVariationDistance middle event)
        (middle.probability_separation_le_totalVariationDistance right event)

/-- Vanishing total variation is exactly observational equivalence of the
two finite laws. -/
theorem totalVariationDistance_eq_zero_iff_evaluationEquivalent
    {α : Type} [DecidableEq α] (left right : Distribution α) :
    left.totalVariationDistance right = 0 ↔
      EvaluationEquivalent left right := by
  constructor
  · intro zero
    have probabilityEqual : ∀ event : α → Bool,
        left.probability event = right.probability event := by
      intro event
      have bounded :=
        left.probability_separation_le_totalVariationDistance right event
      rw [zero] at bounded
      have separationZero := RFAP.ConstructiveFraction.le_antisymm _ _
        bounded (rationalSeparation_nonneg _ _)
      exact (rationalSeparation_eq_zero_iff _ _).mp separationZero
    have contentEquivalent : FiniteContent.EvaluationEquivalent
        left.toFiniteContent right.toFiniteContent :=
      FiniteContent.EvaluationEquivalent.of_atom_measure_eq fun item =>
        probabilityEqual (atomEvent item)
    exact
      { probability_eq := probabilityEqual
        expectation_eq := contentEquivalent.integral_eq }
  · intro equivalent
    rw [← left.probability_sub_at_totalVariationEvent right,
      equivalent.probability_eq]
    ring1

/-- Deterministic postprocessing cannot increase total variation. -/
theorem totalVariationDistance_map_le {α β : Type}
    [DecidableEq α] [DecidableEq β]
    (left right : Distribution α) (function : α → β) :
    (left.map function).totalVariationDistance (right.map function) ≤
      left.totalVariationDistance right := by
  let event := (left.map function).totalVariationEvent (right.map function)
  calc
    (left.map function).totalVariationDistance (right.map function) =
        (left.map function).probability event -
          (right.map function).probability event :=
      ((left.map function).probability_sub_at_totalVariationEvent
        (right.map function)).symm
    _ = left.probability (fun item => event (function item)) -
        right.probability (fun item => event (function item)) := by
      rw [left.map_probability, right.map_probability]
    _ ≤ rationalSeparation
        (left.probability (fun item => event (function item)))
        (right.probability (fun item => event (function item))) :=
      le_max_left _ _
    _ ≤ left.totalVariationDistance right :=
      left.probability_separation_le_totalVariationDistance right _

/-- Passing both laws through the same finite stochastic kernel cannot
increase total variation. -/
theorem totalVariationDistance_bind_le {α β : Type}
    [DecidableEq α] [DecidableEq β]
    (left right : Distribution α) (transition : α → Distribution β) :
    (left.bind transition).totalVariationDistance
        (right.bind transition) ≤
      left.totalVariationDistance right := by
  let event := (left.bind transition).totalVariationEvent
    (right.bind transition)
  let eventProbability := fun item => (transition item).probability event
  calc
    (left.bind transition).totalVariationDistance
          (right.bind transition) =
        (left.bind transition).probability event -
          (right.bind transition).probability event :=
      ((left.bind transition).probability_sub_at_totalVariationEvent
        (right.bind transition)).symm
    _ = left.expectation eventProbability -
        right.expectation eventProbability := by
      rw [left.bind_probability, right.bind_probability]
    _ ≤ rationalSeparation (left.expectation eventProbability)
        (right.expectation eventProbability) :=
      le_max_left _ _
    _ ≤ left.totalVariationDistance right := by
      apply left.expectation_separation_le_totalVariationDistance_of_unitInterval
        right eventProbability
      · intro item
        exact (transition item).probability_nonneg event
      · intro item
        exact (transition item).probability_le_one event

/-- Total variation is convex under a common rational mixture weight. -/
theorem totalVariationDistance_mixture_le
    {α : Type} [DecidableEq α]
    (leftFirst leftSecond rightFirst rightSecond : Distribution α)
    (weight : MixingWeight) :
    (leftFirst.mixture rightFirst weight).totalVariationDistance
        (leftSecond.mixture rightSecond weight) ≤
      weight.coefficient *
          leftFirst.totalVariationDistance leftSecond +
        weight.complement *
          rightFirst.totalVariationDistance rightSecond := by
  let event := (leftFirst.mixture rightFirst weight).totalVariationEvent
    (leftSecond.mixture rightSecond weight)
  have leftBound : leftFirst.probability event -
        leftSecond.probability event ≤
      leftFirst.totalVariationDistance leftSecond :=
    (le_max_left _ _).trans
      (leftFirst.probability_separation_le_totalVariationDistance
        leftSecond event)
  have rightBound : rightFirst.probability event -
        rightSecond.probability event ≤
      rightFirst.totalVariationDistance rightSecond :=
    (le_max_left _ _).trans
      (rightFirst.probability_separation_le_totalVariationDistance
        rightSecond event)
  calc
    (leftFirst.mixture rightFirst weight).totalVariationDistance
          (leftSecond.mixture rightSecond weight) =
        (leftFirst.mixture rightFirst weight).probability event -
          (leftSecond.mixture rightSecond weight).probability event :=
      ((leftFirst.mixture rightFirst weight).probability_sub_at_totalVariationEvent
          (leftSecond.mixture rightSecond weight)).symm
    _ = weight.coefficient *
          (leftFirst.probability event - leftSecond.probability event) +
        weight.complement *
          (rightFirst.probability event - rightSecond.probability event) := by
      rw [leftFirst.mixture_probability rightFirst weight,
        leftSecond.mixture_probability rightSecond weight]
      ring1
    _ ≤ weight.coefficient *
          leftFirst.totalVariationDistance leftSecond +
        weight.complement *
          rightFirst.totalVariationDistance rightSecond :=
      add_le_add
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          leftBound weight.nonnegative)
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct rightBound
          weight.complement_nonnegative)

/-- Total variation depends only on exact event evaluations, not on the
layout of either displayed atom table. -/
theorem totalVariationDistance_eq_of_evaluationEquivalent
    {α : Type} [DecidableEq α]
    {leftFirst leftSecond rightFirst rightSecond : Distribution α}
    (leftEquivalent : EvaluationEquivalent leftFirst leftSecond)
    (rightEquivalent : EvaluationEquivalent rightFirst rightSecond) :
    leftFirst.totalVariationDistance rightFirst =
      leftSecond.totalVariationDistance rightSecond := by
  apply RFAP.ConstructiveFraction.le_antisymm
  · let event := leftFirst.totalVariationEvent rightFirst
    calc
      leftFirst.totalVariationDistance rightFirst =
          leftFirst.probability event - rightFirst.probability event :=
        (leftFirst.probability_sub_at_totalVariationEvent rightFirst).symm
      _ = leftSecond.probability event - rightSecond.probability event := by
        rw [leftEquivalent.probability_eq event,
          rightEquivalent.probability_eq event]
      _ ≤ rationalSeparation (leftSecond.probability event)
          (rightSecond.probability event) := le_max_left _ _
      _ ≤ leftSecond.totalVariationDistance rightSecond :=
        leftSecond.probability_separation_le_totalVariationDistance
          rightSecond event
  · let event := leftSecond.totalVariationEvent rightSecond
    calc
      leftSecond.totalVariationDistance rightSecond =
          leftSecond.probability event - rightSecond.probability event :=
        (leftSecond.probability_sub_at_totalVariationEvent rightSecond).symm
      _ = leftFirst.probability event - rightFirst.probability event := by
        rw [← leftEquivalent.probability_eq event,
          ← rightEquivalent.probability_eq event]
      _ ≤ rationalSeparation (leftFirst.probability event)
          (rightFirst.probability event) := le_max_left _ _
      _ ≤ leftFirst.totalVariationDistance rightFirst :=
        leftFirst.probability_separation_le_totalVariationDistance
          rightFirst event

end Distribution

namespace LawCoupling

/-- Every displayed coupling bounds total variation by its exact mismatch
probability under equality. -/
theorem totalVariationDistance_le_mismatchProbability
    {α : Type} [DecidableEq α]
    {left right : Distribution α} (witness : LawCoupling left right) :
    left.totalVariationDistance right ≤
      witness.mismatchProbability equalityRelation := by
  let event := left.totalVariationEvent right
  have agree : witness.coupling.EventsAgreeOn equalityRelation event event := by
    intro atom member related
    have same : atom.item.1 = atom.item.2 := by
      unfold equalityRelation at related
      exact of_decide_eq_true related
    rw [same]
  have close := witness.probability_close_of_eventsAgree
    equalityRelation event event agree
  calc
    left.totalVariationDistance right =
        left.probability event - right.probability event :=
      (left.probability_sub_at_totalVariationEvent right).symm
    _ ≤ witness.mismatchProbability equalityRelation := close.2

end LawCoupling

end FiniteMeasure
