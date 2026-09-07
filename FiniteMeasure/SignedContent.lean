import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.ContentIntegral
import FiniteMeasure.L1

/-!
# Finite rational signed contents

A signed content is a displayed finite list of rationally weighted atoms;
weights need not be nonnegative.  Positive, negative, and total-variation
contents are computed atom by atom.  The Jordan identities and variation
bounds are therefore exact finite calculations, not existence theorems.
-/

namespace FiniteMeasure

/-- One displayed atom with an arbitrary rational signed weight. -/
structure SignedWeighted (α : Type) where
  item : α
  weight : Coordinate

/-- A finite displayed signed content. -/
structure SignedContent (α : Type) where
  atoms : List (SignedWeighted α)

/-- Signed total of a displayed atom list. -/
def signedTotalWeight {α : Type} : List (SignedWeighted α) → Coordinate
  | [] => 0
  | atom :: remaining => atom.weight + signedTotalWeight remaining

/-- Signed weight selected by an executable event. -/
def signedEventWeight {α : Type} :
    List (SignedWeighted α) → (α → Bool) → Coordinate
  | [], _ => 0
  | atom :: remaining, event =>
      (if event atom.item then atom.weight else 0) +
        signedEventWeight remaining event

/-- Signed rational integral over a displayed atom list. -/
def signedIntegralWeight {α : Type} :
    List (SignedWeighted α) → (α → Coordinate) → Coordinate
  | [], _ => 0
  | atom :: remaining, value =>
      atom.weight * value atom.item + signedIntegralWeight remaining value

/-- Pointwise-equal observables have the same signed integral over every
displayed finite atom list. -/
theorem signedIntegralWeight_congr {α : Type}
    (atoms : List (SignedWeighted α)) (left right : α → Coordinate)
    (pointwise : ∀ item, left item = right item) :
    signedIntegralWeight atoms left = signedIntegralWeight atoms right := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [signedIntegralWeight, pointwise atom.item,
        inductionHypothesis]

/-- Computable positive part of one rational signed weight. -/
def positiveWeight (weight : Coordinate) : Coordinate := max weight 0

/-- Computable negative-part magnitude of one rational signed weight. -/
def negativeWeight (weight : Coordinate) : Coordinate := max (-weight) 0

theorem positiveWeight_nonneg (weight : Coordinate) :
    0 ≤ positiveWeight weight :=
  le_max_right _ _

theorem negativeWeight_nonneg (weight : Coordinate) :
    0 ≤ negativeWeight weight :=
  le_max_right _ _

theorem positiveWeight_eq_self_of_nonneg {weight : Coordinate}
    (nonnegative : 0 ≤ weight) : positiveWeight weight = weight :=
  max_eq_left nonnegative

theorem positiveWeight_eq_zero_of_nonpos {weight : Coordinate}
    (nonpositive : weight ≤ 0) : positiveWeight weight = 0 :=
  max_eq_right nonpositive

theorem negativeWeight_eq_zero_of_nonneg {weight : Coordinate}
    (nonnegative : 0 ≤ weight) : negativeWeight weight = 0 := by
  unfold negativeWeight
  exact max_eq_right (neg_nonpos.mpr nonnegative)

theorem negativeWeight_eq_neg_of_nonpos {weight : Coordinate}
    (nonpositive : weight ≤ 0) : negativeWeight weight = -weight := by
  unfold negativeWeight
  exact max_eq_left (neg_nonneg.mpr nonpositive)

/-- Scalar Jordan decomposition over the constructive rationals. -/
theorem positiveWeight_sub_negativeWeight (weight : Coordinate) :
    positiveWeight weight - negativeWeight weight = weight := by
  by_cases nonnegative : 0 ≤ weight
  · have negativeNonpositive : -weight ≤ 0 := neg_nonpos.mpr nonnegative
    rw [positiveWeight, max_eq_left nonnegative,
      negativeWeight, max_eq_right negativeNonpositive]
    ring1
  · have nonpositive : weight ≤ 0 :=
      (RFAP.ConstructiveFraction.lt_of_not_ge_direct nonnegative).le
    have negativeNonnegative : 0 ≤ -weight := neg_nonneg.mpr nonpositive
    rw [positiveWeight, max_eq_right nonpositive,
      negativeWeight, max_eq_left negativeNonnegative]
    ring1

/-- Scalar total variation is the sum of the computed positive and negative
parts. -/
theorem rationalSeparation_zero_eq_parts (weight : Coordinate) :
    rationalSeparation weight 0 =
      positiveWeight weight + negativeWeight weight := by
  unfold rationalSeparation positiveWeight negativeWeight
  rw [sub_zero, zero_sub]
  by_cases nonnegative : 0 ≤ weight
  · have negativeNonpositive : -weight ≤ 0 := neg_nonpos.mpr nonnegative
    have negativeLeWeight : -weight ≤ weight :=
      negativeNonpositive.trans nonnegative
    rw [max_eq_left negativeLeWeight, max_eq_left nonnegative,
      max_eq_right negativeNonpositive, add_zero]
  · have nonpositive : weight ≤ 0 :=
      (RFAP.ConstructiveFraction.lt_of_not_ge_direct nonnegative).le
    have negativeNonnegative : 0 ≤ -weight := neg_nonneg.mpr nonpositive
    have weightLeNegative : weight ≤ -weight :=
      nonpositive.trans negativeNonnegative
    rw [max_eq_right weightLeNegative, max_eq_right nonpositive,
      max_eq_left negativeNonnegative, zero_add]

namespace SignedContent

/-- Explicit finite Hahn sign certificate.  The Boolean event must classify
every displayed atom as nonnegative inside and nonpositive outside.  Such a
certificate is data, since repeated equal items with conflicting signed
weights need not support an item-level classifier. -/
structure HahnCertificate {α : Type} (content : SignedContent α) where
  positiveEvent : α → Bool
  selected_nonnegative : ∀ atom, atom ∈ content.atoms →
    positiveEvent atom.item = true → 0 ≤ atom.weight
  unselected_nonpositive : ∀ atom, atom ∈ content.atoms →
    positiveEvent atom.item = false → atom.weight ≤ 0

/-- The nonnegative positive-part atom associated with a signed atom. -/
def positivePartAtom {α : Type}
    (atom : SignedWeighted α) : Weighted α where
  item := atom.item
  weight := positiveWeight atom.weight
  nonnegative := positiveWeight_nonneg atom.weight

/-- The nonnegative negative-part atom associated with a signed atom. -/
def negativePartAtom {α : Type}
    (atom : SignedWeighted α) : Weighted α where
  item := atom.item
  weight := negativeWeight atom.weight
  nonnegative := negativeWeight_nonneg atom.weight

/-- The total-variation atom associated with a signed atom. -/
def variationAtom {α : Type}
    (atom : SignedWeighted α) : Weighted α where
  item := atom.item
  weight := rationalSeparation atom.weight 0
  nonnegative := rationalSeparation_nonneg atom.weight 0

private theorem positivePartAtom_item {α : Type}
    (atom : SignedWeighted α) : (positivePartAtom atom).item = atom.item := rfl

private theorem positivePartAtom_weight {α : Type}
    (atom : SignedWeighted α) :
    (positivePartAtom atom).weight = positiveWeight atom.weight := rfl

private theorem negativePartAtom_item {α : Type}
    (atom : SignedWeighted α) : (negativePartAtom atom).item = atom.item := rfl

private theorem negativePartAtom_weight {α : Type}
    (atom : SignedWeighted α) :
    (negativePartAtom atom).weight = negativeWeight atom.weight := rfl

private theorem variationAtom_item {α : Type}
    (atom : SignedWeighted α) : (variationAtom atom).item = atom.item := rfl

private theorem variationAtom_weight {α : Type}
    (atom : SignedWeighted α) :
    (variationAtom atom).weight = rationalSeparation atom.weight 0 := rfl

/-- Positive finite content computed from a signed atom list. -/
def positiveContent {α : Type} (content : SignedContent α) : FiniteContent α where
  atoms := content.atoms.map positivePartAtom

/-- Negative-part magnitude as a nonnegative finite content. -/
def negativeContent {α : Type} (content : SignedContent α) : FiniteContent α where
  atoms := content.atoms.map negativePartAtom

/-- Total-variation finite content computed pointwise by symmetric rational
separation from zero. -/
def variationContent {α : Type} (content : SignedContent α) :
    FiniteContent α where
  atoms := content.atoms.map variationAtom

/-- Exact signed total mass. -/
def total {α : Type} (content : SignedContent α) : Coordinate :=
  signedTotalWeight content.atoms

/-- Exact signed mass of an executable event. -/
def measure {α : Type} (content : SignedContent α)
    (event : α → Bool) : Coordinate :=
  signedEventWeight content.atoms event

/-- Exact signed finite integral. -/
def integral {α : Type} (content : SignedContent α)
    (value : α → Coordinate) : Coordinate :=
  signedIntegralWeight content.atoms value

/-- Pointwise equality suffices for equality of exact signed finite
integrals. -/
theorem integral_congr {α : Type} (content : SignedContent α)
    (left right : α → Coordinate)
    (pointwise : ∀ item, left item = right item) :
    content.integral left = content.integral right :=
  signedIntegralWeight_congr content.atoms left right pointwise

/-- Exact integral of pointwise observable magnitude against the computed
total-variation content. -/
def variationIntegral {α : Type} (content : SignedContent α)
    (value : α → Coordinate) : Coordinate :=
  content.variationContent.integral fun item =>
    rationalSeparation (value item) 0

/-- Total variation controls the rational magnitude of every signed finite
integral. -/
theorem integral_bounded_by_variationIntegral {α : Type}
    (content : SignedContent α) (value : α → Coordinate) :
    rationalSeparation (content.integral value) 0 ≤
      content.variationIntegral value := by
  unfold integral variationIntegral variationContent FiniteContent.integral
  induction content.atoms with
  | nil =>
      simp only [signedIntegralWeight, List.map_nil,
        Distribution.expectationWeight, rationalSeparation]
      exact le_rfl
  | cons atom remaining inductionHypothesis =>
      simp only [signedIntegralWeight, List.map_cons,
        Distribution.expectationWeight]
      calc
        rationalSeparation
              (atom.weight * value atom.item +
                signedIntegralWeight remaining value) 0 ≤
            rationalSeparation (atom.weight * value atom.item) 0 +
              rationalSeparation
                (signedIntegralWeight remaining value) 0 :=
          rationalSeparation_add_zero_le _ _
        _ ≤ rationalSeparation (atom.weight * value atom.item) 0 +
            Distribution.expectationWeight
              (remaining.map variationAtom)
              (fun item => rationalSeparation (value item) 0) :=
          add_le_add le_rfl inductionHypothesis
        _ = rationalSeparation atom.weight 0 *
              rationalSeparation (value atom.item) 0 +
            Distribution.expectationWeight
              (remaining.map variationAtom)
              (fun item => rationalSeparation (value item) 0) := by
          rw [rationalSeparation_mul_zero]

@[simp] theorem measure_empty {α : Type} (content : SignedContent α) :
    content.measure (fun _ => false) = 0 := by
  unfold measure
  induction content.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [signedEventWeight, Bool.false_eq_true, ↓reduceIte,
        zero_add, inductionHypothesis]

@[simp] theorem measure_univ {α : Type} (content : SignedContent α) :
    content.measure (fun _ => true) = content.total := by
  unfold measure total
  induction content.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [signedEventWeight, ↓reduceIte, signedTotalWeight,
        inductionHypothesis]

/-- Exact finite Jordan decomposition of every executable event. -/
theorem measure_eq_positive_sub_negative {α : Type}
    (content : SignedContent α) (event : α → Bool) :
    content.measure event =
      content.positiveContent.measure event -
        content.negativeContent.measure event := by
  unfold measure positiveContent negativeContent FiniteContent.measure
  induction content.atoms with
  | nil =>
      simp only [signedEventWeight, List.map_nil, eventWeight]
      ring1
  | cons atom remaining inductionHypothesis =>
      cases selected : event atom.item
      · simp only [signedEventWeight, selected, Bool.false_eq_true,
          ↓reduceIte, zero_add, List.map_cons, eventWeight,
          positivePartAtom_item, negativePartAtom_item,
          inductionHypothesis]
      · simp only [signedEventWeight, selected, ↓reduceIte, List.map_cons,
          eventWeight, positivePartAtom_item, positivePartAtom_weight,
          negativePartAtom_item, negativePartAtom_weight,
          inductionHypothesis]
        have head : atom.weight =
            positiveWeight atom.weight - negativeWeight atom.weight :=
          (positiveWeight_sub_negativeWeight atom.weight).symm
        calc
          atom.weight +
                (eventWeight
                    (remaining.map positivePartAtom) event -
                  eventWeight
                    (remaining.map negativePartAtom) event) =
              (positiveWeight atom.weight - negativeWeight atom.weight) +
                (eventWeight
                    (remaining.map positivePartAtom) event -
                  eventWeight
                    (remaining.map negativePartAtom) event) :=
            congrArg (fun weight => weight +
              (eventWeight
                  (remaining.map positivePartAtom) event -
                eventWeight
                  (remaining.map negativePartAtom) event)) head
          _ = positiveWeight atom.weight +
                eventWeight
                  (remaining.map positivePartAtom) event -
              (negativeWeight atom.weight +
                eventWeight
                  (remaining.map negativePartAtom) event) := by
            ring1

/-- Exact finite Jordan decomposition of signed integrals. -/
theorem integral_eq_positive_sub_negative {α : Type}
    (content : SignedContent α) (value : α → Coordinate) :
    content.integral value =
      content.positiveContent.integral value -
        content.negativeContent.integral value := by
  unfold integral positiveContent negativeContent FiniteContent.integral
  induction content.atoms with
  | nil =>
      simp only [signedIntegralWeight, List.map_nil,
        Distribution.expectationWeight]
      ring1
  | cons atom remaining inductionHypothesis =>
      simp only [signedIntegralWeight, List.map_cons,
        Distribution.expectationWeight, positivePartAtom_item,
        positivePartAtom_weight, negativePartAtom_item,
        negativePartAtom_weight, inductionHypothesis]
      have headScaled : atom.weight * value atom.item =
          positiveWeight atom.weight * value atom.item -
            negativeWeight atom.weight * value atom.item := by
        calc
          atom.weight * value atom.item =
              (positiveWeight atom.weight - negativeWeight atom.weight) *
                value atom.item :=
            congrArg (fun weight => weight * value atom.item)
              (positiveWeight_sub_negativeWeight atom.weight).symm
          _ = positiveWeight atom.weight * value atom.item -
              negativeWeight atom.weight * value atom.item := by ring1
      rw [headScaled]
      ring1

/-- Signed finite integrals are exactly additive in the observable. -/
theorem integral_add {α : Type} (content : SignedContent α)
    (left right : α → Coordinate) :
    content.integral (fun item => left item + right item) =
      content.integral left + content.integral right := by
  rw [content.integral_eq_positive_sub_negative,
    content.integral_eq_positive_sub_negative left,
    content.integral_eq_positive_sub_negative right,
    content.positiveContent.integral_add,
    content.negativeContent.integral_add]
  ring1

/-- Signed finite integrals are exactly homogeneous. -/
theorem integral_scale {α : Type} (content : SignedContent α)
    (factor : Coordinate) (value : α → Coordinate) :
    content.integral (fun item => factor * value item) =
      factor * content.integral value := by
  rw [content.integral_eq_positive_sub_negative,
    content.integral_eq_positive_sub_negative value,
    content.positiveContent.integral_scale,
    content.negativeContent.integral_scale]
  ring1

/-- Signed finite integrals commute with rational subtraction. -/
theorem integral_sub {α : Type} (content : SignedContent α)
    (left right : α → Coordinate) :
    content.integral (fun item => left item - right item) =
      content.integral left - content.integral right := by
  calc
    content.integral (fun item => left item - right item) =
        content.integral (fun item =>
          left item + (-1) * right item) :=
      content.integral_congr _ _ (fun item => by ring1)
    _ = content.integral left +
          content.integral (fun item => (-1) * right item) :=
      content.integral_add left (fun item => (-1) * right item)
    _ = content.integral left + (-1) * content.integral right := by
      rw [content.integral_scale]
    _ = content.integral left - content.integral right := by ring1

/-- Integrating a rational event indicator recovers signed event mass. -/
theorem integral_indicator {α : Type} (content : SignedContent α)
    (event : α → Bool) :
    content.integral (Distribution.indicator event) =
      content.measure event := by
  unfold integral measure
  induction content.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      cases selected : event atom.item <;>
        simp only [signedIntegralWeight, signedEventWeight,
          Distribution.indicator, selected, mul_zero, mul_one, zero_add,
          Bool.false_eq_true, ↓reduceIte, inductionHypothesis]

/-- The exact finite valuation law also holds for signed contents. -/
theorem valuation {α : Type} (content : SignedContent α)
    (first second : α → Bool) :
    content.measure first + content.measure second =
      content.measure (unionEvent first second) +
        content.measure (intersectionEvent first second) := by
  rw [content.measure_eq_positive_sub_negative first,
    content.measure_eq_positive_sub_negative second,
    content.measure_eq_positive_sub_negative (unionEvent first second),
    content.measure_eq_positive_sub_negative
      (intersectionEvent first second)]
  have positiveValuation :=
    content.positiveContent.valuation first second
  have negativeValuation :=
    content.negativeContent.valuation first second
  calc
    (content.positiveContent.measure first -
          content.negativeContent.measure first) +
        (content.positiveContent.measure second -
          content.negativeContent.measure second) =
      (content.positiveContent.measure first +
          content.positiveContent.measure second) -
        (content.negativeContent.measure first +
          content.negativeContent.measure second) := by ring1
    _ = (content.positiveContent.measure (unionEvent first second) +
          content.positiveContent.measure (intersectionEvent first second)) -
        (content.negativeContent.measure (unionEvent first second) +
          content.negativeContent.measure
            (intersectionEvent first second)) :=
      congrArg₂ (fun positive negative => positive - negative)
        positiveValuation negativeValuation
    _ = (content.positiveContent.measure (unionEvent first second) -
          content.negativeContent.measure (unionEvent first second)) +
        (content.positiveContent.measure
            (intersectionEvent first second) -
          content.negativeContent.measure
            (intersectionEvent first second)) := by ring1

/-- Variation content is exactly the sum of positive and negative contents
on every executable event. -/
theorem variation_measure_eq_add {α : Type}
    (content : SignedContent α) (event : α → Bool) :
    content.variationContent.measure event =
      content.positiveContent.measure event +
        content.negativeContent.measure event := by
  unfold variationContent positiveContent negativeContent
    FiniteContent.measure
  induction content.atoms with
  | nil =>
      simp only [List.map_nil, eventWeight, add_zero]
  | cons atom remaining inductionHypothesis =>
      cases selected : event atom.item
      · simp only [List.map_cons, eventWeight, variationAtom_item,
          positivePartAtom_item, negativePartAtom_item, selected, zero_add,
          inductionHypothesis]
      · simp only [List.map_cons, eventWeight, variationAtom_item,
          variationAtom_weight, positivePartAtom_item,
          positivePartAtom_weight, negativePartAtom_item,
          negativePartAtom_weight, selected]
        rw [inductionHypothesis,
          rationalSeparation_zero_eq_parts atom.weight]
        ring1

/-- Total variation controls both directed signed event masses. -/
theorem measure_bounded_by_variation {α : Type}
    (content : SignedContent α) (event : α → Bool) :
    content.measure event ≤ content.variationContent.measure event ∧
      -content.measure event ≤ content.variationContent.measure event := by
  rw [content.measure_eq_positive_sub_negative event,
    content.variation_measure_eq_add event]
  constructor
  · have negativeNonnegative := content.negativeContent.measure_nonneg event
    calc
      content.positiveContent.measure event -
            content.negativeContent.measure event ≤
          content.positiveContent.measure event :=
        sub_le_self _ negativeNonnegative
      _ ≤ content.positiveContent.measure event +
            content.negativeContent.measure event :=
        le_add_of_nonneg_right negativeNonnegative
  · have positiveNonnegative := content.positiveContent.measure_nonneg event
    have negativeNonnegative := content.negativeContent.measure_nonneg event
    calc
      -(content.positiveContent.measure event -
          content.negativeContent.measure event) =
          content.negativeContent.measure event -
            content.positiveContent.measure event := by ring1
      _ ≤ content.positiveContent.measure event +
          content.negativeContent.measure event := by
        calc
          content.negativeContent.measure event -
                content.positiveContent.measure event ≤
              content.negativeContent.measure event :=
            sub_le_self _ positiveNonnegative
          _ ≤ content.positiveContent.measure event +
                content.negativeContent.measure event := by
            simpa only [add_comm] using
              le_add_of_nonneg_right positiveNonnegative

namespace HahnCertificate

/-- Executable ±1 sign observable selected by a finite Hahn certificate. -/
def signObservable {α : Type} {content : SignedContent α}
    (certificate : HahnCertificate content) : α → Coordinate :=
  fun item => if certificate.positiveEvent item then 1 else -1

theorem signObservable_magnitude_one {α : Type}
    {content : SignedContent α} (certificate : HahnCertificate content)
    (item : α) :
    rationalSeparation (certificate.signObservable item) 0 = 1 := by
  cases selected : certificate.positiveEvent item <;>
    simp only [signObservable, selected, ↓reduceIte, rationalSeparation] <;>
    decide

private theorem signedEventWeight_positive_eq {α : Type}
    (event : α → Bool) : ∀ atoms : List (SignedWeighted α),
    (∀ atom, atom ∈ atoms → event atom.item = true →
      0 ≤ atom.weight) →
    (∀ atom, atom ∈ atoms → event atom.item = false →
      atom.weight ≤ 0) →
    signedEventWeight atoms event =
      totalWeight (atoms.map positivePartAtom)
  | [], selectedNonnegative, unselectedNonpositive => rfl
  | atom :: remaining, selectedNonnegative, unselectedNonpositive => by
      have tailSelected : ∀ candidate, candidate ∈ remaining →
          event candidate.item = true → 0 ≤ candidate.weight :=
        fun candidate member selected => selectedNonnegative candidate
          (List.mem_cons_of_mem atom member) selected
      have tailUnselected : ∀ candidate, candidate ∈ remaining →
          event candidate.item = false → candidate.weight ≤ 0 :=
        fun candidate member selected => unselectedNonpositive candidate
          (List.mem_cons_of_mem atom member) selected
      cases selected : event atom.item
      · simp only [signedEventWeight, selected, Bool.false_eq_true,
          ↓reduceIte, zero_add, List.map_cons, totalWeight,
          positivePartAtom_weight]
        rw [positiveWeight_eq_zero_of_nonpos
          (unselectedNonpositive atom List.mem_cons_self selected), zero_add]
        exact signedEventWeight_positive_eq event remaining tailSelected
          tailUnselected
      · simp only [signedEventWeight, selected, ↓reduceIte,
          List.map_cons, totalWeight, positivePartAtom_weight]
        rw [positiveWeight_eq_self_of_nonneg
          (selectedNonnegative atom List.mem_cons_self selected)]
        rw [signedEventWeight_positive_eq event remaining tailSelected
          tailUnselected]

private theorem signedEventWeight_negative_eq {α : Type}
    (event : α → Bool) : ∀ atoms : List (SignedWeighted α),
    (∀ atom, atom ∈ atoms → event atom.item = true →
      0 ≤ atom.weight) →
    (∀ atom, atom ∈ atoms → event atom.item = false →
      atom.weight ≤ 0) →
    signedEventWeight atoms (fun item => !(event item)) =
      -totalWeight (atoms.map negativePartAtom)
  | [], selectedNonnegative, unselectedNonpositive => by
      change (0 : Coordinate) = -0
      ring1
  | atom :: remaining, selectedNonnegative, unselectedNonpositive => by
      have tailSelected : ∀ candidate, candidate ∈ remaining →
          event candidate.item = true → 0 ≤ candidate.weight :=
        fun candidate member selected => selectedNonnegative candidate
          (List.mem_cons_of_mem atom member) selected
      have tailUnselected : ∀ candidate, candidate ∈ remaining →
          event candidate.item = false → candidate.weight ≤ 0 :=
        fun candidate member selected => unselectedNonpositive candidate
          (List.mem_cons_of_mem atom member) selected
      cases selected : event atom.item
      · simp only [signedEventWeight, selected, Bool.not_false,
          ↓reduceIte, List.map_cons, totalWeight,
          negativePartAtom_weight]
        rw [negativeWeight_eq_neg_of_nonpos
          (unselectedNonpositive atom List.mem_cons_self selected)]
        rw [signedEventWeight_negative_eq event remaining tailSelected
          tailUnselected]
        ring1
      · simp only [signedEventWeight, selected, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte, zero_add, List.map_cons, totalWeight,
          negativePartAtom_weight]
        rw [negativeWeight_eq_zero_of_nonneg
          (selectedNonnegative atom List.mem_cons_self selected), zero_add]
        exact signedEventWeight_negative_eq event remaining tailSelected
          tailUnselected

/-- The certified positive event attains the entire positive Jordan mass. -/
theorem measure_positiveEvent_eq_positiveTotal {α : Type}
    {content : SignedContent α} (certificate : HahnCertificate content) :
    content.measure certificate.positiveEvent =
      content.positiveContent.total := by
  unfold SignedContent.measure positiveContent FiniteContent.total
  exact signedEventWeight_positive_eq certificate.positiveEvent content.atoms
    certificate.selected_nonnegative certificate.unselected_nonpositive

/-- The Boolean complement of the certified positive event attains the
negative Jordan mass with its signed orientation. -/
theorem measure_complement_eq_neg_negativeTotal {α : Type}
    {content : SignedContent α} (certificate : HahnCertificate content) :
    content.measure (fun item => !(certificate.positiveEvent item)) =
      -content.negativeContent.total := by
  unfold SignedContent.measure negativeContent FiniteContent.total
  exact signedEventWeight_negative_eq certificate.positiveEvent content.atoms
    certificate.selected_nonnegative certificate.unselected_nonpositive

/-- Every executable event has signed mass at most the certified positive
event. -/
theorem measure_le_positiveEvent {α : Type}
    {content : SignedContent α} (certificate : HahnCertificate content)
    (event : α → Bool) :
    content.measure event ≤ content.measure certificate.positiveEvent := by
  rw [certificate.measure_positiveEvent_eq_positiveTotal,
    content.measure_eq_positive_sub_negative event]
  calc
    content.positiveContent.measure event -
          content.negativeContent.measure event ≤
        content.positiveContent.measure event :=
      sub_le_self _ (content.negativeContent.measure_nonneg event)
    _ ≤ content.positiveContent.total :=
      content.positiveContent.measure_le_total event

/-- The certified negative complement is a lower bound for the signed mass
of every executable event. -/
theorem complement_measure_le {α : Type}
    {content : SignedContent α} (certificate : HahnCertificate content)
    (event : α → Bool) :
    content.measure (fun item => !(certificate.positiveEvent item)) ≤
      content.measure event := by
  rw [certificate.measure_complement_eq_neg_negativeTotal,
    content.measure_eq_positive_sub_negative event]
  have negativeBound := content.negativeContent.measure_le_total event
  have positiveNonnegative := content.positiveContent.measure_nonneg event
  calc
    -content.negativeContent.total ≤
        -content.negativeContent.measure event := RFAP.ConstructiveFraction.neg_le_neg_direct negativeBound
    _ ≤ content.positiveContent.measure event -
          content.negativeContent.measure event := by
      exact le_add_of_nonneg_left positiveNonnegative

/-- The Hahn witness attains the full total variation as the gap between
its positive event and negative complement. -/
theorem variationTotal_eq_measure_sub_complement {α : Type}
    {content : SignedContent α} (certificate : HahnCertificate content) :
    content.variationContent.total =
      content.measure certificate.positiveEvent -
        content.measure (fun item => !(certificate.positiveEvent item)) := by
  have variationTotal : content.variationContent.total =
      content.positiveContent.total + content.negativeContent.total := by
    simpa only [FiniteContent.measure_univ] using
      content.variation_measure_eq_add (fun _ => true)
  rw [variationTotal, certificate.measure_positiveEvent_eq_positiveTotal,
    certificate.measure_complement_eq_neg_negativeTotal]
  ring1

/-- The computed sign observable attains total variation exactly as a signed
finite integral. -/
theorem integral_signObservable_eq_variationTotal {α : Type}
    {content : SignedContent α} (certificate : HahnCertificate content) :
    content.integral certificate.signObservable =
      content.variationContent.total := by
  calc
    content.integral certificate.signObservable =
        content.integral (fun item =>
          Distribution.indicator certificate.positiveEvent item -
            Distribution.indicator
              (fun candidate => !(certificate.positiveEvent candidate))
              item) :=
      content.integral_congr _ _ (fun item => by
        cases selected : certificate.positiveEvent item <;>
          simp [signObservable, Distribution.indicator, selected])
    _ = content.measure certificate.positiveEvent -
          content.measure
            (fun item => !(certificate.positiveEvent item)) := by
      rw [content.integral_sub, content.integral_indicator,
        content.integral_indicator]
    _ = content.variationContent.total :=
      certificate.variationTotal_eq_measure_sub_complement.symm

end HahnCertificate

end SignedContent

end FiniteMeasure
