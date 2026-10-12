module

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Integral
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
public import Purelib.Data.Rat.PositiveNegativePart
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

section
public section

/-!
# Finite rational signed contents

A signed content is a displayed finite list of rationally weighted atoms;
weights need not be nonnegative.  Positive, negative, and total-variation
contents are computed atom by atom.  The Jordan identities and variation
bounds are therefore exact finite calculations, not existence theorems.
-/

namespace Purelib.Measure

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- Retain one exact payload occurrence with an unrestricted rational signed weight. -/
structure SignedWeighted (α : Type) where
  /-- The exact retained payload occurrence. -/ item : α
  /-- Its original unrestricted signed rational weight. -/ weight : Fraction.Rational

constructive_injectivity SignedWeighted

set_option genInjectivity false in
/-- Represent finite signed content by its exact ordered list of signed weighted occurrences.

Repeated payloads retain separate weights and positions. Positive, negative and variation readbacks operate on these
original occurrence weights before any cancellation. -/
structure SignedContent (α : Type) where
  /-- The exact ordered finite list of signed weighted occurrences. -/ atoms : List (SignedWeighted α)

constructive_injectivity SignedContent

section
open Purelib.Data.Rat
/-- Sum the exact retained signed occurrence weights in list order. -/
@[expose] def signedTotalWeight {α : Type} : List (SignedWeighted α) → Fraction.Rational
  | [] => 0
  | atom :: remaining => atom.weight + signedTotalWeight remaining

/-- Sum original signed weights at occurrences selected by the supplied Boolean event. -/
@[expose] def signedEventWeight {α : Type} :
    List (SignedWeighted α) → (α → Bool) → Fraction.Rational
  | [], _ => 0
  | atom :: remaining, event =>
      (if event atom.item then atom.weight else 0) +
        signedEventWeight remaining event

/-- Sum each original signed occurrence weight times its exact observable value. -/
@[expose] def signedIntegralWeight {α : Type} :
    List (SignedWeighted α) → (α → Fraction.Rational) → Fraction.Rational
  | [], _ => 0
  | atom :: remaining, value =>
      atom.weight * value atom.item + signedIntegralWeight remaining value

/-- Pointwise equal observables give the same integral over the exact retained signed atom list. -/
theorem signedIntegralWeight_congr {α : Type}
    (atoms : List (SignedWeighted α)) (left right : α → Fraction.Rational)
    (pointwise : ∀ item, left item = right item) :
    signedIntegralWeight atoms left = signedIntegralWeight atoms right := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, signedIntegralWeight, pointwise atom.item,
        inductionHypothesis]
      rfl

end

namespace SignedContent

section
open Purelib
/-- Read the same payload with the nonnegative positive part of its original signed weight. -/
@[expose] def positivePartAtom {α : Type}
    (atom : SignedWeighted α) : Weighted α where
  item := atom.item
  weight := Data.Rat.positiveWeight atom.weight
  nonnegative := Data.Rat.positiveWeight_nonneg atom.weight

/-- Read the same payload with the nonnegative negative part of its original signed weight. -/
@[expose] def negativePartAtom {α : Type}
    (atom : SignedWeighted α) : Weighted α where
  item := atom.item
  weight := Data.Rat.negativeWeight atom.weight
  nonnegative := Data.Rat.negativeWeight_nonneg atom.weight

end

open Purelib.Data.Rat in
/-- Read the same payload with the rational magnitude of its original signed weight. -/
@[expose] def variationAtom {α : Type}
    (atom : SignedWeighted α) : Weighted α where
  item := atom.item
  weight := Distance.rationalSeparation atom.weight 0
  nonnegative := Distance.rationalSeparation_nonneg atom.weight 0

/-- Positive-part readback retains the exact original payload. -/
private theorem positivePartAtom_item {α : Type}
    (atom : SignedWeighted α) : (positivePartAtom atom).item = atom.item := rfl

open Purelib in
/-- Positive-part readback uses the exact positive part of the original signed weight. -/
public theorem positivePartAtom_weight {α : Type}
    (atom : SignedWeighted α) :
    (positivePartAtom atom).weight = Data.Rat.positiveWeight atom.weight := rfl

/-- Negative-part readback retains the exact original payload. -/
private theorem negativePartAtom_item {α : Type}
    (atom : SignedWeighted α) : (negativePartAtom atom).item = atom.item := rfl

open Purelib in
/-- Negative-part readback uses the exact negative part of the original signed weight. -/
public theorem negativePartAtom_weight {α : Type}
    (atom : SignedWeighted α) :
    (negativePartAtom atom).weight = Data.Rat.negativeWeight atom.weight := rfl

/-- Variation readback retains the exact original payload. -/
private theorem variationAtom_item {α : Type}
    (atom : SignedWeighted α) : (variationAtom atom).item = atom.item := rfl

open Purelib.Data.Rat in
/-- Variation readback uses the exact magnitude of the original signed weight. -/
private theorem variationAtom_weight {α : Type}
    (atom : SignedWeighted α) :
    (variationAtom atom).weight = Distance.rationalSeparation atom.weight 0 := rfl

/-- Map the original signed occurrence list to its exact nonnegative positive-weight content. -/
@[expose] def positiveContent {α : Type} (content : SignedContent α) : Content α where
  atoms := content.atoms.map positivePartAtom

/-- Map the original signed occurrence list to its exact nonnegative negative-weight content. -/
@[expose] def negativeContent {α : Type} (content : SignedContent α) : Content α where
  atoms := content.atoms.map negativePartAtom

/-- Map each original occurrence to its weight magnitude, retaining order and repetitions. -/
@[expose] def variationContent {α : Type} (content : SignedContent α) :
    Content α where
  atoms := content.atoms.map variationAtom

section
open Purelib.Data.Rat
/-- Read the signed sum of the exact retained content occurrence weights. -/
@[expose] def total {α : Type} (content : SignedContent α) : Fraction.Rational :=
  signedTotalWeight content.atoms

/-- Read the signed weight selected by the exact Boolean event. -/
@[expose] def measure {α : Type} (content : SignedContent α)
    (event : α → Bool) : Fraction.Rational :=
  signedEventWeight content.atoms event

/-- Integrate the observable against the exact retained signed occurrence weights. -/
@[expose] def integral {α : Type} (content : SignedContent α)
    (value : α → Fraction.Rational) : Fraction.Rational :=
  signedIntegralWeight content.atoms value

/-- Pointwise equal observables have equal signed integrals over the same retained content. -/
theorem integral_congr {α : Type} (content : SignedContent α)
    (left right : α → Fraction.Rational)
    (pointwise : ∀ item, left item = right item) :
    content.integral left = content.integral right :=
  signedIntegralWeight_congr content.atoms left right pointwise

/-- Integrate observable magnitude against the exact occurrence-wise weight-magnitude content. -/
@[expose] def variationIntegral {α : Type} (content : SignedContent α)
    (value : α → Fraction.Rational) : Fraction.Rational :=
  content.variationContent.integral fun item =>
    Distance.rationalSeparation (value item) 0

/-- The magnitude of a signed integral is bounded by the integral of magnitude against original occurrence-wise weight
variation. -/
theorem integral_bounded_by_variationIntegral {α : Type}
    (content : SignedContent α) (value : α → Fraction.Rational) :
    Distance.rationalSeparation (content.integral value) 0 ≤
      content.variationIntegral value := by
  unfold integral variationIntegral variationContent Content.integral
  induction content.atoms with
  | nil =>
      simp only [-eq_self, -iff_self, signedIntegralWeight, List.map_nil,
        Distribution.expectationWeight, Distance.rationalSeparation]

      exact le_rfl
  | cons atom remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, signedIntegralWeight, List.map_cons,
        Distribution.expectationWeight]

      calc
        Distance.rationalSeparation
              (atom.weight * value atom.item +
                signedIntegralWeight remaining value) 0 ≤
            Distance.rationalSeparation (atom.weight * value atom.item) 0 +
              Distance.rationalSeparation
                (signedIntegralWeight remaining value) 0 :=
          Distance.rationalSeparation_add_zero_le _ _
        _ ≤ Distance.rationalSeparation (atom.weight * value atom.item) 0 +
            Distribution.expectationWeight
              (remaining.map variationAtom)
              (fun item => Distance.rationalSeparation (value item) 0) :=
          add_le_add le_rfl inductionHypothesis
        _ = Distance.rationalSeparation atom.weight 0 *
              Distance.rationalSeparation (value atom.item) 0 +
            Distribution.expectationWeight
              (remaining.map variationAtom)
              (fun item => Distance.rationalSeparation (value item) 0) := by
          rw [Distance.rationalSeparation_mul_zero]

end

/-- The empty event has signed mass zero. -/
@[simp] theorem measure_empty {α : Type} (content : SignedContent α) :
    content.measure (fun _ => false) = 0 := by
  unfold measure
  induction content.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      change (if false = true then atom.weight else 0) +
        signedEventWeight remaining (fun _ => false) = 0
      rw [if_neg (fun equal => Bool.noConfusion equal), zero_add, inductionHypothesis]

/-- The universal event has signed mass equal to the retained signed total. -/
@[simp] theorem measure_univ {α : Type} (content : SignedContent α) :
    content.measure (fun _ => true) = content.total := by
  unfold measure total
  induction content.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      change (if true = true then atom.weight else 0) +
        signedEventWeight remaining (fun _ => true) = atom.weight + signedTotalWeight remaining
      rw [if_pos rfl, inductionHypothesis]

open Purelib in
/-- Every signed event reading is its exact positive-part content reading minus its negative-part reading. -/
theorem measure_eq_positive_sub_negative {α : Type}
    (content : SignedContent α) (event : α → Bool) :
    content.measure event =
      content.positiveContent.measure event -
        content.negativeContent.measure event := by
  unfold measure positiveContent negativeContent Content.measure
  induction content.atoms with
  | nil =>
      simp only [-eq_self, -iff_self, signedEventWeight, List.map_nil, eventWeight]

      ring1
  | cons atom remaining inductionHypothesis =>
      cases selected : event atom.item
      · simp only [-eq_self, -iff_self, signedEventWeight, selected, zero_add, List.map_cons, eventWeight,
          positivePartAtom_item, negativePartAtom_item,
          inductionHypothesis]
        rw [if_neg (fun equal => Bool.noConfusion equal), zero_add]
      · simp only [-eq_self, -iff_self, signedEventWeight, selected, List.map_cons,
          eventWeight, positivePartAtom_item, positivePartAtom_weight,
          negativePartAtom_item, negativePartAtom_weight,
          inductionHypothesis]
        rw [if_pos rfl]
        have head : atom.weight =
            Data.Rat.positiveWeight atom.weight - Data.Rat.negativeWeight atom.weight :=
          (Data.Rat.positiveWeight_sub_negativeWeight atom.weight).symm
        calc
          atom.weight +
                (eventWeight
                    (remaining.map positivePartAtom) event -
                  eventWeight
                    (remaining.map negativePartAtom) event) =
              (Data.Rat.positiveWeight atom.weight - Data.Rat.negativeWeight atom.weight) +
                (eventWeight
                    (remaining.map positivePartAtom) event -
                  eventWeight
                    (remaining.map negativePartAtom) event) :=
            congrArg (fun weight => weight +
              (eventWeight
                  (remaining.map positivePartAtom) event -
                eventWeight
                  (remaining.map negativePartAtom) event)) head
          _ = Data.Rat.positiveWeight atom.weight +
                eventWeight
                  (remaining.map positivePartAtom) event -
              (Data.Rat.negativeWeight atom.weight +
                eventWeight
                  (remaining.map negativePartAtom) event) := by
            ring1

open Purelib in
open Purelib.Data.Rat in
/-- Every signed integral is its exact positive-part integral minus its negative-part integral. -/
theorem integral_eq_positive_sub_negative {α : Type}
    (content : SignedContent α) (value : α → Fraction.Rational) :
    content.integral value =
      content.positiveContent.integral value -
        content.negativeContent.integral value := by
  unfold integral positiveContent negativeContent Content.integral
  induction content.atoms with
  | nil =>
      simp only [-eq_self, -iff_self, signedIntegralWeight, List.map_nil,
        Distribution.expectationWeight]

      ring1
  | cons atom remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, signedIntegralWeight, List.map_cons,
        Distribution.expectationWeight, positivePartAtom_item,
        positivePartAtom_weight, negativePartAtom_item,
        negativePartAtom_weight, inductionHypothesis]

      have headScaled : atom.weight * value atom.item =
          Data.Rat.positiveWeight atom.weight * value atom.item -
            Data.Rat.negativeWeight atom.weight * value atom.item := by
        calc
          atom.weight * value atom.item =
              (Data.Rat.positiveWeight atom.weight - Data.Rat.negativeWeight atom.weight) *
                value atom.item :=
            congrArg (fun weight => weight * value atom.item)
              (Data.Rat.positiveWeight_sub_negativeWeight atom.weight).symm
          _ = Data.Rat.positiveWeight atom.weight * value atom.item -
              Data.Rat.negativeWeight atom.weight * value atom.item := by ring1
      rw [headScaled]
      ring1

section
open Purelib.Data.Rat
/-- Signed integration preserves pointwise addition. -/
theorem integral_add {α : Type} (content : SignedContent α)
    (left right : α → Fraction.Rational) :
    content.integral (fun item => left item + right item) =
      content.integral left + content.integral right := by
  rw [content.integral_eq_positive_sub_negative,
    content.integral_eq_positive_sub_negative left,
    content.integral_eq_positive_sub_negative right,
    content.positiveContent.integral_add,
    content.negativeContent.integral_add]
  ring1

/-- Signed integration preserves rational scalar multiplication. -/
theorem integral_scale {α : Type} (content : SignedContent α)
    (factor : Fraction.Rational) (value : α → Fraction.Rational) :
    content.integral (fun item => factor * value item) =
      factor * content.integral value := by
  rw [content.integral_eq_positive_sub_negative,
    content.integral_eq_positive_sub_negative value,
    content.positiveContent.integral_scale,
    content.negativeContent.integral_scale]
  ring1

/-- Signed integration preserves pointwise subtraction. -/
theorem integral_sub {α : Type} (content : SignedContent α)
    (left right : α → Fraction.Rational) :
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

end

/-- The signed integral of an event indicator equals its exact signed event mass. -/
theorem integral_indicator {α : Type} (content : SignedContent α)
    (event : α → Bool) :
    content.integral (Distribution.indicator event) =
      content.measure event := by
  unfold integral measure
  induction content.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      cases selected : event atom.item with
      | false =>
          simp only [-eq_self, -iff_self, signedIntegralWeight, signedEventWeight,
            Distribution.indicator, selected, mul_zero,
            zero_add, inductionHypothesis]
          rw [if_neg (fun equal => Bool.noConfusion equal), zero_add]
      | true =>
          simp only [-eq_self, -iff_self, signedIntegralWeight, signedEventWeight,
            Distribution.indicator, selected, mul_one, inductionHypothesis]
          rw [if_pos rfl]

/-- Signed event readings satisfy the finite union-intersection valuation identity. -/
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

open Purelib in
/-- Occurrence-wise weight variation measures an event as the sum of its positive-part and negative-part measurements.
-/
theorem variation_measure_eq_add {α : Type}
    (content : SignedContent α) (event : α → Bool) :
    content.variationContent.measure event =
      content.positiveContent.measure event +
        content.negativeContent.measure event := by
  unfold variationContent positiveContent negativeContent
    Content.measure
  induction content.atoms with
  | nil =>
      simp only [-eq_self, -iff_self, List.map_nil, eventWeight, add_zero]
      rfl

  | cons atom remaining inductionHypothesis =>
      cases selected : event atom.item
      · simp only [-eq_self, -iff_self, List.map_cons, eventWeight, variationAtom_item,
          positivePartAtom_item, negativePartAtom_item, selected, zero_add,
          inductionHypothesis]
        rfl
      · simp only [-eq_self, -iff_self, List.map_cons, eventWeight, variationAtom_item,
          variationAtom_weight, positivePartAtom_item,
          positivePartAtom_weight, negativePartAtom_item,
          negativePartAtom_weight, selected]
        rw [inductionHypothesis,
          Data.Rat.rationalSeparation_zero_eq_parts atom.weight]
        ring1

/-- Occurrence-wise weight variation bounds both signs of the original signed event measurement. -/
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
        by
          have bound := Data.Rat.Fraction.Order.Arithmetic.sub_le_sub_left_direct negativeNonnegative
            (content.positiveContent.measure event)
          convert bound using 1; ring1
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
            by
              have bound := Data.Rat.Fraction.Order.Arithmetic.sub_le_sub_left_direct positiveNonnegative
                (content.negativeContent.measure event)
              convert bound using 1; ring1
          _ ≤ content.positiveContent.measure event +
                content.negativeContent.measure event := by
            simpa only [-eq_self, -iff_self, add_comm] using
              le_add_of_nonneg_right positiveNonnegative

end SignedContent

end Purelib.Measure

end
