module
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Tactic.Ring

import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Weighted.Operations
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

section
section
public section

/-!
# Finite restriction and pushforward

Restriction and pushforward are direct transformations of displayed weighted
lists.  Their measure identities are finite recursive calculations over
executable Boolean events.
-/

namespace Purelib.Measure

/-- Retain exactly the original weighted occurrences selected by the Boolean event, in their original order.

A true test retains the original head record and its weight witness. A false
test skips that same head while recursively retaining the selected tail. -/
@[expose] def restrictAtoms {α : Type} :
    List (Weighted α) → (α → Bool) → List (Weighted α)
  | [], _ => []
  | atom :: remaining, event =>
      if event atom.item then atom :: restrictAtoms remaining event
      else restrictAtoms remaining event

section
open Purelib.Data.Rat
/-- The restricted total weight equals the event weight on the original occurrence list.

A true Boolean test retains the original head and weight; a false test skips
that same occurrence. Scalar transport of the original tail establishes the
weight of the unchanged restricted output. -/
theorem totalWeight_restrictAtoms {α : Type} :
    ∀ (atoms : List (Weighted α)) (event : α → Bool),
      totalWeight (restrictAtoms atoms event) = eventWeight atoms event
  | [], event => rfl
  | atom :: remaining, event => by
      change totalWeight (if event atom.item then atom :: restrictAtoms remaining event
          else restrictAtoms remaining event) =
        (match event atom.item with | true => atom.weight | false => 0) +
          eventWeight remaining event
      cases event atom.item with
      | false =>
          exact (totalWeight_restrictAtoms remaining event).trans
            (Fraction.Field.zero_add _).symm
      | true =>
          exact congrArg (fun tail => atom.weight + tail)
            (totalWeight_restrictAtoms remaining event)

/-- Event weight after restriction equals original weight of the event intersected with the condition.

The condition retains the original occurrence exactly when true. The two
Boolean tests at the current payload determine its scalar contribution;
structural tail transport retains the original intersection scan. -/
theorem eventWeight_restrictAtoms {α : Type} :
    ∀ (atoms : List (Weighted α)) (condition event : α → Bool),
      eventWeight (restrictAtoms atoms condition) event =
        eventWeight atoms (intersectionEvent event condition)
  | [], condition, event => rfl
  | atom :: remaining, condition, event => by
      change eventWeight (if condition atom.item then atom :: restrictAtoms remaining condition
          else restrictAtoms remaining condition) event =
        (match event atom.item && condition atom.item with | true => atom.weight | false => 0) +
          eventWeight remaining (intersectionEvent event condition)
      cases condition atom.item with
      | false =>
          cases event atom.item <;>
            exact (eventWeight_restrictAtoms remaining condition event).trans
              (Fraction.Field.zero_add _).symm
      | true =>
          change (match event atom.item with | true => atom.weight | false => 0) +
              eventWeight (restrictAtoms remaining condition) event =
            (match event atom.item && true with | true => atom.weight | false => 0) +
              eventWeight remaining (intersectionEvent event condition)
          cases event atom.item with
          | false =>
              exact congrArg (fun tail => (0 : Fraction.Rational) + tail)
                (eventWeight_restrictAtoms remaining condition event)
          | true =>
              exact congrArg (fun tail => atom.weight + tail)
                (eventWeight_restrictAtoms remaining condition event)

end

/-- Map every retained payload through the supplied function while preserving its exact weight and nonnegativity
witness.

The mapped head retains the original weight and its proof. The recursive tail
keeps the original occurrence order and multiplicities under that same map. -/
@[expose] def mapAtoms {α β : Type} (function : α → β) :
    List (Weighted α) → List (Weighted β)
  | [] => []
  | atom :: remaining =>
      { item := function atom.item
        weight := atom.weight
        nonnegative := atom.nonnegative } ::
        mapAtoms function remaining

/-- Mapping payloads preserves the exact retained total weight.

Each mapped head carries its original weight and proof witness. Scalar tail
transport identifies the two sums over those same ordered occurrences. -/
theorem totalWeight_mapAtoms {α β : Type} (function : α → β) :
    ∀ atoms : List (Weighted α),
      totalWeight (mapAtoms function atoms) = totalWeight atoms
  | [] => rfl
  | atom :: remaining => congrArg (fun tail => atom.weight + tail)
      (totalWeight_mapAtoms function remaining)

/-- Event weight on mapped payloads equals weight of the pulled-back event on the original occurrences.

Both scans test the same mapped original payload and retain the original
weight. Scalar tail transport compares those exact event contributions. -/
theorem eventWeight_mapAtoms {α β : Type} (function : α → β) :
    ∀ (atoms : List (Weighted α)) (event : β → Bool),
      eventWeight (mapAtoms function atoms) event =
        eventWeight atoms (fun item => event (function item))
  | [], event => rfl
  | atom :: remaining, event => by
      let contribution := match event (function atom.item) with
        | true => atom.weight | false => 0
      change contribution + eventWeight (mapAtoms function remaining) event =
        contribution + eventWeight remaining (fun item => event (function item))
      exact congrArg (fun tail => contribution + tail)
        (eventWeight_mapAtoms function remaining event)

/-- Enumerate exact pairs of retained occurrences in left-major order with product weights.

Each original left occurrence scales the full mapped right list. Concatenating these blocks preserves both payload
occurrences and their weights without consolidating equal pairs. -/
@[expose] def productAtoms {α β : Type} :
    List (Weighted α) → List (Weighted β) → List (Weighted (α × β))
  | [], _ => []
  | atom :: remaining, right =>
      scaleAtoms atom.weight atom.nonnegative
          (mapAtoms (fun rightItem => (atom.item, rightItem)) right) ++
        productAtoms remaining right

section
open Purelib.Data.Rat
/-- The total weight of the exact occurrence product is the product of its original totals.

Each original left occurrence scales the exact mapped right row. The append,
scaling and map certificates retain those rows, and scalar distributivity
combines their totals in the original left-major order. -/
theorem totalWeight_productAtoms {α β : Type} :
    ∀ (left : List (Weighted α)) (right : List (Weighted β)),
      totalWeight (productAtoms left right) =
        totalWeight left * totalWeight right
  | [], right => (Fraction.Field.zero_mul_direct _).symm
  | atom :: remaining, right => by
      rw [productAtoms, totalWeight_append, totalWeight_scaleAtoms,
        totalWeight_mapAtoms, totalWeight_productAtoms remaining right]
      dsimp only [totalWeight]
      ring1

/-- A rectangular event on the exact product list has weight equal to the product of its marginal event weights.

Each original left selection fixes the Boolean event on its exact mapped
right row. The existing pointwise event certificate and scalar distributivity
combine those retained rows with the recursive product tail. -/
theorem eventWeight_productAtoms_rectangle {α β : Type} :
    ∀ (left : List (Weighted α)) (right : List (Weighted β))
      (leftEvent : α → Bool) (rightEvent : β → Bool),
      eventWeight (productAtoms left right)
          (fun pair => leftEvent pair.1 && rightEvent pair.2) =
        eventWeight left leftEvent * eventWeight right rightEvent
  | [], right, leftEvent, rightEvent => (Fraction.Field.zero_mul_direct _).symm
  | atom :: remaining, right, leftEvent, rightEvent => by
      rw [productAtoms, eventWeight_append, eventWeight_scaleAtoms,
        eventWeight_mapAtoms,
        eventWeight_productAtoms_rectangle remaining right]
      cases selected : leftEvent atom.item
      · have combinedWeightZero :
            eventWeight right
                (fun rightItem =>
                  leftEvent atom.item && rightEvent rightItem) = 0 :=
          calc
            eventWeight right
                  (fun rightItem =>
                    leftEvent atom.item && rightEvent rightItem) =
                eventWeight right (fun _ => false) :=
              eventWeight_congr right _ _ (fun rightItem => by
                rw [selected]
                rfl)
            _ = 0 := Content.measure_empty ⟨right⟩
        rw [combinedWeightZero]
        have headZero : (match leftEvent atom.item with
            | true => atom.weight | false => 0) = 0 := by rw [selected]
        change atom.weight * 0 + eventWeight remaining leftEvent * eventWeight right rightEvent =
          ((match leftEvent atom.item with | true => atom.weight | false => 0) +
            eventWeight remaining leftEvent) * eventWeight right rightEvent
        rw [headZero]
        ring1
      · have combinedWeightEqual :
            eventWeight right
                (fun rightItem =>
                  leftEvent atom.item && rightEvent rightItem) =
              eventWeight right rightEvent :=
          eventWeight_congr right _ _ (fun rightItem => by
            rw [selected]
            rfl)
        rw [combinedWeightEqual]
        have headSelected : (match leftEvent atom.item with
            | true => atom.weight | false => 0) = atom.weight := by rw [selected]
        change atom.weight * eventWeight right rightEvent +
            eventWeight remaining leftEvent * eventWeight right rightEvent =
          ((match leftEvent atom.item with | true => atom.weight | false => 0) +
            eventWeight remaining leftEvent) * eventWeight right rightEvent
        rw [headSelected]
        ring1

end

namespace Content
end Content

end Purelib.Measure

end

end

section
/-!
# Essential maxima under finite measure operations

Restriction and nonnegative reweighting can only remove nonzero rows from
the support relevant to the executable essential maximum.  Consequently
restriction, change of density, and positive-event conditioning are exact
finite `L∞` contractions.
-/

public section

namespace Purelib.Measure

/-- Every occurrence retained by restriction belongs to the exact original list.

The Boolean condition selects the original head occurrence or skips it.
Structural membership retains the actual selected head or recursively retained
tail occurrence, with its original weight and nonnegativity witness. -/
theorem mem_restrictAtoms {α : Type} :
    ∀ (atoms : List (Weighted α)) (event : α → Bool)
      (candidate : Weighted α),
      candidate ∈ restrictAtoms atoms event → candidate ∈ atoms
  | [], _, _, member => by nomatch member
  | atom :: remaining, event, candidate, member => by
      cases selected : event atom.item with
      | false =>
          rw [restrictAtoms, selected] at member
          exact List.Mem.tail atom (mem_restrictAtoms remaining event candidate member)
      | true =>
          rw [restrictAtoms, selected] at member
          cases member with
          | head => exact List.Mem.head remaining
          | tail _ tailMember =>
              exact List.Mem.tail atom (mem_restrictAtoms remaining event candidate tailMember)

end Purelib.Measure

end
