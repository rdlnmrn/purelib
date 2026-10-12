module

import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Content.Basic
public import Purelib.Measure.SignedContent.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.PositiveNegativePart
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
namespace SignedContent

open Purelib.Data.Rat

set_option genInjectivity false in
/-- Retain a Boolean event separating nonnegative from nonpositive weights in the exact signed occurrence list.

Selection implies a nonnegative original weight and rejection implies a nonpositive one. The certificate is supplied
explicitly, so repeated payloads with incompatible signs are not silently identified. -/
structure HahnCertificate {α : Type} (content : SignedContent α) where
  /-- The exact retained Boolean event separating original occurrence signs. -/ positiveEvent : α → Bool
  /-- Each selected original occurrence has nonnegative signed weight. -/ selected_nonnegative : ∀ atom, atom ∈
    content.atoms →
    positiveEvent atom.item = true → 0 ≤ atom.weight
  /-- Each rejected original occurrence has nonpositive signed weight. -/ unselected_nonpositive : ∀ atom, atom ∈
    content.atoms →
    positiveEvent atom.item = false → atom.weight ≤ 0

constructive_injectivity HahnCertificate

namespace HahnCertificate

section
open Purelib.Data.Rat
/-- Read plus one on the exact retained positive event and minus one on its complement. -/
@[expose] def signObservable {α : Type} {content : SignedContent α}
    (certificate : HahnCertificate content) : α → Fraction.Rational :=
  fun item => if certificate.positiveEvent item then 1 else -1

/-- The retained Hahn sign observable has magnitude one at every payload. -/
theorem signObservable_magnitude_one {α : Type}
    {content : SignedContent α} (certificate : HahnCertificate content)
    (item : α) :
    Distance.rationalSeparation (certificate.signObservable item) 0 = 1 := by
  cases selected : certificate.positiveEvent item <;>
    simp only [-eq_self, -iff_self, signObservable, selected, if_pos rfl, Distance.rationalSeparation] <;>
    decide

end

open Purelib in
open Purelib.Measure in
/-- An occurrence-wise sign separator selects exactly the total positive-part weight. -/
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
      · simp only [-eq_self, -iff_self, signedEventWeight, selected, if_neg (by decide : ¬ false = true), zero_add,
          List.map_cons, totalWeight,
          SignedContent.positivePartAtom_weight]
        rw [Data.Rat.positiveWeight_eq_zero_of_nonpos
          (unselectedNonpositive atom List.mem_cons_self selected), zero_add]
        exact signedEventWeight_positive_eq event remaining tailSelected
          tailUnselected
      · simp only [-eq_self, -iff_self, signedEventWeight, selected, if_pos rfl,
          List.map_cons, totalWeight, SignedContent.positivePartAtom_weight]
        rw [Data.Rat.positiveWeight_eq_self_of_nonneg
          (selectedNonnegative atom List.mem_cons_self selected)]
        rw [signedEventWeight_positive_eq event remaining tailSelected
          tailUnselected]

open Purelib in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- The complement of an occurrence-wise sign separator has signed weight equal to minus the total negative-part weight.
-/
private theorem signedEventWeight_negative_eq {α : Type}
    (event : α → Bool) : ∀ atoms : List (SignedWeighted α),
    (∀ atom, atom ∈ atoms → event atom.item = true →
      0 ≤ atom.weight) →
    (∀ atom, atom ∈ atoms → event atom.item = false →
      atom.weight ≤ 0) →
    signedEventWeight atoms (fun item => !(event item)) =
      -totalWeight (atoms.map negativePartAtom)
  | [], selectedNonnegative, unselectedNonpositive => by
      change (0 : Fraction.Rational) = -0
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
      · simp only [-eq_self, -iff_self, signedEventWeight, selected, Bool.not_false, if_pos rfl, List.map_cons,
          totalWeight,
          SignedContent.negativePartAtom_weight]
        rw [Data.Rat.negativeWeight_eq_neg_of_nonpos
          (unselectedNonpositive atom List.mem_cons_self selected)]
        rw [signedEventWeight_negative_eq event remaining tailSelected
          tailUnselected]
        ring1
      · simp only [-eq_self, -iff_self, signedEventWeight, selected, Bool.not_true,
          if_neg (by decide : ¬ false = true), zero_add, List.map_cons, totalWeight,
          SignedContent.negativePartAtom_weight]
        rw [Data.Rat.negativeWeight_eq_zero_of_nonneg
          (selectedNonnegative atom List.mem_cons_self selected), zero_add]
        exact signedEventWeight_negative_eq event remaining tailSelected
          tailUnselected

/-- The certified positive event's signed mass equals the exact positive-part total. -/
theorem measure_positiveEvent_eq_positiveTotal {α : Type}
    {content : SignedContent α} (certificate : HahnCertificate content) :
    content.measure certificate.positiveEvent =
      content.positiveContent.total := by
  unfold SignedContent.measure positiveContent Content.total
  exact signedEventWeight_positive_eq certificate.positiveEvent content.atoms
    certificate.selected_nonnegative certificate.unselected_nonpositive

/-- The certified positive event's complement has signed mass equal to minus the exact negative-part total. -/
theorem measure_complement_eq_neg_negativeTotal {α : Type}
    {content : SignedContent α} (certificate : HahnCertificate content) :
    content.measure (fun item => !(certificate.positiveEvent item)) =
      -content.negativeContent.total := by
  unfold SignedContent.measure negativeContent Content.total
  exact signedEventWeight_negative_eq certificate.positiveEvent content.atoms
    certificate.selected_nonnegative certificate.unselected_nonpositive

/-- Every signed event mass is bounded above by the retained certified positive-event mass. -/
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
      Fraction.Order.Arithmetic.sub_le_iff_le_add_direct.mpr (by
        have translated := Fraction.Order.Arithmetic.add_le_add_right_direct
          (content.negativeContent.measure_nonneg event)
          (content.positiveContent.measure event)
        calc
          content.positiveContent.measure event =
              0 + content.positiveContent.measure event := (Fraction.zero_add _).symm
          _ ≤ content.negativeContent.measure event +
              content.positiveContent.measure event := translated
          _ = content.positiveContent.measure event +
              content.negativeContent.measure event := Fraction.add_comm _ _)
    _ ≤ content.positiveContent.total :=
      content.positiveContent.measure_le_total event

open Purelib.Data.Rat in
/-- The retained certified negative-event mass bounds every signed event mass from below. -/
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
        -content.negativeContent.measure event := Fraction.Order.Arithmetic.neg_le_neg_direct negativeBound
    _ ≤ content.positiveContent.measure event -
          content.negativeContent.measure event := by
      exact le_add_of_nonneg_left positiveNonnegative

/-- Total occurrence-wise variation is positive-event signed mass minus its complement's signed mass. -/
theorem variationTotal_eq_measure_sub_complement {α : Type}
    {content : SignedContent α} (certificate : HahnCertificate content) :
    content.variationContent.total =
      content.measure certificate.positiveEvent -
        content.measure (fun item => !(certificate.positiveEvent item)) := by
  have variationTotal : content.variationContent.total =
      content.positiveContent.total + content.negativeContent.total := by
    simpa only [-eq_self, -iff_self, Content.measure_univ] using
      content.variation_measure_eq_add (fun _ => true)
  rw [variationTotal, certificate.measure_positiveEvent_eq_positiveTotal,
    certificate.measure_complement_eq_neg_negativeTotal]
  ring1

/-- Integrating the retained Hahn sign observable attains the exact total occurrence-wise variation. -/
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
          simp only [-eq_self, -iff_self, signObservable, Distribution.indicator, selected, Bool.not_false,
            Bool.not_true, if_pos rfl, if_neg (by decide : ¬ false = true)] <;> ring1)
    _ = content.measure certificate.positiveEvent -
          content.measure
            (fun item => !(certificate.positiveEvent item)) := by
      rw [content.integral_sub, content.integral_indicator,
        content.integral_indicator]
    _ = content.variationContent.total :=
      certificate.variationTotal_eq_measure_sub_complement.symm

end HahnCertificate

end SignedContent

end Purelib.Measure

end
