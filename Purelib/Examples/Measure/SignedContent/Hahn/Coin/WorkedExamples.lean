module
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Equivalence
import Purelib.Measure.Content.Histogram
import Purelib.Measure.Content.Singularity
import Purelib.Measure.Distribution.Content
import Purelib.Measure.SignedContent.Basic
public import Purelib.Measure.SignedContent.Hahn.Basic
import Purelib.Measure.SignedContent.Hahn.Singularity
import Purelib.Measure.SignedContent.Jordan
import Purelib.Measure.Weighted.Consolidation
import Purelib.Data.Rat.Distance.Basic
import Purelib.Examples.Measure.Distribution.Coin.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Basic
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
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Weighted.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.SignedContent.Hahn.Coin.WorkedExamples

open Purelib.Data.Rat
open Purelib.Measure
open Purelib.Examples.Measure.SignedContent
open Purelib.Examples
open Purelib.Examples.Measure.Distribution.Coin.Basic (fairCoin)

/-- The signed coin content with tails weight one and heads weight minus one. -/
def signedCoinDifference : SignedContent Bool
  where
  atoms := [⟨false, 1⟩, ⟨true, -1⟩]

/-- Consolidating the fair-coin content preserves evaluation on all events. -/
example : Purelib.Measure.Content.EvaluationEquivalent
    fairCoin.toContent.consolidate
      fairCoin.toContent :=
  fairCoin.toContent.consolidate_evaluationEquivalent

/-- Evaluation equivalence of the consolidated and original coin contents is equivalent to equality on every singleton
atom event. -/
example : Purelib.Measure.Content.EvaluationEquivalent
      fairCoin.toContent.consolidate
        fairCoin.toContent ↔
    ∀ outcome : Bool,
      fairCoin.toContent.consolidate.measure (Purelib.Measure.atomEvent
        outcome) =
        fairCoin.toContent.measure (Purelib.Measure.atomEvent outcome)
          :=
  Content.evaluationEquivalent_iff_atom_measure_eq _ _

/-- The Hahn certificate selecting tails as the nonnegative part of the signed coin.

The original two signed atoms prove nonnegativity on the selected event and nonpositivity on its complement. -/
def signedCoinHahnCertificate :
    SignedContent.HahnCertificate signedCoinDifference where
  positiveEvent := fun outcome => !outcome
  selected_nonnegative := by
    intro atom member selected
    simp only [-eq_self, -iff_self, signedCoinDifference] at member
    have member := (Purelib.Data.List.Membership.mem_cons.mp member).elim
      (fun equal => Or.inl equal)
      (fun tail => Or.inr (Purelib.Data.List.Membership.mem_singleton.mp tail))
    rcases member with rfl | rfl
    · decide
    · have impossible : false = true := by
        simpa only [-eq_self, -iff_self, Bool.not_true] using selected
      exact Bool.noConfusion impossible
  unselected_nonpositive := by
    intro atom member selected
    simp only [-eq_self, -iff_self, signedCoinDifference] at member
    have member := (Purelib.Data.List.Membership.mem_cons.mp member).elim
      (fun equal => Or.inl equal)
      (fun tail => Or.inr (Purelib.Data.List.Membership.mem_singleton.mp tail))
    rcases member with rfl | rfl
    · have impossible : true = false := by
        simpa only [-eq_self, -iff_self, Bool.not_false] using selected
      exact Bool.noConfusion impossible
    · decide

/-- The signed coin has total zero. -/
example : signedCoinDifference.total = 0 := by
  decide

/-- The signed tails event has measure one. -/
example : signedCoinDifference.measure (fun outcome => !outcome) = 1 :=
  by
  decide

/-- The signed heads event has measure minus one. -/
example : signedCoinDifference.measure (fun outcome => outcome) = -1 :=
  by
  decide

/-- Every signed event measure is at most the retained positive Hahn-event measure. -/
example (event : Bool → Bool) :
    signedCoinDifference.measure event ≤
      signedCoinDifference.measure
        signedCoinHahnCertificate.positiveEvent :=
  signedCoinHahnCertificate.measure_le_positiveEvent event

/-- The total variation equals positive-event measure minus its complement measure. -/
example : signedCoinDifference.variationContent.total =
    signedCoinDifference.measure
      signedCoinHahnCertificate.positiveEvent -
      signedCoinDifference.measure
        (fun outcome => !(signedCoinHahnCertificate.positiveEvent
          outcome)) :=
  signedCoinHahnCertificate.variationTotal_eq_measure_sub_complement

/-- The Hahn sign observable has signed integral two. -/
example : signedCoinDifference.integral
      signedCoinHahnCertificate.signObservable = 2 := by
  decide

/-- The Hahn sign observable integrates to the original total variation. -/
example : signedCoinDifference.integral
      signedCoinHahnCertificate.signObservable =
    signedCoinDifference.variationContent.total :=
  signedCoinHahnCertificate.integral_signObservable_eq_variationTotal

/-- The positive and negative parts each have total one and total variation is two. -/
example : signedCoinDifference.positiveContent.total = 1 ∧
    signedCoinDifference.negativeContent.total = 1 ∧
    signedCoinDifference.variationContent.total = 2 := by
  decide

/-- The canonical positive and negative contents are mutually singular. -/
example : Purelib.Measure.Content.MutuallySingular
    signedCoinDifference.positiveContent
      signedCoinDifference.negativeContent :=

    Hahn.Coin.WorkedExamples.signedCoinHahnCertificate.positiveContent_mutuallySingular_negativeContent

/-- Every Jordan decomposition has the same positive event measures as the retained canonical positive part. -/
example (other : Purelib.Measure.SignedContent.JordanDecomposition
  signedCoinDifference)
    (event : Bool → Bool) :
    other.positive.measure event =
      signedCoinDifference.positiveContent.measure event :=
  other.positive_measure_eq_canonical signedCoinHahnCertificate event

/-- Every Jordan decomposition has the same negative event measures as the retained canonical negative part. -/
example (other : Purelib.Measure.SignedContent.JordanDecomposition
  signedCoinDifference)
    (event : Bool → Bool) :
    other.negative.measure event =
      signedCoinDifference.negativeContent.measure event :=
  other.negative_measure_eq_canonical signedCoinHahnCertificate event

/-- The signed heads measure is its positive measure minus its negative measure. -/
example : signedCoinDifference.measure (fun outcome => outcome) =
    signedCoinDifference.positiveContent.measure (fun outcome => outcome)
      -
      signedCoinDifference.negativeContent.measure (fun outcome =>
        outcome) :=
  signedCoinDifference.measure_eq_positive_sub_negative
    (fun outcome => outcome)

/-- The heads variation measure bounds both signs of the signed heads measure. -/
example :
    signedCoinDifference.measure (fun outcome => outcome) ≤
        signedCoinDifference.variationContent.measure
          (fun outcome => outcome) ∧
      -signedCoinDifference.measure (fun outcome => outcome) ≤
        signedCoinDifference.variationContent.measure
          (fun outcome => outcome) :=
  signedCoinDifference.measure_bounded_by_variation
    (fun outcome => outcome)

/-- The observable taking value three on tails and two on heads. -/
def signedCoinObservable (outcome : Bool) :
  Fraction.Rational :=
  if outcome then 2 else 3

/-- The displayed observable has signed integral one. -/
example : signedCoinDifference.integral
  signedCoinObservable = 1 := by
  decide

/-- The displayed observable has variation integral five. -/
example : signedCoinDifference.variationIntegral
  signedCoinObservable = 5 := by
  decide

/-- The absolute signed integral is bounded by the retained variation integral. -/
example : Purelib.Data.Rat.Distance.rationalSeparation
      (signedCoinDifference.integral
        signedCoinObservable) 0 ≤
    signedCoinDifference.variationIntegral
      signedCoinObservable :=
  signedCoinDifference.integral_bounded_by_variationIntegral
    signedCoinObservable

/-- The fair-coin heads content is one half. -/
example : fairCoin.toContent.measure (fun outcome => outcome) =
    1 / 2 := by
  decide

/-- Restricting fair-coin content to heads gives total one half. -/
example :
    (fairCoin.toContent.restrict (fun outcome => outcome)).total =
      1 / 2 := by
  decide

/-- The fair-coin integral of values one on tails and three on heads is two. -/
example : fairCoin.toContent.integral
    (fun outcome => if outcome then 3 else 1) = 2 := by
  decide

/-- The product coin content assigns the both-heads event measure one quarter. -/
example :
    (fairCoin.toContent.product
      fairCoin.toContent).measure
        (fun pair => pair.1 && pair.2) = 1 / 4 := by
  decide

/-- The zero-one heads indicator has fair-coin expectation one half. -/
example : fairCoin.expectation (fun outcome => if outcome then 1 else
  0) =
    1 / 2 := by
  decide

end Purelib.Examples.Measure.SignedContent.Hahn.Coin.WorkedExamples

end
