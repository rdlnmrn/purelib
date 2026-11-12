module

import Purelib.Approximation.Gaussian.Translation.CCL.Cursor.RoundTrip
import Purelib.Tactic.OperationalEquivalence
import Purelib.Approximation.Gaussian.Sequence.Preparation
import Purelib.Approximation.Gaussian.Division.Prepared.Quotient
import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic
import Purelib.Approximation.Gaussian.Sequence.Constant
meta import Purelib.Approximation.Gaussian.Translation.CCL.Cursor.RoundTrip
meta import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Comparison
meta import Purelib.Approximation.Gaussian.Sequence.Constant
meta import Purelib.Approximation.Gaussian.Sequence.Preparation
meta import Purelib.Approximation.Gaussian.Division.Prepared.Quotient

/-!
# Arithmetic through retained approximation/cursor round trips

Quantified comparisons retain independent input approximations and starts.
The executable regression compares actual arithmetic cursors after different
nonempty prefixes, preserving each request list and its original parser owner.
-/

namespace TestPurelib.Approximation.Gaussian.TranslationRoundTrip

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (Comparison Equivalent NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic (BitLaw)
open Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic (ChannelCursor)
open Purelib.Approximation.Gaussian.Sequence (ApproximationData)
open Purelib.Approximation.Gaussian.Sequence.Constant (constantApproximation)
open Purelib.Approximation.Gaussian.Translation.CCL.Cursor
open Purelib.Approximation.Gaussian.Translation.CCL.Cursor.Basic
open Purelib.Data.Rat.Fraction (Rational)

example (first second : ApproximationData)
    (left : RoundTrip.CertifiedApproximationCursorRoundTrip first)
    (right : RoundTrip.CertifiedApproximationCursorRoundTrip second)
    (equivalent : Equivalent first second) (firstStart secondStart : Nat)
    (target : Rational) (positive : 0 < target) :
    Comparison (CursorObservation.approximation first.toNamed)
      (CursorObservation.approximation second.toNamed) firstStart secondStart target :=
  (left.compare right equivalent).compare firstStart secondStart target positive

example (first second : ApproximationData)
    (left : RoundTrip.CertifiedApproximationCursorRoundTrip first)
    (right : RoundTrip.CertifiedApproximationCursorRoundTrip second) :
    NamedEquivalent
      (CoherentNamed.add (CoherentNamed.ofApproximation first) (CoherentNamed.ofApproximation second)).name
      (CoherentNamed.add
        (CoherentNamed.ofApproximation (CursorObservation.approximation first.toNamed))
        (CoherentNamed.ofApproximation (CursorObservation.approximation second.toNamed))).name :=
  left.add_equivalent right

example (first second : ApproximationData)
    (left : RoundTrip.CertifiedApproximationCursorRoundTrip first)
    (right : RoundTrip.CertifiedApproximationCursorRoundTrip second) :
    NamedEquivalent
      (CoherentNamed.mul (CoherentNamed.ofApproximation first) (CoherentNamed.ofApproximation second)).name
      (CoherentNamed.mul
        (CoherentNamed.ofApproximation (CursorObservation.approximation first.toNamed))
        (CoherentNamed.ofApproximation (CursorObservation.approximation second.toNamed))).name :=
  left.mul_equivalent right

/-- Execute both arithmetic routes from different already nonempty persistent prefixes. -/
private meta def checkSchedules : IO Unit := do
  let first := constantApproximation 2
  let second := constantApproximation 3
  let leftRoundTrip := RoundTrip.certifiedApproximationCursorRoundTrip first
  let rightRoundTrip := RoundTrip.certifiedApproximationCursorRoundTrip second
  let leftSource := CoherentNamed.ofApproximation first
  let rightSource := CoherentNamed.ofApproximation second
  let leftTranslated := CoherentNamed.ofApproximation (CursorObservation.approximation first.toNamed)
  let rightTranslated := CoherentNamed.ofApproximation (CursorObservation.approximation second.toNamed)
  let sourceSum := (ChannelCursor.initial (CoherentNamed.add leftSource rightSource)).request 1
    (by decide +kernel) 1
  let translatedSum := (ChannelCursor.initial (CoherentNamed.add leftTranslated rightTranslated)).request 1
    (by decide +kernel) 2
  let sumComparison := ChannelCursor.compareSchedules sourceSum translatedSum
    (BitLaw.ofEquivalent (leftRoundTrip.add_equivalent rightRoundTrip))
    [⟨1, by decide +kernel, 2⟩] [⟨1, by decide +kernel, 3⟩]
  unless sumComparison.sourceLeft.cursor.machine.emitted.length = 1 ∧
      sumComparison.sourceRight.cursor.machine.emitted.length = 2 ∧
      sumComparison.outputLeft.cursor.machine.emitted.length = 3 ∧
      sumComparison.outputRight.cursor.machine.emitted.length = 5 do
    throw (IO.userError "translated sum discarded original prefixes or requests")
  let sourceProduct := (ChannelCursor.initial (CoherentNamed.mul leftSource rightSource)).request 1
    (by decide +kernel) 2
  let translatedProduct := (ChannelCursor.initial (CoherentNamed.mul leftTranslated rightTranslated)).request 1
    (by decide +kernel) 1
  let productComparison := ChannelCursor.compareSchedules sourceProduct translatedProduct
    (BitLaw.ofEquivalent (leftRoundTrip.mul_equivalent rightRoundTrip))
    [⟨1, by decide +kernel, 1⟩] [⟨1, by decide +kernel, 2⟩]
  unless productComparison.sourceLeft.cursor.machine.emitted.length = 2 ∧
      productComparison.sourceRight.cursor.machine.emitted.length = 1 ∧
      productComparison.outputLeft.cursor.machine.emitted.length = 3 ∧
      productComparison.outputRight.cursor.machine.emitted.length = 3 do
    throw (IO.userError "translated product discarded original prefixes or requests")

#eval checkSchedules

example (approximation : ApproximationData)
    (certificate : RoundTrip.CertifiedApproximationCursorRoundTrip approximation) :
    NamedEquivalent
      (CoherentNamed.mul (CoherentNamed.ofApproximation approximation)
        (CoherentNamed.add (CoherentNamed.ofApproximation approximation) (CoherentNamed.Coherence.exact 1))).name
      (CoherentNamed.add
        (CoherentNamed.mul
          (CoherentNamed.ofApproximation (CursorObservation.approximation approximation.toNamed))
          (CoherentNamed.ofApproximation (CursorObservation.approximation approximation.toNamed)))
        (CoherentNamed.ofApproximation (CursorObservation.approximation approximation.toNamed))).name := by
  ccl_equiv [certificate.named]

/-- Execute original shifted-channel preparation and its retained ordinary quotient. -/
private meta def checkPreparation : IO Unit := do
  let approximation := constantApproximation 2
  let prepared := approximation.prepareDifference (-1) 0 9 (by decide +kernel) (by
    intro _later _order
    change (9 : Rational) ≤ Purelib.Data.Gaussian.Norm.Basic.normSq ((2 : Purelib.Data.Gaussian.Basic.Canonical) - (-1))
    decide +kernel)
  let quotient := Division.Prepared.Quotient.quotient (CoherentNamed.Coherence.exact 1) prepared
  let denominatorSample := (prepared.denominator.name.process.witness prepared.denominator.name.state).val
  let quotientSample := (quotient.output.name.process.witness quotient.output.name.state).val
  unless denominatorSample = 3 do
    throw (IO.userError "preparation changed the original two-minus-minus-one denominator")
  unless quotientSample = 1 / 3 do
    throw (IO.userError "cached ordinary quotient did not retain the computed denominator")

#eval checkPreparation

/-- Execute paired original-stage preparation while preserving both ordered input sample histories. -/
private meta def checkPairPreparation : IO Unit := do
  let first := constantApproximation 3
  let second := constantApproximation 2
  let prepared := first.prepareSubtraction second 2 5 1 (by decide +kernel) (by
    intro _firstLater _secondLater _leftOrder _rightOrder
    change (1 : Rational) ≤ Purelib.Data.Gaussian.Norm.Basic.normSq
      ((3 : Purelib.Data.Gaussian.Basic.Canonical) - 2)
    decide +kernel)
  let retained := first.subtractionState second 2 5
  let source : Nat × Nat := retained.source
  unless source = (2, 5) do
    throw (IO.userError "paired preparation discarded the original ordered sample stages")
  let quotient := Division.Prepared.Quotient.quotient (CoherentNamed.Coherence.exact 1) prepared
  let denominatorSample := (prepared.denominator.name.process.witness prepared.denominator.name.state).val
  let quotientSample := (quotient.output.name.process.witness quotient.output.name.state).val
  unless denominatorSample = 1 ∧ quotientSample = 1 do
    throw (IO.userError "paired preparation or its cached quotient changed the original difference")

#eval checkPairPreparation

end TestPurelib.Approximation.Gaussian.TranslationRoundTrip
