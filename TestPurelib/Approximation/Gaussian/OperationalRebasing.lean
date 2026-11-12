module

import Purelib.Polynomial.Multivariate.Gaussian.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent.Based
import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Tactic.OperationalEquivalence
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Name.Sampling
meta import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Comparison
meta import Purelib.Approximation.Gaussian.Name.Coherent.Based
meta import Purelib.Approximation.Gaussian.Name.Sampling
meta import Purelib.Polynomial.Multivariate.Gaussian.Comparison

/-!
# Normalized comparisons across actual dependent states and independent schedules

The two inputs retain separate starting states of their original process.
Their normalized arithmetic and supplied state comparison produce a bit law.
The persistent cursor adapter keeps both original prefixes and exact origins.
-/

namespace TestPurelib.Approximation.Gaussian.OperationalRebasing

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic (BitLaw)
open Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic
open Purelib.Polynomial.Multivariate
open Purelib.Approximation.Gaussian.Sequence (ApproximationData)
open Purelib.Approximation.Gaussian.Name

/-- The same original coherent process started at its supplied dependent state. -/
private def atState (input : CoherentNamed) (state : input.name.process.State) : CoherentNamed :=
  ⟨⟨input.name.process, state⟩, input.coherent⟩

/-- Compare two separate original dependent starting states using the retained process coherence. -/
private def stateComparison (input : CoherentNamed) (first second : input.name.process.State) :
    NamedEquivalent (atState input first).name (atState input second).name :=
  NamedEquivalent.trans (NamedEquivalent.symm (input.rebaseEquivalent first)) (input.rebaseEquivalent second)

/-- Normalize the original shifted-square arithmetic at its actual supplied starting state. -/
private def polynomial (input : CoherentNamed) (state : input.name.process.State) :=
  let bindings : Fin 1 → CoherentNamed := fun _ => atState input state
  let atom := Gaussian.Normalized.atom bindings 0
  let shifted := atom.add (Gaussian.Normalized.constant bindings 1)
  shifted.mul shifted

/-- The cached shifted-square form depends on coefficients and original atom indices alone. -/
private theorem polynomial_form (input : CoherentNamed) (state : input.name.process.State) :
    (polynomial input state).form =
      Sparse.mul (Sparse.add (Sparse.atom (0 : Fin 1)) (Sparse.constant 1))
        (Sparse.add (Sparse.atom (0 : Fin 1)) (Sparse.constant 1)) := by
  unfold polynomial
  rewrite [Gaussian.Normalized.mul_form, Gaussian.Normalized.add_form,
    Gaussian.Normalized.atom_form, Gaussian.Normalized.constant_form]
  rfl

/-- Identical finite coefficients compare the original arithmetic at independent dependent states. -/
private def polynomialLaw (input : CoherentNamed) (first second : input.name.process.State) :
    BitLaw
      (CoherentNamed.mul (CoherentNamed.add (atState input first) (CoherentNamed.Coherence.exact 1))
        (CoherentNamed.add (atState input first) (CoherentNamed.Coherence.exact 1)))
      (CoherentNamed.mul (CoherentNamed.add (atState input second) (CoherentNamed.Coherence.exact 1))
        (CoherentNamed.add (atState input second) (CoherentNamed.Coherence.exact 1))) :=
  BitLaw.ofEquivalent ((polynomial input first).compareAcross (polynomial input second)
    (fun _ => stateComparison input first second)
    (congrArg Sparse.terms ((polynomial_form input first).trans (polynomial_form input second).symm)))

/-- A displayed finite index at the original approximation-backed process's dependent state type. -/
private def startingIndex (approximation : ApproximationData) (index : Nat) :
    (CoherentNamed.ofApproximation approximation).name.process.State := by
  change Nat
  exact index

/-- Compare shifted-square arithmetic at the original approximation's zero and successor states. -/
private def differentStarts (approximation : ApproximationData) :=
  polynomialLaw (CoherentNamed.ofApproximation approximation) (startingIndex approximation 0)
    (startingIndex approximation 1)

example (approximation : ApproximationData) (leftSchedule rightSchedule : List ChannelCursor.RequestStep) :
    ChannelCursor.ScheduleComparison
      (ChannelCursor.initial
        (CoherentNamed.mul
          (CoherentNamed.add (atState (CoherentNamed.ofApproximation approximation) (startingIndex approximation 0))
            (CoherentNamed.Coherence.exact 1))
          (CoherentNamed.add (atState (CoherentNamed.ofApproximation approximation) (startingIndex approximation 0))
            (CoherentNamed.Coherence.exact 1))))
      (ChannelCursor.initial
        (CoherentNamed.mul
          (CoherentNamed.add (atState (CoherentNamed.ofApproximation approximation) (startingIndex approximation 1))
            (CoherentNamed.Coherence.exact 1))
          (CoherentNamed.add (atState (CoherentNamed.ofApproximation approximation) (startingIndex approximation 1))
            (CoherentNamed.Coherence.exact 1))))
      leftSchedule rightSchedule :=
  ChannelCursor.compareSchedules _ _ (differentStarts approximation) leftSchedule rightSchedule

example (input : CoherentNamed) (first second : input.name.process.State) :
    NamedEquivalent
      (CoherentNamed.add (atState input first) (atState input second)).name
      (CoherentNamed.add (atState input second) (atState input first)).name := by
  ccl_equiv

example (input : CoherentNamed) (first second : input.name.process.State)
    (leftSchedule rightSchedule : List ChannelCursor.RequestStep) :
    ChannelCursor.ScheduleComparison
      (ChannelCursor.initial
        (CoherentNamed.mul (CoherentNamed.add (atState input first) (CoherentNamed.Coherence.exact 1))
          (CoherentNamed.add (atState input first) (CoherentNamed.Coherence.exact 1))))
      (ChannelCursor.initial
        (CoherentNamed.mul (CoherentNamed.add (atState input second) (CoherentNamed.Coherence.exact 1))
          (CoherentNamed.add (atState input second) (CoherentNamed.Coherence.exact 1))))
      leftSchedule rightSchedule :=
  ChannelCursor.compareSchedules _ _ (polynomialLaw input first second) leftSchedule rightSchedule

/-- Execute different finite requests from two already nonempty prefixes at distinct original starting indices. -/
private meta def checkSchedules : IO Unit := do
  let approximation := Sampling.approximation (CoherentNamed.Coherence.exact 2).name
  let input := CoherentNamed.ofApproximation approximation
  let firstState : input.name.process.State := by change Nat; exact 0
  let secondState : input.name.process.State := by change Nat; exact 1
  let first : CoherentNamed := ⟨⟨input.name.process, firstState⟩, input.coherent⟩
  let second : CoherentNamed := ⟨⟨input.name.process, secondState⟩, input.coherent⟩
  let leftChannel := CoherentNamed.mul (CoherentNamed.add first (CoherentNamed.Coherence.exact 1))
    (CoherentNamed.add first (CoherentNamed.Coherence.exact 1))
  let rightChannel := CoherentNamed.mul (CoherentNamed.add second (CoherentNamed.Coherence.exact 1))
    (CoherentNamed.add second (CoherentNamed.Coherence.exact 1))
  let left := (ChannelCursor.initial leftChannel).request 1 (by decide +kernel) 1
  let right := (ChannelCursor.initial rightChannel).request 1 (by decide +kernel) 2
  let firstBindings : Fin 1 → CoherentNamed := fun _ => first
  let secondBindings : Fin 1 → CoherentNamed := fun _ => second
  let firstShift := (Gaussian.Normalized.atom firstBindings 0).add (Gaussian.Normalized.constant firstBindings 1)
  let secondShift := (Gaussian.Normalized.atom secondBindings 0).add (Gaussian.Normalized.constant secondBindings 1)
  let stateLaw := NamedEquivalent.trans (NamedEquivalent.symm (input.rebaseEquivalent firstState))
    (input.rebaseEquivalent secondState)
  have forms : (firstShift.mul firstShift).form.terms = (secondShift.mul secondShift).form.terms := by
    apply congrArg Sparse.terms
    rewrite [Gaussian.Normalized.mul_form, Gaussian.Normalized.add_form,
      Gaussian.Normalized.atom_form, Gaussian.Normalized.constant_form]
    rfl
  let law : BitLaw left.channel right.channel := BitLaw.ofEquivalent
    ((firstShift.mul firstShift).compareAcross (secondShift.mul secondShift) (fun _ => stateLaw) forms)
  let result := ChannelCursor.compareSchedules left right law
    [⟨1, by decide +kernel, 2⟩] [⟨1, by decide +kernel, 3⟩]
  unless result.sourceLeft.cursor.machine.emitted.length = 1 ∧
      result.sourceRight.cursor.machine.emitted.length = 2 ∧
      result.outputLeft.cursor.machine.emitted.length = 3 ∧
      result.outputRight.cursor.machine.emitted.length = 5 do
    throw (IO.userError "independent normalized schedules did not preserve their own prefixes and requested lengths")
  unless ChannelCursor.scheduledBitCount result.requestsLeft = 2 ∧
      ChannelCursor.scheduledBitCount result.requestsRight = 3 do
    throw (IO.userError "schedule comparison discarded the two actual original requests")

#eval checkSchedules

end TestPurelib.Approximation.Gaussian.OperationalRebasing
