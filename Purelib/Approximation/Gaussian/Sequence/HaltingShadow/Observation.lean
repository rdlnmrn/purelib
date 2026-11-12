module

public import Purelib.Approximation.Gaussian.Sequence.HaltingShadow
public import Purelib.Computation.Query.Computation
import Purelib.Data.Nat.Order

/-!
# Finite numerical queries cannot classify all halting shadows

An indexed numerical reply contains the original bounded sample and its
successor quarter-power allowance. A finite protocol's actual ordered trace
has an explicit maximum queried bound. A delayed finite program first halts
after that maximum and returns every earlier numerical reply unchanged.
The complete adaptive execution therefore remains unchanged as well.
This theorem concerns fixed numerical protocols; program-code classifiers
have a separate represented-computation reduction.
-/

public section

namespace Purelib.Approximation.Gaussian.Sequence.HaltingShadow

open Purelib
open Purelib.Computation
open Purelib.Computation.Query
open Purelib.Data.Nat

namespace Code

/-- Read the original numerical shadow ball at its displayed finite simulation bound. -/
@[expose] def observe (code : Code) (index : Nat) : Gaussian.Enclosure.Ball :=
  code.process.ball (show code.process.State from index)

end Code

/-- The indexed zero-centred numerical reply retains the same original successor allowance. -/
@[expose] def zeroReply (index : Nat) : Gaussian.Enclosure.Ball := ⟨0, radiusSq index, (radiusSq_pos index).le⟩

namespace Code

/-- Bounded absence makes this same original numerical shadow reply exactly the retained zero-centred ball. -/
theorem observe_of_none (code : Code) {index : Nat} (absent : code.firstHalt index = none) :
    code.observe index = zeroReply index := by
  have sampleEq : code.sample index = 0 := by unfold sample; rewrite [absent]; rfl
  change (⟨code.sample index, radiusSq index, (radiusSq_pos index).le⟩ : Gaussian.Enclosure.Ball) = _
  rewrite [sampleEq]
  rfl

/-- Every numerical reply of the explicit never-halting program is its same indexed zero-centred ball. -/
theorem observe_loop (input : Machine.Value) (index : Nat) :
    (ofProgram Machine.Program.loop input).observe index = zeroReply index :=
  (ofProgram Machine.Program.loop input).observe_of_none (Machine.Halting.loop_absent input index)

/-- A delayed finite program returns the same indexed zero-centred ball through its original tick count. -/
theorem observe_delay (ticks : Nat) (input : Machine.Value) {index : Nat} (within : index ≤ ticks) :
    (ofProgram (Machine.Program.delay ticks) input).observe index = zeroReply index :=
  (ofProgram (Machine.Program.delay ticks) input).observe_of_none (Machine.Halting.delay_absent ticks input within)

end Code

namespace Observation

/-- Compute the maximum of the actual requested finite bounds, preserving an empty trace's zero bound. -/
@[expose] def traceBound : Basic.Trace Nat Gaussian.Enclosure.Ball → Nat
  | [] => 0
  | entry :: remaining => Nat.max entry.query (traceBound remaining)

/-- Every actual original query is bounded by the same retained finite trace maximum. -/
theorem query_le_bound (trace : Basic.Trace Nat Gaussian.Enclosure.Ball)
    (entry : Basic.Exchange Nat Gaussian.Enclosure.Ball) (member : entry ∈ trace) : entry.query ≤ traceBound trace := by
  induction trace with
  | nil => nomatch member
  | cons head remaining induction =>
      cases member with
      | head => exact Order.le_max_left _ _
      | tail _ included => exact Nat.le_trans (induction included) (Order.le_max_right _ _)

/-- A program delayed beyond the actual trace maximum preserves the entire fixed adaptive numerical execution. -/
theorem delayed_execution {Value : Type} (protocol : Protocol Nat Gaussian.Enclosure.Ball Value)
    (input : Machine.Value) :
    let original := Code.ofProgram Machine.Program.loop input
    let bound := traceBound (protocol.run original.observe).trace
    let delayed := Code.ofProgram (Machine.Program.delay bound) input
    protocol.run delayed.observe = protocol.run original.observe := by
  intro original bound delayed
  apply protocol.run_of_answers
  intro entry member
  have within := query_le_bound (protocol.run original.observe).trace entry member
  have delayedReply := Code.observe_delay bound input within
  have originalReply := Code.observe_loop input entry.query
  exact delayedReply.trans (originalReply.symm.trans (protocol.answers_run original.observe entry member))

set_option genInjectivity false in
/-- A fixed finite numerical classifier returns zero or reached apartness with sound original-owner certificates. -/
structure Classifier where
  /-- The same source-independent numerical protocol for all finite shadow descriptions. -/ protocol :
    Protocol Nat Gaussian.Enclosure.Ball Bool
  /-- A reported zero carries operational equality of this original shadow with exact zero. -/ zeroSound :
    ∀ code : Code, (protocol.run code.observe).value = false →
      Gaussian.Equivalence.NamedEquivalent code.named.name (Gaussian.Name.Basic.Named.exact 0)
  /-- A reported apartness carries its actual reached state and positive candidate bound. -/ apartSound :
    ∀ code : Code, (protocol.run code.observe).value = true → code.ReachedApart

/-- No fixed finite numerical protocol can soundly classify every shadow as operational zero or reached apartness. -/
theorem no_classifier (classifier : Classifier) : False := by
  let input := Machine.Value.number 0
  let original := Code.ofProgram Machine.Program.loop input
  let execution := classifier.protocol.run original.observe
  cases outcome : execution.value with
  | true =>
      have reached := classifier.apartSound original outcome
      have halted := original.halts_of_apart reached
      rcases (Machine.Halting.halts_iff_firstHalt original.initial).mp halted with ⟨bound, stage, observed⟩
      have absent := Machine.Halting.loop_absent input bound
      have impossible := absent.symm.trans observed
      nomatch impossible
  | false =>
      let bound := traceBound execution.trace
      let delayed := Code.ofProgram (Machine.Program.delay bound) input
      have same := delayed_execution classifier.protocol input
      have delayedOutcome : (classifier.protocol.run delayed.observe).value = false :=
        (congrArg Basic.Execution.value same).trans outcome
      have noHalt := delayed.noHalt_of_zero (classifier.zeroSound delayed delayedOutcome)
      exact noHalt ⟨bound + 1, input, Machine.Simulation.delay_halted bound input⟩

end Observation

end Purelib.Approximation.Gaussian.Sequence.HaltingShadow

end
