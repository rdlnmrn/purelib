module
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-! Completed payloads and resumable finite execution attempts. -/

namespace Purelib.Control.FiniteRunner.LegendreFold

set_option genInjectivity false in
/-- A completed result or a retained state from a finite execution attempt.

The two constructors preserve the supplied payload types. Exhaustion carries a resumable state and makes no claim that
future execution cannot succeed. -/
inductive ResultPayload (readyType stateType : Type 1) : Type 1
  /-- Retain the completed payload. -/ | ready (preparations : readyType)
  /-- Retain the unfinished state for a later attempt. -/ | exhausted (cursor : stateType)

constructive_injectivity Purelib.Control.FiniteRunner.LegendreFold.ResultPayload

end Purelib.Control.FiniteRunner.LegendreFold

end

section
@[expose] public section

/-! Universe-polymorphic outcomes and bounded inspection. -/

namespace Purelib.Control.FiniteRunner
namespace LegendreTransport

set_option genInjectivity false in
/-- A completed result or a retained state from a finite execution attempt.

The two constructors preserve the supplied payload types. Exhaustion carries a resumable state and makes no claim that
future execution cannot succeed. -/
inductive ResultPayload.{u, v} (readyType : Type u) (stateType :
  Type v) : Type (max u v)
  /-- Retain the completed payload. -/ | ready (result : readyType)
  /-- Retain the unfinished state for a later attempt. -/ | exhausted (state : stateType)

constructive_injectivity Purelib.Control.FiniteRunner.LegendreTransport.ResultPayload

end LegendreTransport
namespace Basic

/-- Run at most the supplied number of inspections, retaining the current state on exhaustion.

An inspection returns either a completed result or the next state. Zero fuel performs no inspection, and each
unsuccessful inspection consumes exactly one unit of fuel. -/
def runPayload {readyType : Type u} {stateType : Type v}
    (inspect : stateType → Sum readyType stateType) (state : stateType) :
    Nat → LegendreTransport.ResultPayload readyType stateType
  | 0 => .exhausted state
  | fuel + 1 => match inspect state with
      | .inl result => .ready result
      | .inr next => Purelib.Control.FiniteRunner.Basic.runPayload inspect next fuel

/-- Splitting a finite inspection budget preserves the result and retained state.

A successful first run remains successful. An exhausted first run resumes from its exact retained state with the
remaining budget, giving the same outcome as one run with the summed budget. -/
theorem runPayload_add {readyType : Type u} {stateType : Type v}
    (inspect : stateType → Sum readyType stateType) (state : stateType)
    (first second : Nat) :
    Basic.runPayload inspect state (first + second) =
      match Basic.runPayload inspect state first with
      | .ready result => .ready result
      | .exhausted retained => Basic.runPayload inspect retained second := by
  induction first generalizing state with
  | zero => rw [Nat.zero_add, Basic.runPayload]
  | succ first inductionHypothesis =>
      rw [Nat.succ_add, Basic.runPayload, Basic.runPayload]
      cases inspect state with
      | inl result => rfl
      | inr next => exact inductionHypothesis next
end Basic
end Purelib.Control.FiniteRunner

end
