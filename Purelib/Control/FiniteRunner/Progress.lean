module
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-! Finite execution steps retaining indexed progress. -/

namespace Purelib.Control.FiniteRunner.Progress

set_option genInjectivity false in
/-- A successful result or one next state carrying evidence of progress.

The supplied dependent family states what evidence must accompany the next state. The carrier adds no termination or
eventual-success assumption. -/
inductive StepResultPayload.{u, v, w} (readyType : Type u)
    (stateType : Type v) (progressType : stateType -> Type w) :
    Type (max u (max v w))
  /-- Retain a completed preparation. -/ | ready (preparation : readyType)
  /-- Retain the next state with its indexed evidence of progress. -/ | progressed (next : stateType) (progress :
    progressType next)

constructive_injectivity Purelib.Control.FiniteRunner.Progress.StepResultPayload

end Purelib.Control.FiniteRunner.Progress

end
