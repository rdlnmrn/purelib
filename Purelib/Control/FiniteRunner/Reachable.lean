module
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-! Finite execution outcomes retaining reachability evidence. -/

namespace Purelib.Control.FiniteRunner.Reachable

set_option genInjectivity false in
/-- A budget-indexed result retaining a final state and its reachability evidence.

Both success and exhaustion preserve evidence in the supplied state-dependent family; success additionally carries the
prepared output. The fuel index labels the attempt without itself asserting how many steps were executed. -/
inductive RunResultPayload.{u, v, w} (readyType : Type u)
    (stateType : Type v) (reachableType : stateType -> Type w) :
    Nat -> Type (max u (max v w))
  /-- Retain the reached state, its reachability evidence and a successful preparation. -/ | ready {fuel : Nat} (final :
    stateType)
      (reachable : reachableType final) (preparation : readyType) :
      Purelib.Control.FiniteRunner.Reachable.RunResultPayload readyType stateType reachableType fuel
  /-- Retain the reached state and its reachability evidence after the attempt stops. -/ | exhausted {fuel : Nat} (final
    : stateType)
      (reachable : reachableType final) :
      Purelib.Control.FiniteRunner.Reachable.RunResultPayload readyType stateType reachableType fuel

constructive_injectivity Purelib.Control.FiniteRunner.Reachable.RunResultPayload

end Purelib.Control.FiniteRunner.Reachable

end
