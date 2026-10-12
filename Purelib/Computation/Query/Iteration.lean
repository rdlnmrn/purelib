module

public import Purelib.Computation.Query.Computation
import Purelib.Data.List.Append
import Mathlib.Tactic.Linter.Lint

/-!
# Splitting finite query iteration

The retained finite protocol first runs a specified number of adaptive steps,
then continues with the same returned state. Splitting the count preserves the
complete returned value and ordered concatenation of both recorded traces.
-/

public section

namespace Purelib.Computation.Query.Protocol

-- Retain the established Iteration.Computation.iterate_run_add theorem name.

open Purelib.Computation.Query
open _root_.Purelib.Computation.Query renaming Protocol -> Protocol
open Purelib.Data.List

universe u v w

/-- Splitting finite iteration preserves the returned state and concatenated trace.

Running the first count and then the extra count from its retained returned state
gives the same execution as their sum. Both traces retain the original order
and multiplicity of every adaptive query occurrence. -/
theorem iterate_run_add {Query : Type u} {Reply : Type v} {Value : Type w}
    (step : Value → Protocol Query Reply Value)
    (first extra : Nat) (state : Value) (oracle : Query → Reply) :
    (Protocol.iterate step (first + extra) state).run oracle =
      let before := (Protocol.iterate step first state).run oracle
      let after := (Protocol.iterate step extra before.value).run oracle
      ⟨after.value, before.trace ++ after.trace⟩ := by
  induction first generalizing state with
  | zero => rw [Nat.zero_add]; rfl
  | succ first induction =>
      let current := (step state).run oracle
      let before := (Protocol.iterate step first current.value).run oracle
      let after := (Protocol.iterate step extra before.value).run oracle
      have remainder := induction current.value
      change (Protocol.iterate step (first + extra) current.value).run oracle =
        ⟨after.value, before.trace ++ after.trace⟩ at remainder
      rw [Nat.succ_add]
      change (⟨((Protocol.iterate step (first + extra) current.value).run oracle).value,
        current.trace ++ ((Protocol.iterate step (first + extra) current.value).run oracle).trace⟩ :
          Basic.Execution Query Reply Value) =
        ⟨after.value, (current.trace ++ before.trace) ++ after.trace⟩
      rw [remainder]
      exact congrArg (fun trace => Basic.Execution.mk after.value trace)
        (Append.append_assoc current.trace before.trace after.trace).symm

end Purelib.Computation.Query.Protocol
