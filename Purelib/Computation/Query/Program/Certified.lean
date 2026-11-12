module

public import Purelib.Computation.Query.Program

/-! Certified execution with the original indexed receipt payloads. -/

public section

namespace Purelib.Computation.Query.Program.Certified

variable {Model Receipt Value : Type}

set_option genInjectivity false in
/-- An indexed source and the certified original model retained by each receipt. -/
structure Source (Model Receipt : Type) where
  /-- The original indexed model source. -/ stage : Nat → Model
  /-- The original index reported by a receipt. -/ index : Receipt → Nat
  /-- The actual model readback retained by that receipt. -/ model : Receipt → Model
  /-- Every receipt's model belongs to its reported original index. -/ model_eq :
    ∀ receipt, model receipt = stage (index receipt)

/-- Project the actual ordered receipt execution to its original model readbacks. -/
@[expose] def project (source : Source Model Receipt) (execution : Basic.Execution Nat Receipt Value) :
    Basic.Execution Nat Model Value :=
  ⟨execution.value, execution.trace.map fun exchange => ⟨exchange.query, source.model exchange.reply⟩⟩

/-- Actual receipt execution whose model projection is the original indexed-source execution. -/
abbrev Execution (source : Source Model Receipt) (original : Program Nat Model Value) :=
  {execution : Basic.Execution Nat Receipt Value //
    project source execution = original.protocol.run source.stage ∧
      ∀ exchange ∈ execution.trace, source.index exchange.reply = exchange.query}

/-- Prepend the same returned receipt to the certified original model continuation. -/
@[expose] def prepend (source : Source Model Receipt) (index : Nat)
    (next : Model → Program Nat Model Value) (receipt : Receipt) (same : source.index receipt = index)
    (after : Execution source (next (source.model receipt))) : Execution source (.request index next) := by
  cases after with
  | mk execution valid =>
    refine ⟨⟨execution.value, ⟨index, receipt⟩ :: execution.trace⟩, ?_, ?_⟩
    · have model_eq : source.model receipt = source.stage index :=
        (source.model_eq receipt).trans (congrArg source.stage same)
      have projected := valid.1
      rw [model_eq] at projected
      change (⟨execution.value, ⟨index, source.model receipt⟩ ::
        (execution.trace.map fun exchange => ⟨exchange.query, source.model exchange.reply⟩)⟩ :
          Basic.Execution Nat Model Value) = _
      rw [model_eq]
      exact congrArg (fun tail : Basic.Execution Nat Model Value =>
        (⟨tail.value, ⟨index, source.stage index⟩ :: tail.trace⟩ : Basic.Execution Nat Model Value)) projected
    · intro exchange member
      cases member with
      | head => exact same
      | tail _ tailMember => exact valid.2 exchange tailMember

end Purelib.Computation.Query.Program.Certified

end
