module

public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Expansion
public import Purelib.Computation.Query.Program.Certified

/-! Actual original integration runner receipts and their selected first model. -/

public section

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Receipt

open Purelib.CCL.Progressive.IntegrationReplay
open Purelib.Computation.Query
open Purelib.Integration.CertifiedProgram (Request)

variable {Reply : Type} (program : CachedProgram) (source : Program.Certified.Source CachedModel Reply)
variable (source_eq : source.stage = program.stage) (request : Request) (count : Nat)

/-- An actual complete receipt execution of the original integration query construction. -/
abbrev Execution := Program.Certified.Execution source (Expansion.program (control program) request count)

include source_eq

/-- Construct the original record directly from the actual receipt execution's model projection. -/
@[expose] def record (execution : Execution program source request count) (observation : Replay.Observation)
    (success : execution.val.value = .ok observation) : Record.Recorded program request count := by
  cases execution with
  | mk actual certified =>
    have same := certified.1.trans (Expansion.program_execution (control program) request count source.stage)
    rw [source_eq] at same
    exact ⟨observation, (Program.Certified.project source actual).trace,
      (congrArg Basic.Execution.value same).symm.trans success, congrArg Basic.Execution.trace same⟩

/-- An actual receipt execution for a successful integration request has a nonempty trace. -/
theorem trace_nonempty (execution : Execution program source request count) (observation : Replay.Observation)
    (success : execution.val.value = .ok observation) : execution.val.trace ≠ [] := by
  intro empty
  apply (record program source source_eq request count execution observation success).trace_nonempty
  change execution.val.trace.map (fun exchange =>
    (⟨exchange.query, source.model exchange.reply⟩ : Basic.Exchange Nat CachedModel)) = []
  rw [empty]
  rfl

/-- Read the actual first receipt from the returned original integration execution. -/
@[expose] def selected (execution : Execution program source request count) (observation : Replay.Observation)
    (success : execution.val.value = .ok observation) : Reply :=
  (execution.val.trace.head (trace_nonempty program source source_eq request count execution observation success)).reply

omit source_eq in
/-- Mapping a nonempty actual list preserves its first entry. -/
private theorem map_head {A B : Type} (f : A → B) : ∀ (values : List A)
    (nonempty : values ≠ []) (mapped : values.map f ≠ []),
    (values.map f).head mapped = f (values.head nonempty)
  | [], nonempty, _ => (nonempty rfl).elim
  | _ :: _, _, _ => rfl

omit source_eq in
/-- A nonempty returned list contains its first entry. -/
private theorem head_mem {A : Type} : ∀ (values : List A) (nonempty : values ≠ []), values.head nonempty ∈ values
  | [], nonempty => (nonempty rfl).elim
  | _ :: _, _ => List.Mem.head _

/-- The selected receipt's actual model is the original record's selected model. -/
theorem selected_model (execution : Execution program source request count) (observation : Replay.Observation)
    (success : execution.val.value = .ok observation) :
    source.model (selected program source source_eq request count execution observation success) =
      (record program source source_eq request count execution observation success).selectedExchange.reply := by
  let values := execution.val.trace
  let nonempty := trace_nonempty program source source_eq request count execution observation success
  let mapped := (record program source source_eq request count execution observation success).trace_nonempty
  have first := map_head (fun exchange : Basic.Exchange Nat Reply =>
    (⟨exchange.query, source.model exchange.reply⟩ : Basic.Exchange Nat CachedModel)) values nonempty mapped
  exact (congrArg Basic.Exchange.reply first).symm

/-- The actual selected receipt reports the original integration request's selected index. -/
theorem selected_index (execution : Execution program source request count) (observation : Replay.Observation)
    (success : execution.val.value = .ok observation) :
    source.index (selected program source source_eq request count execution observation success) =
      selectedIndex (control program) request := by
  let values := execution.val.trace
  let nonempty := trace_nonempty program source source_eq request count execution observation success
  let mapped := (record program source source_eq request count execution observation success).trace_nonempty
  have first := map_head (fun exchange : Basic.Exchange Nat Reply =>
    (⟨exchange.query, source.model exchange.reply⟩ : Basic.Exchange Nat CachedModel)) values nonempty mapped
  have query := (congrArg Basic.Exchange.query first).symm.trans
    (congrArg Basic.Exchange.query
      (record program source source_eq request count execution observation success).selectedExchange_eq)
  exact (execution.property.2 (values.head nonempty) (head_mem values nonempty)).trans query

end Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Receipt

end
