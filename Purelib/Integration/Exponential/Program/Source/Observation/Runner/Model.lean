module

public import Purelib.Integration.Exponential.Program.Source.Observation.Runner
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Receipt
public import Purelib.Computation.Query.Program.Certified.Cache
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Expansion

/-!
# Authenticated model acquisition for the original exponential runner

Each model request is answered by an indexed receipt carrying the actual
cached model and its original retained-program identity. The original query
construction controls every continuation. Successful lowering retains the
same complete model execution, including its ordered original model log.
-/

public section

namespace Purelib.Integration.Exponential.Program.Source.Observation.Runner.Model

open Purelib.Computation.Query
open Purelib.Data.Nat.Schedule
open Purelib.Integration.Exponential
open Purelib.Integration.Program.Gaussian
open Purelib.Integration.Program.Gaussian.CCL
open Purelib.Integration.Program.Gaussian.CCL.Replay
open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation
open Purelib.CCL.Progressive.IntegrationReplay

set_option genInjectivity false in
/-- A returned original model together with its exact retained program and requested index. -/
structure Receipt {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) where
  /-- The reported original stage index. -/ index : Nat
  /-- The actual selected Taylor geometry. -/ selection : Selection index
  /-- The selection comes from this retained original program. -/ selection_eq :
    selection = retained.selection index
  /-- The actual returned cached model. -/ model : Cached.Basic.CachedModel
  /-- The returned model is the original retained program stage at that index. -/ model_eq :
    model = retained.program.stage index

/-- Read the original selected geometry and its cached model once at the displayed index. -/
@[expose] def originalReply {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat) : Receipt retained :=
  let selected := retained.selectedStage index
  ⟨index, selected.selection, selected.selection_eq, selected.model, selected.model_eq⟩

/-- The original program and complete selection-bearing receipts as a certified indexed source. -/
@[expose] def receiptSource {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) :
    Program.Certified.Source Cached.Basic.CachedModel (Receipt retained) :=
  ⟨retained.program.stage, Receipt.index, Receipt.model, Receipt.model_eq⟩

/-- A failed original model request retaining its actual bank and any rejected receipt. -/
abbrev Invalid {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) :=
  Program.Certified.Cache.Failure (receiptSource retained)

/-- Continue original model queries using the supplied same-owner receipt bank. -/
@[expose] def receiptComputation {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) {Value : Type}
    (bank : List (Receipt retained)) (original : Program Nat Cached.Basic.CachedModel Value) :=
  Program.Certified.Cache.computation (receiptSource retained) bank original

/-- A complete original model execution certified against the same retained program. -/
abbrev Certified {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) {Value : Type}
    (original : Program Nat Cached.Basic.CachedModel Value) :=
  {execution : Basic.Execution Nat Cached.Basic.CachedModel Value //
    execution = original.protocol.run retained.program.stage}

/-- Project a complete actual receipt execution to the certified original model execution. -/
@[expose] def projectExecution {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) {Value : Type}
    {original : Program Nat Cached.Basic.CachedModel Value}
    (execution : Program.Certified.Execution (receiptSource retained) original) : Certified retained original :=
  ⟨Program.Certified.project (receiptSource retained) execution.val, execution.property.1⟩

/-- Build the existing original runner record from its actual authenticated execution and successful observation.

The original model trace is reused directly. The retained equality certifies
both record fields; no stage, model or runner query is repeated. -/
@[expose] def recorded {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (request : CertifiedProgram.Request) (count : Nat)
    (execution : Certified retained (Expansion.program (control retained.program) request count))
    (observation : Replay.Observation) (success : execution.val.value = .ok observation) :
    Record.Recorded retained.program request count := by
  have same := execution.property.trans
    (Expansion.program_execution (control retained.program) request count retained.program.stage)
  exact ⟨observation, execution.val.trace, (congrArg Basic.Execution.value same).symm.trans success,
    congrArg Basic.Execution.trace same⟩

/-- The resulting original runner record retains the actual authenticated model trace. -/
theorem recorded_trace {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (request : CertifiedProgram.Request) (count : Nat)
    (execution : Certified retained (Expansion.program (control retained.program) request count))
    (observation : Replay.Observation) (success : execution.val.value = .ok observation) :
    (recorded retained request count execution observation success).trace = execution.val.trace := rfl

/-- A complete actual receipt execution of one original integration observation. -/
abbrev ReceiptExecution {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (request : CertifiedProgram.Request) (count : Nat) :=
  Program.Certified.Execution (receiptSource retained) (Expansion.program (control retained.program) request count)

/-- Build the existing original record from the actual certified receipt execution. -/
@[expose] def receiptRecord {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (request : CertifiedProgram.Request) (count : Nat)
    (execution : ReceiptExecution retained request count) (observation : Replay.Observation)
    (success : execution.val.value = .ok observation) : Record.Recorded retained.program request count :=
  Replay.Observation.Receipt.record retained.program (receiptSource retained) rfl request count
    execution observation success

/-- The actual receipt execution has the original selected query at its head. -/
theorem receiptTrace_nonempty {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (request : CertifiedProgram.Request) (count : Nat)
    (execution : ReceiptExecution retained request count) (observation : Replay.Observation)
    (success : execution.val.value = .ok observation) : execution.val.trace ≠ [] :=
  Replay.Observation.Receipt.trace_nonempty retained.program (receiptSource retained) rfl request count
    execution observation success

/-- Read the actual first selected-stage receipt from the returned runner execution. -/
@[expose] def selectedReceipt {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (request : CertifiedProgram.Request) (count : Nat)
    (execution : ReceiptExecution retained request count) (observation : Replay.Observation)
    (success : execution.val.value = .ok observation) : Receipt retained :=
  Replay.Observation.Receipt.selected retained.program (receiptSource retained) rfl request count
    execution observation success

/-- The actual selected receipt's model is the existing record's selected model cache. -/
theorem selectedReceipt_model {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (request : CertifiedProgram.Request) (count : Nat)
    (execution : ReceiptExecution retained request count) (observation : Replay.Observation)
    (success : execution.val.value = .ok observation) :
    (selectedReceipt retained request count execution observation success).model =
      (receiptRecord retained request count execution observation success).selectedExchange.reply :=
  Replay.Observation.Receipt.selected_model retained.program (receiptSource retained) rfl request count
    execution observation success

/-- The selected actual receipt reports the original integration request's selected index. -/
theorem selectedReceipt_index {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (request : CertifiedProgram.Request) (count : Nat)
    (execution : ReceiptExecution retained request count) (observation : Replay.Observation)
    (success : execution.val.value = .ok observation) :
    (selectedReceipt retained request count execution observation success).index =
      selectedIndex (control retained.program) request :=
  Replay.Observation.Receipt.selected_index retained.program (receiptSource retained) rfl request count
    execution observation success

/-- A returned receipt is determined by its original retained stage index. -/
theorem Receipt.eq_of_index {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    {retained : Program.Retained policy schedule extraDepth} (first second : Receipt retained)
    (same : first.index = second.index) : first = second := by
  cases first with
  | mk firstIndex firstSelection firstSelectionEq firstModel firstModelEq =>
    cases second with
    | mk secondIndex secondSelection secondSelectionEq secondModel secondModelEq =>
      cases same
      have selectionSame := firstSelectionEq.trans secondSelectionEq.symm
      cases selectionSame
      have modelSame := firstModelEq.trans secondModelEq.symm
      cases modelSame
      rfl

/-- The actual first returned receipt belongs to the original selected stage. -/
theorem selectedReceipt_original {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (request : CertifiedProgram.Request) (count : Nat)
    (execution : ReceiptExecution retained request count) (observation : Replay.Observation)
    (success : execution.val.value = .ok observation) :
    selectedReceipt retained request count execution observation success =
      originalReply retained (selectedIndex (control retained.program) request) :=
  Receipt.eq_of_index _ _ (selectedReceipt_index retained request count execution observation success)

end Purelib.Integration.Exponential.Program.Source.Observation.Runner.Model

end
