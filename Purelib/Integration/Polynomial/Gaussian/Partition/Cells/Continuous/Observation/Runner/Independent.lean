module

public import Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous.Observation.Independent
public import Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous.Observation.Runner
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Independent polynomial runners and their ordered source comparison

Each original runner retains its own policy, source, stage receipts and path
states. Their actual returned frontiers are compared in an explicitly aligned
segment order; no relation between independent sources is presumed.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous.Observation.Runner.Independent

open Purelib.Approximation
open Purelib.CCL.Progressive.IntegrationPrograms
open Purelib.Computation.Query
open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Partition
open Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous.Observation

variable {leftSource rightSource : Source.PolynomialPath}
variable {leftPolicy : PartitionPolicy leftSource} {rightPolicy : PartitionPolicy rightSource}
variable (left : Runner.Input leftSource leftPolicy) (right : Runner.Input rightSource rightPolicy)
variable (alignment : Observation.Independent.Alignment leftSource rightSource)

/-- A left runner, right runner or original aligned common-point question. -/
abbrev Query := Sum (Runner.Question left) (Sum (Runner.Question right) (Observation.Independent.Query alignment))

/-- An original source-owner reply for the corresponding runner or aligned comparison. -/
abbrev Reply := Sum (Runner.Reply left) (Sum (Runner.Reply right) (Observation.Independent.Reply alignment))

set_option genInjectivity false in
/-- The first original runner or aligned-source failure, retaining every completed earlier runner. -/
inductive Failure where
  /-- A left-runner request received another operation's reply. -/ | leftOwner (question : Runner.Question left)
  /-- The original left runner failed. -/ | left (invalid : Runner.Failure left)
  /-- A right-runner request received another operation's reply. -/ | rightOwner
      (first : Runner.Result left) (question : Runner.Question right)
  /-- The original right runner failed after the returned left runner. -/ | right
      (first : Runner.Result left) (invalid : Runner.Failure right)
  /-- The aligned comparison failed at its original source occurrence. -/ | comparison
      (first : Runner.Result left) (second : Runner.Result right)
      (invalid : Observation.Independent.Failure alignment first.real second.real first.imaginary second.imaginary)

constructive_injectivity Failure

set_option genInjectivity false in
/-- Two returned original runners and the actual aligned comparison of their returned path states. -/
structure Result where
  /-- The actual returned original left runner, including its selected compilation and receipt bank. -/ left :
    Runner.Result left
  /-- The actual returned original right runner, including its selected compilation and receipt bank. -/ right :
    Runner.Result right
  /-- Common readings at the actual original segment occurrences of those returned paths. -/ comparison :
    Observation.Independent.Result alignment left.real right.real left.imaginary right.imaginary

constructive_injectivity Result

/-- Answer every displayed request through its original runner or source owner. -/
@[expose] def original : Query left right alignment → Reply left right alignment
  | .inl question => .inl (Runner.originalReply left question)
  | .inr (.inl question) => .inr (.inl (Runner.originalReply right question))
  | .inr (.inr question) => .inr (.inr (Observation.Independent.original alignment question))

/-- Forward the original left runner operation. -/
@[expose] def leftHandler (question : Runner.Question left) :
    Program (Query left right alignment) (Reply left right alignment) (Except (Failure left right alignment)
      (Runner.Reply left)) :=
  .request (.inl question) fun returned => match returned with
    | .inl reply => .pure (.ok reply)
    | .inr _ => .pure (.error (.leftOwner question))

/-- Forward the original right runner operation, retaining the completed left runner. -/
@[expose] def rightHandler (first : Runner.Result left) (question : Runner.Question right) :
    Program (Query left right alignment) (Reply left right alignment) (Except (Failure left right alignment)
      (Runner.Reply right)) :=
  .request (.inr (.inl question)) fun returned => match returned with
    | .inr (.inl reply) => .pure (.ok reply)
    | _ => .pure (.error (.rightOwner first question))

/-- Forward an aligned source reply; a different outer operation becomes a local missing reply. -/
@[expose] def comparisonHandler (question : Observation.Independent.Query alignment) :
    Program (Query left right alignment) (Reply left right alignment) (Except (Failure left right alignment)
      (Option (Observation.Independent.Reply alignment))) :=
  .request (.inr (.inr question)) fun returned => match returned with
    | .inr (.inr reply) => .pure (.ok (some reply))
    | _ => .pure (.ok none)

/-- Execute both original runners and compare their actual returned path frontiers in aligned order.

Both original runner receipt banks and selected compilations remain in the
returned records. The initial common-reading cache is empty; the returned
comparison retains every actual per-segment coordinate budget. -/
@[expose] def computation : Program (Query left right alignment) (Reply left right alignment)
    (Except (Failure left right alignment) (Result left right alignment)) :=
  ((Runner.computation left).substituteChecked (leftHandler left right alignment)).bind fun first =>
    match first with
    | .error invalid => .pure (.error invalid)
    | .ok execution => match execution.value with
      | .error invalid => .pure (.error (.left invalid))
      | .ok first => ((Runner.computation right).substituteChecked (rightHandler left right alignment first)).bind
          fun second => match second with
          | .error invalid => .pure (.error invalid)
          | .ok execution => match execution.value with
            | .error invalid => .pure (.error (.right first invalid))
            | .ok second =>
                ((Observation.Independent.computationOptional alignment first.real second.real
                    first.imaginary second.imaginary
                      (Observation.Independent.emptyCache alignment first.real second.real
                        first.imaginary second.imaginary)).substituteChecked
                        (comparisonHandler left right alignment)).map fun compared =>
                    match compared with
                    | .error invalid => .error invalid
                    | .ok execution => match execution.value with
                      | .error invalid => .error (.comparison first second invalid)
                      | .ok result => .ok ⟨first, second, result⟩

/-- Original replies return both original runner results and their actual aligned common readings. -/
theorem computation_original :
    ∃ result : Result left right alignment,
      ((computation left right alignment).protocol.run (original left right alignment)).value = .ok result ∧
      ((Runner.computation left).protocol.run (Runner.originalReply left)).value = .ok result.left ∧
      ((Runner.computation right).protocol.run (Runner.originalReply right)).value = .ok result.right ∧
      result.comparison = Observation.Independent.originalResult alignment result.left.real result.right.real
        result.left.imaginary result.right.imaginary := by
  obtain ⟨first, firstOk, _⟩ := Runner.computation_original left
  obtain ⟨second, secondOk, _⟩ := Runner.computation_original right
  refine ⟨⟨first, second, Observation.Independent.originalResult alignment first.real second.real
    first.imaginary second.imaginary⟩, ?_, firstOk, secondOk, rfl⟩
  unfold computation
  rw [Program.bind_execution, Protocol.bind_run_value]
  have firstForward := Program.substituteChecked_value (leftHandler left right alignment) (Runner.computation left)
    (original left right alignment) (Runner.originalReply left) (by intro; rfl)
  rw [firstForward]
  dsimp only
  rw [firstOk]
  dsimp only
  rw [Program.bind_execution, Protocol.bind_run_value]
  have secondForward := Program.substituteChecked_value (rightHandler left right alignment first)
    (Runner.computation right)
    (original left right alignment) (Runner.originalReply right) (by intro; rfl)
  rw [secondForward]
  dsimp only
  rw [secondOk]
  dsimp only
  rw [Program.map_execution, Protocol.map_run_value]
  have compared := Program.substituteChecked_value (comparisonHandler left right alignment)
    (Observation.Independent.computationOptional alignment first.real second.real first.imaginary second.imaginary
      (Observation.Independent.emptyCache alignment first.real second.real first.imaginary second.imaginary))
    (original left right alignment) (fun question => some (Observation.Independent.original alignment question))
    (by intro; rfl)
  rw [compared]
  dsimp only
  rw [Observation.Independent.computationOptional_original]

/-- Exact replay recovers the actual returned runners, common readings and typed failures. -/
theorem replay (oracle : Query left right alignment → Reply left right alignment) :
    let program := computation left right alignment
    program.protocol.replayExact (program.protocol.run oracle).trace = .ok (program.protocol.run oracle).value :=
  (computation left right alignment).protocol.replayExact_run oracle

/-- Replies outside the displayed runner and aligned point requests preserve the complete execution. -/
theorem payload_erasure (oracle : Query left right alignment → Reply left right alignment) {Payload : Type}
    (payload : Payload)
    (outside : Payload → Query left right alignment → Reply left right alignment) :
    let program := computation left right alignment
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run oracle).trace
      (outside payload)) = program.protocol.run oracle :=
  (computation left right alignment).protocol.annotation_erasure oracle payload outside

/-- The actual common-point budgets bound the original selected Gaussian runner samples. -/
theorem Result.samples_normSq_le (result : Result left right alignment) :
    Norm.Basic.normSq (result.left.recorded.observation.selected.sample -
      result.right.recorded.observation.selected.sample) ≤
      (Observation.Independent.realBudget alignment result.left.real result.right.real
        result.left.imaginary result.right.imaginary result.comparison) ^ 2 +
      (Observation.Independent.imaginaryBudget alignment result.left.real result.right.real
        result.left.imaginary result.right.imaginary result.comparison) ^ 2 := by
  rw [result.left.selected_sample, result.right.selected_sample,
    result.left.selected.compiled.sample_eq, result.right.selected.compiled.sample_eq]
  exact Observation.Independent.samples_normSq_le alignment result.left.real result.right.real
    result.left.imaginary result.right.imaginary result.comparison result.left.selected.compiled.cells
    result.right.selected.compiled.cells

/-- Recompare the two exact returned path owners using their retained common readings. -/
@[expose] def Result.recompare (result : Result left right alignment) :=
  Observation.Independent.computationOptional alignment result.left.real result.right.real
    result.left.imaginary result.right.imaginary
    (Observation.Independent.cacheOf alignment result.left.real result.right.real
      result.left.imaginary result.right.imaginary result.comparison)

/-- The exact retained comparison returns unchanged without another source request. -/
theorem Result.recompare_reused (result : Result left right alignment) :
    result.recompare = .pure (.ok result.comparison) :=
  Observation.Independent.computationOptional_reused alignment result.left.real result.right.real
    result.left.imaginary result.right.imaginary result.comparison

/-- Reobserving those exact returned owners makes no source call for any supplied replies. -/
theorem Result.recompare_trace (result : Result left right alignment)
    (oracle : Observation.Independent.Query alignment → Option (Observation.Independent.Reply alignment)) :
    (result.recompare.protocol.run oracle).trace = [] := by
  rw [Result.recompare_reused]
  rfl

end Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous.Observation.Runner.Independent

end
