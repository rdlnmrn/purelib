module

public import Purelib.Integration.Exponential.Program.Source.Observation.Numerical.Points.Cached

/-!
# Continue an interrupted original common-point batch

The original effective point banks, certified completed prefix and pending
Gaussian state remain fixed. Only the interrupted ball is requested again;
the untouched suffix is then executed in the original order.
-/

public section

namespace Purelib.Integration.Exponential.Program.Source.Observation.Numerical.Points.Resume

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Computation.Query
open Purelib.Data.Rat
open Purelib.Integration.NumericalFrontier
open Purelib.Integration.NumericalFrontier.Common.Observation

variable (depth : Nat) (left : NumericalFrontier (Points.finiteProcess depth))
  (right : NumericalFrontier Horner.Real.source)
  (effectiveLeft : List (NumericalPoint (Points.finiteProcess depth)))
  (effectiveRight : List (NumericalPoint Horner.Real.source)) (request : AccuracyRequest)

/-- A failure owned by the same actual effective banks and saved input banks. -/
abbrev Failure (savedLeft : List (NumericalPoint (Points.finiteProcess depth)))
    (savedRight : List (NumericalPoint Horner.Real.source)) :=
  Independent.Cache.Failure left right request
    (Cached.ProgressFailure depth left right effectiveLeft effectiveRight request) savedLeft savedRight

/-- The original certified batch stopped at an actual common occurrence. -/
abbrev Stopped (savedLeft : List (NumericalPoint (Points.finiteProcess depth)))
    (savedRight : List (NumericalPoint Horner.Real.source)) :=
  Independent.Cache.BatchStopped left right effectiveLeft effectiveRight request savedLeft savedRight
    (Cached.ProgressFailure depth left right effectiveLeft effectiveRight request)

/-- The two exact bank-selected owners at one original common occurrence. -/
abbrev Pair (index : Independent.Index left right) :=
  Independent.Cache.SelectedPair left right effectiveLeft effectiveRight request index

set_option genInjectivity false in
/-- An originally stopped batch does not contain a pending receipt for its failed occurrence. -/
inductive Invalid where
  /-- The cached failure names an occurrence different from the batch failure. -/
  | batchIndex (cached batch : Independent.Index left right) (different : cached ≠ batch)
  /-- The checked pending view found no receipt or a different occurrence. -/
  | pending (invalid : Cached.PendingAccessFailure depth left right)

set_option genInjectivity false in
/-- One finite retry, retaining all original owners and any later stopped batch. -/
inductive Result (savedLeft : List (NumericalPoint (Points.finiteProcess depth)))
    (savedRight : List (NumericalPoint Horner.Real.source)) (stopped : Stopped depth left right effectiveLeft
      effectiveRight request savedLeft savedRight) where
  /-- The original failure cannot be resumed as this pending occurrence. -/
  | invalid (invalid : Invalid depth left right)
  /-- The same pending ball failed again; its updated exact receipt is retained. -/
  | pending (next : Stopped depth left right effectiveLeft effectiveRight request savedLeft savedRight)
  /-- The resumed point succeeded and a later original occurrence stopped. -/
  | later (point : Pair depth left right effectiveLeft effectiveRight request stopped.failed)
      (next : Stopped depth left right effectiveLeft effectiveRight request stopped.reason.leftBank
        (point.2.val :: stopped.reason.rightBank))
  /-- The actual resumed point and untouched suffix assemble the original full common refinement. -/
  | completed (point : Pair depth left right effectiveLeft effectiveRight request stopped.failed)
      (suffix : Program.CertifiedBatch (Independent.Cache.originalChild left right effectiveLeft effectiveRight request)
        stopped.after)
      (common : CommonReadings left right request)
      (same : common = Independent.Cache.assemble left right effectiveLeft effectiveRight request
        (Program.CertifiedBatch.Stopped.finish
          (Independent.Cache.originalChild left right effectiveLeft effectiveRight request)
          (Independent.Cache.SelectedPair left right effectiveLeft effectiveRight request)
          (Independent.Cache.returnedChild left right effectiveLeft effectiveRight request)
          (Independent.Cache.returnedChild_eq left right effectiveLeft effectiveRight request) stopped point suffix))

/-- Resume exactly the retained pending point, then execute only its original untouched suffix. -/
def computation (savedLeft : List (NumericalPoint (Points.finiteProcess depth)))
    (savedRight : List (NumericalPoint Horner.Real.source))
    (stopped : Stopped depth left right effectiveLeft effectiveRight request savedLeft savedRight) :
    Program Points.Query (Option (Points.Reply depth))
      (Result depth left right effectiveLeft effectiveRight request savedLeft savedRight stopped) :=
  if matching : stopped.reason.failed = stopped.failed then
    match Cached.pendingView depth left right effectiveLeft effectiveRight request savedLeft savedRight
      stopped.reason with
    | .error invalid => .pure (.invalid (.pending invalid))
    | .ok view =>
      let same := view.property.1.trans matching
      let receipt : Cached.Pending depth left right effectiveLeft effectiveRight request stopped.failed :=
        same ▸ view.val.2
      (Cached.resumePair depth left right effectiveLeft effectiveRight request stopped.failed receipt).bind
        fun resumed =>
        match resumed with
        | .error next =>
            let failure := { stopped.reason with reason := .pending stopped.failed next }
            .pure (.pending { stopped with reason := failure })
        | .ok point =>
          let nextLeft := stopped.reason.leftBank
          let nextRight := point.2.val :: stopped.reason.rightBank
          (Independent.Cache.batchWithProgress left right effectiveLeft effectiveRight request nextLeft nextRight
            (Cached.pair depth left right effectiveLeft effectiveRight request nextLeft nextRight) stopped.after).map
              fun returned => match returned with
                | .error later => .later point
                    (Program.CertifiedBatch.Stopped.advance
                      (Independent.Cache.originalChild left right effectiveLeft effectiveRight request)
                      (Independent.Cache.SelectedPair left right effectiveLeft effectiveRight request)
                      (Independent.Cache.returnedChild left right effectiveLeft effectiveRight request)
                      (Independent.Cache.returnedChild_eq left right effectiveLeft effectiveRight request)
                      stopped point later)
                | .ok suffix =>
                    let completed := Program.CertifiedBatch.Stopped.finish
                      (Independent.Cache.originalChild left right effectiveLeft effectiveRight request)
                      (Independent.Cache.SelectedPair left right effectiveLeft effectiveRight request)
                      (Independent.Cache.returnedChild left right effectiveLeft effectiveRight request)
                      (Independent.Cache.returnedChild_eq left right effectiveLeft effectiveRight request)
                      stopped point suffix
                    let common := Independent.Cache.assemble left right effectiveLeft effectiveRight request completed
                    .completed point suffix common rfl
  else .pure (.invalid (.batchIndex stopped.reason.failed stopped.failed matching))

/-- Original replies resume the retained point and complete the untouched original suffix. -/
theorem computation_original (savedLeft : List (NumericalPoint (Points.finiteProcess depth)))
    (savedRight : List (NumericalPoint Horner.Real.source))
    (stopped : Stopped depth left right effectiveLeft effectiveRight request savedLeft savedRight)
    (matching : stopped.reason.failed = stopped.failed)
    (view : Cached.PendingView depth left right effectiveLeft effectiveRight request savedLeft savedRight
      stopped.reason)
    (access : Cached.pendingView depth left right effectiveLeft effectiveRight request savedLeft savedRight
      stopped.reason = .ok view) :
    let receipt := (view.property.1.trans matching) ▸ view.val.2
    let point : Pair depth left right effectiveLeft effectiveRight request stopped.failed :=
      (receipt.leftPoint, ⟨(Independent.Cache.rightPoint left right effectiveRight request stopped.failed).val, rfl⟩)
    let suffix : Program.CertifiedBatch
        (Independent.Cache.originalChild left right effectiveLeft effectiveRight request) stopped.after :=
      ⟨stopped.after.map (Independent.Cache.originalChild left right effectiveLeft effectiveRight request), rfl⟩
    let batch := Program.CertifiedBatch.Stopped.finish
      (Independent.Cache.originalChild left right effectiveLeft effectiveRight request)
      (Independent.Cache.SelectedPair left right effectiveLeft effectiveRight request)
      (Independent.Cache.returnedChild left right effectiveLeft effectiveRight request)
      (Independent.Cache.returnedChild_eq left right effectiveLeft effectiveRight request) stopped point suffix
    let common := Independent.Cache.assemble left right effectiveLeft effectiveRight request batch
    ((computation depth left right effectiveLeft effectiveRight request savedLeft savedRight stopped).protocol.run
      (fun question => some (Points.original depth question))).value = .completed point suffix common rfl := by
  dsimp only
  unfold computation
  rw [dif_pos matching, access, Program.bind_execution, Protocol.bind_run_value, Cached.resumePair_original]
  dsimp only
  rw [Program.map_execution, Protocol.map_run_value]
  unfold Independent.Cache.batchWithProgress
  rw [Program.certifiedBatchProgress_original
    (Independent.Cache.originalChild left right effectiveLeft effectiveRight request)
    (Independent.Cache.SelectedPair left right effectiveLeft effectiveRight request)
    (Independent.Cache.returnedChild left right effectiveLeft effectiveRight request)
    (Independent.Cache.returnedChild_eq left right effectiveLeft effectiveRight request)
    (fun index points failure => Independent.Cache.Failure.prepend left right effectiveLeft effectiveRight request
      stopped.reason.leftBank
      ((Independent.Cache.rightPoint left right effectiveRight request stopped.failed).val :: stopped.reason.rightBank)
      index points failure)
    (Cached.pair depth left right effectiveLeft effectiveRight request stopped.reason.leftBank
      ((Independent.Cache.rightPoint left right effectiveRight request stopped.failed).val :: stopped.reason.rightBank))
    (fun question => some (Points.original depth question))
    (fun index => (⟨(Independent.Cache.leftPoint left right effectiveLeft request index).val, rfl⟩,
      ⟨(Independent.Cache.rightPoint left right effectiveRight request index).val, rfl⟩))
    (Cached.pair_original depth left right effectiveLeft effectiveRight request stopped.reason.leftBank
      ((Independent.Cache.rightPoint left right effectiveRight request stopped.failed).val ::
        stopped.reason.rightBank))]

/-- Every oracle sees exactly one retained-state ball request before the returned suffix is visited. -/
theorem computation_trace (savedLeft : List (NumericalPoint (Points.finiteProcess depth)))
    (savedRight : List (NumericalPoint Horner.Real.source))
    (stopped : Stopped depth left right effectiveLeft effectiveRight request savedLeft savedRight)
    (matching : stopped.reason.failed = stopped.failed)
    (view : Cached.PendingView depth left right effectiveLeft effectiveRight request savedLeft savedRight
      stopped.reason)
    (access : Cached.pendingView depth left right effectiveLeft effectiveRight request savedLeft savedRight
      stopped.reason = .ok view) (oracle : Points.Query → Option (Points.Reply depth)) :
    let receipt := (view.property.1.trans matching) ▸ view.val.2
    let resumed := Cached.resumePair depth left right effectiveLeft effectiveRight request stopped.failed receipt
    ((computation depth left right effectiveLeft effectiveRight request savedLeft savedRight stopped).protocol.run
      oracle).trace =
      ((resumed.protocol.run oracle).trace ++
        (match (resumed.protocol.run oracle).value with
        | .error _ => []
        | .ok point =>
            ((Independent.Cache.batchWithProgress left right effectiveLeft effectiveRight request
              stopped.reason.leftBank (point.2.val :: stopped.reason.rightBank)
              (Cached.pair depth left right effectiveLeft effectiveRight request stopped.reason.leftBank
                (point.2.val :: stopped.reason.rightBank)) stopped.after).protocol.run oracle).trace)) ∧
      ((resumed.protocol.run oracle).trace =
        [⟨.inr (Points.tag depth left right stopped.failed, .ball receipt.next.val),
          oracle (.inr (Points.tag depth left right stopped.failed, .ball receipt.next.val))⟩]) := by
  dsimp only
  constructor
  · unfold computation
    rw [dif_pos matching, access, Program.bind_execution, Protocol.bind_run_trace]
    split
    next failure =>
      rewrite [failure]
      rfl
    next point =>
      rewrite [point, Program.map_execution, Protocol.map_run_trace]
      rfl
  · exact Cached.resumePair_trace depth left right effectiveLeft effectiveRight request stopped.failed _ oracle

/-- Changing replies outside the actual resume trace preserves the returned work and ordered operations. -/
theorem payload_erasure (savedLeft : List (NumericalPoint (Points.finiteProcess depth)))
    (savedRight : List (NumericalPoint Horner.Real.source))
    (stopped : Stopped depth left right effectiveLeft effectiveRight request savedLeft savedRight)
    (oracle : Points.Query → Option (Points.Reply depth)) {Payload : Type} (payload : Payload)
    (outside : Payload → Points.Query → Option (Points.Reply depth)) :
    let program := computation depth left right effectiveLeft effectiveRight request savedLeft savedRight stopped
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run oracle).trace (outside payload)) =
      program.protocol.run oracle :=
  (computation depth left right effectiveLeft effectiveRight request savedLeft savedRight stopped).protocol
    |>.annotation_erasure oracle payload outside

/-- Exact replay preserves the original retry outcome and any later typed failure. -/
theorem replay (savedLeft : List (NumericalPoint (Points.finiteProcess depth)))
    (savedRight : List (NumericalPoint Horner.Real.source))
    (stopped : Stopped depth left right effectiveLeft effectiveRight request savedLeft savedRight)
    (oracle : Points.Query → Option (Points.Reply depth)) :
    let program := computation depth left right effectiveLeft effectiveRight request savedLeft savedRight stopped
    program.protocol.replayExact (program.protocol.run oracle).trace = .ok (program.protocol.run oracle).value :=
  (computation depth left right effectiveLeft effectiveRight request savedLeft savedRight stopped).protocol
    |>.replayExact_run oracle

end Purelib.Integration.Exponential.Program.Source.Observation.Numerical.Points.Resume

end
