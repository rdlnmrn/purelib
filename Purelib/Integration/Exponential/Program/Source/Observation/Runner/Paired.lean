module

public import Purelib.Integration.Exponential.Program.Source.Observation.Runner.Full
public import Purelib.Integration.Exponential.Real.Paired
import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Gaussian.Norm.Coordinates
import Purelib.Tactic.Ring

/-!
# Paired samples from the original exponential runner's source replies

Each returned source point retains its original selected finite Taylor owner
and cached exact real reading. That same reading and its proved zero imaginary
coordinate identify the original finite Gaussian sample without another source
request or a second sample computation.
-/

public section

namespace Purelib.Integration.Exponential.Program.Source.Observation.Runner.Paired

open Purelib.Approximation.Gaussian.Exponential
open Purelib.Computation.Query
open Purelib.Data.Gaussian
open Purelib.Data.Nat.Schedule
open Purelib.Data.Rat
open Purelib.Integration.Exponential

/-- The Gaussian value assembled from the original point's already returned exact real reading. -/
@[expose] def sample {source : Fraction.Rational → Fraction.Rational} (point : SourcePoint source) :
    Basic.Canonical := ⟨point.reading, 0⟩

/-- The cached reading and zero imaginary coordinate are the same original finite Horner sample. -/
theorem sample_eq (depth : Nat) (point : SourcePoint (Horner.Real.finiteSource depth)) :
    sample point = Horner.Sample.sample (RationalEmbedding.realPoint point.point) depth := by
  apply Basic.ext
  · exact point.reading_eq
  · exact (Horner.Sample.sample_im_zero _ (RationalEmbedding.realPoint_im point.point) depth).symm

variable {policy rightPolicy : Geometry.Policy} {schedule rightSchedule : PositiveStride} {extraDepth rightExtra : Nat}
variable (input : Full.Input policy rightPolicy schedule rightSchedule extraDepth rightExtra)

/-- One returned point, retaining the actual selected receipt and source owner. -/
abbrev Point := Σ selected : Full.Selected input,
  Sum (SourcePoint (Full.selectedRequest input selected).source) (SourcePoint input.right.source)

/-- Recover an actual source point from one original runner reply, preserving the selected receipt and owner. -/
@[expose] def returnedPoint : Full.Reply input → Option (Point input)
  | .inl _ => none
  | .inr ⟨selected, .fresh (.left point)⟩ => some ⟨selected, .inl point⟩
  | .inr ⟨selected, .fresh (.right point)⟩ => some ⟨selected, .inr point⟩
  | .inr ⟨selected, .fresh (.common (.inl point))⟩ => some ⟨selected, .inl point⟩
  | .inr ⟨selected, .fresh (.common (.inr point))⟩ => some ⟨selected, .inr point⟩
  | .inr ⟨selected, .refine point⟩ => some ⟨selected, .inl point⟩
  | .inr ⟨selected, .common (.inl point)⟩ => some ⟨selected, .inl point⟩
  | .inr ⟨selected, .common (.inr point)⟩ => some ⟨selected, .inr point⟩

/-- The Gaussian sample assembled from that actual source reply and its cached reading. -/
@[expose] def returnedSample : Point input → Basic.Canonical
  | ⟨_, .inl point⟩ => sample point
  | ⟨_, .inr point⟩ => sample point

/-- The retained left reading identifies its actual selected finite Gaussian sample. -/
theorem returnedSample_left (selected : Full.Selected input)
    (point : SourcePoint (Full.selectedRequest input selected).source) :
    returnedSample input ⟨selected, .inl point⟩ =
      Horner.Sample.sample (RationalEmbedding.realPoint point.point)
        (Full.selectedRequest input selected).selection.depth :=
  sample_eq _ point

/-- The retained right reading identifies its own original selected finite Gaussian sample. -/
theorem returnedSample_right (selected : Full.Selected input) (point : SourcePoint input.right.source) :
    returnedSample input ⟨selected, .inr point⟩ = Horner.Sample.sample (RationalEmbedding.realPoint point.point)
      input.right.selection.depth :=
  sample_eq _ point

/-- One returned source point together with the Gaussian sample built from its exact cached reading. -/
abbrev PairedPoint := Σ point : Point input, {value : Basic.Canonical // value = returnedSample input point}

/-- The exact original runner execution, including its ordered model and source replies. -/
abbrev Execution := Basic.Execution (Full.Question input) (Full.Reply input)
  (Except (Full.Failure input) (Full.Result input))

/-- Extract source-point owners directly from the actual original ordered reply trace. -/
@[expose] def returnedPoints (execution : Execution input) : List (Point input) :=
  execution.trace.filterMap fun exchange => returnedPoint input exchange.reply

/-- Pair every actual source reply with its same cached real reading and zero imaginary coordinate. -/
@[expose] def pairedPoints (execution : Execution input) : List (PairedPoint input) :=
  (returnedPoints input execution).map fun point => ⟨point, ⟨returnedSample input point, rfl⟩⟩

/-- Forward one original runner request and retain the exact returned reply. -/
@[expose] def forward (question : Full.Question input) :
    Program (Full.Question input) (Full.Reply input) (Except Empty (Full.Reply input)) :=
  .request question fun reply => .pure (.ok reply)

/-- Observe the original production runner and retain every source point used for its paired samples.

The original execution drives all branch decisions and retains failures. The
paired points are extracted from its actual replies in their original order;
constructing their Gaussian samples performs no additional source requests. -/
@[expose] def computation : Program (Full.Question input) (Full.Reply input)
    (Except Empty (Execution input × List (PairedPoint input))) :=
  ((Full.computation input).substituteChecked (forward input)).map fun result =>
    result.map fun execution => (execution, pairedPoints input execution)

/-- Original execution returns the same complete runner execution and its actual returned source points. -/
theorem computation_original :
    let execution := (Full.computation input).protocol.run (Full.originalReply input)
    ((computation input).protocol.run (Full.originalReply input)).value =
      .ok (execution, pairedPoints input execution) := by
  unfold computation
  rw [Program.map_execution, Protocol.map_run_value]
  have success : ∀ question, ((forward input question).protocol.run (Full.originalReply input)).value =
      .ok (Full.originalReply input question) := by
    intro question
    rfl
  rw [Program.substituteChecked_value (forward input) (Full.computation input)
    (Full.originalReply input) (Full.originalReply input) success]
  rfl

/-- Exact replay retains the complete original runner and its original paired-point occurrences. -/
theorem computation_replay :
    let execution := (Full.computation input).protocol.run (Full.originalReply input)
    (computation input).protocol.replayExact ((computation input).protocol.run (Full.originalReply input)).trace =
      .ok (.ok (execution, pairedPoints input execution)) := by
  rw [(computation input).protocol.replayExact_run, computation_original]

/-- Changes outside the actual original runner requests preserve the complete result and trace. -/
theorem computation_payload_erasure {Payload : Type} (payload : Payload)
    (outside : Payload → Full.Question input → Full.Reply input) :
    let program := computation input
    program.protocol.run
      (Boundary.Trace.overlay (program.protocol.run (Full.originalReply input)).trace (outside payload)) =
      program.protocol.run (Full.originalReply input) :=
  (computation input).protocol.annotation_erasure (Full.originalReply input) payload outside

/-- The retained selected Gaussian samples satisfy the actual common-point squared-norm bound. -/
theorem selected_normSq_le_actual (result : Full.Result input) :
    Norm.Basic.normSq (result.recorded.observation.selected.sample - input.right.stage.sample) ≤
      ((integralBound result.comparison.left.cells).width +
        (integralBound result.comparison.rightFrontier.cells).width +
          result.comparison.common.val.pointBudget) ^ 2 := by
  have sameModel : result.comparison.leftAnchor.stage = result.selected.val.model :=
    result.comparison.leftModel.trans (congrArg (fun receipt => receipt.model) result.comparison_receipt)
  have same : result.recorded.observation.selected.sample = result.comparison.leftAnchor.stage.sample :=
    (Runner.selected_sample result.recorded).trans
      ((congrArg (fun model => model.sample) result.selected_model.symm).trans
        (congrArg (fun model => model.sample) sameModel.symm))
  have leftZero : result.recorded.observation.selected.sample.im = 0 :=
    (congrArg (fun value : Basic.Canonical => value.im) same).trans result.comparison.leftAnchor.sample_im_zero
  have rightZero : input.right.stage.sample.im = 0 :=
    (congrArg (fun model => model.sample.im) result.comparison.rightModel.symm).trans
      result.comparison.rightAnchor.sample_im_zero
  have square := Norm.Coordinates.square_le_of_abs_le (Full.Result.selected_difference_le_actual input result)
  have normEq : Norm.Basic.normSq (result.recorded.observation.selected.sample - input.right.stage.sample) =
      (result.recorded.observation.selected.sample.re - input.right.stage.sample.re) ^ 2 := by
    rw [Norm.Basic.normSq, Basic.sub_re, Basic.sub_im, leftZero, rightZero]
    ring1
  rw [normEq]
  exact square

/-- A returned selected-stage sample is quantitatively compared with an actual paired numerical point.

The supplied tag equality relates the original source-point occurrence to the
original numerical point. The bound retains that point's real and imaginary
widths and the selected receipt's actual finite-depth tail radius. -/
theorem selectedSample_numerical_midpoint_normSq_le (selected : Full.Selected input)
    (sourcePoint : SourcePoint (Full.selectedRequest input selected).source)
    (numericalPoint : NumericalPoint Horner.Real.source)
    (unit : 0 ≤ numericalPoint.point ∧ numericalPoint.point ≤ 1)
    (paired : Real.Paired.PointState numericalPoint unit) (same : sourcePoint.point = numericalPoint.point) :
    Norm.Basic.normSq (returnedSample input ⟨selected, .inl sourcePoint⟩ - paired.paired.midpoint) ≤
      (paired.paired.real.interval.width +
        Horner.Real.tailRadius (Full.selectedRequest input selected).selection.depth) ^ 2 +
        (paired.paired.imaginary.interval.width * (1 / 2)) ^ 2 := by
  let depth := (Full.selectedRequest input selected).selection.depth
  have actual : returnedSample input ⟨selected, .inl sourcePoint⟩ =
      Horner.Sample.sample (RationalEmbedding.realPoint numericalPoint.point) depth :=
    (returnedSample_left input selected sourcePoint).trans
      (congrArg (fun point => Horner.Sample.sample (RationalEmbedding.realPoint point) depth) same)
  rw [actual]
  exact Real.Paired.finiteSample_midpoint_normSq_le numericalPoint unit paired depth

/-- A returned independent-stage sample is quantitatively compared with an actual paired numerical point.

The supplied tag equality relates the independent source owner to the actual
numerical point. Its selected finite depth and both coordinate widths remain
explicit in the resulting squared-norm bound. -/
theorem rightSample_numerical_midpoint_normSq_le (selected : Full.Selected input)
    (sourcePoint : SourcePoint input.right.source) (numericalPoint : NumericalPoint Horner.Real.source)
    (unit : 0 ≤ numericalPoint.point ∧ numericalPoint.point ≤ 1)
    (paired : Real.Paired.PointState numericalPoint unit) (same : sourcePoint.point = numericalPoint.point) :
    Norm.Basic.normSq (returnedSample input ⟨selected, .inr sourcePoint⟩ - paired.paired.midpoint) ≤
      (paired.paired.real.interval.width + Horner.Real.tailRadius input.right.selection.depth) ^ 2 +
        (paired.paired.imaginary.interval.width * (1 / 2)) ^ 2 := by
  let depth := input.right.selection.depth
  have actual : returnedSample input ⟨selected, .inr sourcePoint⟩ =
      Horner.Sample.sample (RationalEmbedding.realPoint numericalPoint.point) depth :=
    (returnedSample_right input selected sourcePoint).trans
      (congrArg (fun point => Horner.Sample.sample (RationalEmbedding.realPoint point) depth) same)
  rw [actual]
  exact Real.Paired.finiteSample_midpoint_normSq_le numericalPoint unit paired depth

end Purelib.Integration.Exponential.Program.Source.Observation.Runner.Paired

end
