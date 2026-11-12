module
public import Purelib.Integration.Exponential.Program
public import Purelib.Approximation.Gaussian.Exponential.Horner.Real
public import Purelib.Integration.Polynomial.Gaussian.Continuous
public import Purelib.Integration.Cell.Source.Continuous.Comparison
public import Purelib.Integration.Cell.Source.Continuous.Producer
import Purelib.Approximation.Gaussian.Exponential.Taylor.Integral
import Purelib.Data.Gaussian.Field
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Source-linked enclosures for original exponential program stages

The original cached program and stage retain their policy, schedule, model,
selected depth and actual sample. The same finite Taylor depth supplies a
rational source frontier whose integral enclosure contains that sample.
-/

public section

namespace Purelib.Integration.Exponential.Program.Source

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Data.Gaussian
open Purelib.Data.Nat.Schedule
open Purelib.Data.Rat
open Purelib.Integration.Exponential
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Program.Gaussian.Cached

set_option genInjectivity false in
/-- An original cached exponential stage and the source enclosure for its selected finite Taylor depth.

The original policy, schedule, stage index and accuracy request remain
indexed owners. The program and stage retain the exact original cached
objects, and the computed frontier admits that same stage's sample. -/
structure Result (policy : Geometry.Policy) (schedule : PositiveStride) (extraDepth index : Nat)
    (request : AccuracyRequest) where
  /-- The original policy-controlled cached program. -/ program : Basic.CachedProgram
  /-- The cached program is the original policy, schedule and observation-depth construction. -/ program_eq :
    program = Program.program policy schedule extraDepth
  /-- The actual original cached model and sample at the supplied stage. -/ stage : Basic.CachedModel
  /-- The cached stage is read from that same retained program. -/ stage_eq : stage = program.stage index
  /-- The source-linked result for the original selected Taylor depth and request. -/ sourceResult :
    SourceFrontier.Continuous.Result (Horner.Real.finiteModulus (Selection.selection policy schedule index).depth)
  /-- The source result retains the supplied accuracy request. -/ request_eq :
    sourceResult.preparation.request = request
  /-- The original cached stage sample's real coordinate belongs to its actual source enclosure. -/ sample_inside :
    (integralBound sourceResult.frontier.cells).Contains stage.sample.re

constructive_injectivity Result

namespace Result

/-- Stage-source results with the same original program, stage and source result are equal. -/
theorem ext {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth index : Nat}
    {request : AccuracyRequest} (left right : Result policy schedule extraDepth index request)
    (program_eq : left.program = right.program) (stage_eq : left.stage = right.stage)
    (source_eq : left.sourceResult = right.sourceResult) : left = right := by
  cases left with
  | mk leftProgram leftProgramEq leftStage leftStageEq leftSource leftRequest leftInside =>
    cases right with
    | mk rightProgram rightProgramEq rightStage rightStageEq rightSource rightRequest rightInside =>
      cases program_eq
      cases stage_eq
      cases source_eq
      rfl

/-- The actual original exponential-stage sample has zero imaginary coordinate. -/
theorem sample_im_zero {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth index : Nat}
    {request : AccuracyRequest} (result : Result policy schedule extraDepth index request) :
    result.stage.sample.im = 0 := by
  rw [result.stage_eq, result.program_eq]
  change ((Program.program policy schedule extraDepth).approximation.sample index).im = 0
  rw [Program.program_sample, Basic.sub_im, Taylor.Integral.sample_one_im_zero, Basic.one_im]
  rfl

end Result

/-- Build the source-linked enclosure using the exact original cached program stage and selected depth. -/
@[expose] def build (policy : Geometry.Policy) (schedule : PositiveStride) (extraDepth index : Nat)
    (request : AccuracyRequest) : Result policy schedule extraDepth index request := by
  let original := Program.program policy schedule extraDepth
  let stage := original.stage index
  let depth := (Selection.selection policy schedule index).depth
  let polynomial := Taylor.Integral.polynomial depth
  let result := SourceFrontier.Continuous.build (Horner.Real.finiteModulus depth) request
  have same : ∀ point, 0 ≤ point → point ≤ 1 →
      Horner.Real.finiteSource depth point = Continuous.source polynomial point := by
    intro point _ _
    exact (congrArg Basic.Canonical.re
      (Taylor.Integral.eval_polynomial depth (RationalEmbedding.realPoint point))).symm
  have inside := Continuous.model_sample_contains_of_eq polynomial result.frontier same
  have sample : (Continuous.model polynomial).integralSample = stage.sample := by
    change (Continuous.model polynomial).integralSample = original.approximation.sample index
    rw [show original = Program.program policy schedule extraDepth from rfl, Program.program_sample]
    rw [Continuous.model, Cell.Basic.CellModel.exact_integralSample]
    have displacement : (1 : Basic.Canonical) - 0 = 1 := by rw [Basic.sub_zero]
    rw [displacement, Basic.one_mul, Taylor.Integral.integral_polynomial]
  rw [sample] at inside
  exact ⟨original, rfl, stage, rfl, result, rfl, inside⟩

namespace Result

/-- Any source frontier at the retained Taylor depth contains the original stage's real sample.

The frontier may come from another request or a saved continuation. It uses
the same selected finite Taylor source and the original cached stage. -/
theorem sample_contains {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth index : Nat}
    {request : AccuracyRequest} (result : Result policy schedule extraDepth index request)
    (frontier : SourceFrontier (Horner.Real.finiteSource (Selection.selection policy schedule index).depth)) :
    (integralBound frontier.cells).Contains result.stage.sample.re := by
  let depth := (Selection.selection policy schedule index).depth
  let polynomial := Taylor.Integral.polynomial depth
  have same : ∀ point, 0 ≤ point → point ≤ 1 →
      Horner.Real.finiteSource depth point = Continuous.source polynomial point := by
    intro point _ _
    exact (congrArg Basic.Canonical.re
      (Taylor.Integral.eval_polynomial depth (RationalEmbedding.realPoint point))).symm
  have inside := Continuous.model_sample_contains_of_eq polynomial frontier same
  have sample : (Continuous.model polynomial).integralSample = result.stage.sample := by
    rw [result.stage_eq, result.program_eq]
    change (Continuous.model polynomial).integralSample =
      (Program.program policy schedule extraDepth).approximation.sample index
    rw [Program.program_sample, Continuous.model, Cell.Basic.CellModel.exact_integralSample]
    have displacement : (1 : Basic.Canonical) - 0 = 1 := by rw [Basic.sub_zero]
    rw [displacement, Basic.one_mul, Taylor.Integral.integral_polynomial]
  rw [sample] at inside
  exact inside

/-- Continue a saved frontier for the original stage, reusing its previous and supplied source readings.

The original stage remains with the caller. A sufficient frontier is returned
unchanged; otherwise the existing continuous producer constructs and intersects
a new frontier using the retained point bank. -/
@[expose] def advanceFrontier {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth index : Nat}
    {oldRequest : AccuracyRequest} (_result : Result policy schedule extraDepth index oldRequest)
    (previous : SourceFrontier (Horner.Real.finiteSource (Selection.selection policy schedule index).depth))
    (cached : List (SourcePoint (Horner.Real.finiteSource (Selection.selection policy schedule index).depth)))
    (request : AccuracyRequest) :
    SourceFrontier.Producer.Continuation
      (SourceFrontier.Continuous.producer (Horner.Real.finiteModulus (Selection.selection policy schedule index).depth))
      previous :=
  (SourceFrontier.Continuous.producer
    (Horner.Real.finiteModulus (Selection.selection policy schedule index).depth)).advanceCached
      cached previous request

/-- An adequate saved frontier is returned without a fresh source request. -/
theorem advanceFrontier_reused {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth index : Nat}
    {oldRequest : AccuracyRequest} (result : Result policy schedule extraDepth index oldRequest)
    (previous : SourceFrontier (Horner.Real.finiteSource (Selection.selection policy schedule index).depth))
    (cached : List (SourcePoint (Horner.Real.finiteSource (Selection.selection policy schedule index).depth)))
    (request : AccuracyRequest) (adequate : (integralBound previous.cells).width < request.tolerance) :
    result.advanceFrontier previous cached request = .reused request adequate := by
  unfold advanceFrontier SourceFrontier.Producer.advanceCached SourceFrontier.Producer.advanceWithBank
  rw [dif_pos adequate]

/-- A refinement retains the supplied original bank for the cached producer request. -/
theorem advanceFrontier_cached {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth index : Nat}
    {oldRequest : AccuracyRequest} (result : Result policy schedule extraDepth index oldRequest)
    (previous : SourceFrontier (Horner.Real.finiteSource (Selection.selection policy schedule index).depth))
    (cached : List (SourcePoint (Horner.Real.finiteSource (Selection.selection policy schedule index).depth)))
    (request : AccuracyRequest) (insufficient : ¬ (integralBound previous.cells).width < request.tolerance) :
    match result.advanceFrontier previous cached request with
    | .reused _ _ => False
    | .refined _ retained _ _ _ _ => retained = cached := by
  unfold advanceFrontier SourceFrontier.Producer.advanceCached SourceFrontier.Producer.advanceWithBank
  rw [dif_neg insufficient]

/-- The continuation retains the exact new integration request. -/
theorem advanceFrontier_request {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth index : Nat}
    {oldRequest : AccuracyRequest} (result : Result policy schedule extraDepth index oldRequest)
    (previous : SourceFrontier (Horner.Real.finiteSource (Selection.selection policy schedule index).depth))
    (cached : List (SourcePoint (Horner.Real.finiteSource (Selection.selection policy schedule index).depth)))
    (request : AccuracyRequest) : (result.advanceFrontier previous cached request).request = request :=
  SourceFrontier.Producer.advanceCached_request _ _ _ _

/-- Every actual continued frontier still contains the same original stage sample. -/
theorem advanceFrontier_sample_contains {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth index : Nat}
    {oldRequest : AccuracyRequest} (result : Result policy schedule extraDepth index oldRequest)
    (previous : SourceFrontier (Horner.Real.finiteSource (Selection.selection policy schedule index).depth))
    (cached : List (SourcePoint (Horner.Real.finiteSource (Selection.selection policy schedule index).depth)))
    (request : AccuracyRequest) :
    (integralBound (result.advanceFrontier previous cached request).frontier.cells).Contains result.stage.sample.re :=
  result.sample_contains _

end Result

/-- The comparison retains both original program stages and their actual common point-reading budget. -/
@[expose] def common {leftPolicy rightPolicy : Geometry.Policy} {leftSchedule rightSchedule : PositiveStride}
    {leftExtra rightExtra leftIndex rightIndex : Nat} {leftRequest rightRequest : AccuracyRequest}
    (left : Result leftPolicy leftSchedule leftExtra leftIndex leftRequest)
    (right : Result rightPolicy rightSchedule rightExtra rightIndex rightRequest) :=
  SourceFrontier.commonReadings left.sourceResult.frontier right.sourceResult.frontier

/-- The original policy-selected stage samples differ by their source widths and actual common-tag discrepancy.

Both original program owners, cached models and sample readings are retained.
The additional point budget is computed from their actual finite Taylor
readings on the common partition, rather than supplied as an equality. -/
theorem samples_difference_le {leftPolicy rightPolicy : Geometry.Policy} {leftSchedule rightSchedule : PositiveStride}
    {leftExtra rightExtra leftIndex rightIndex : Nat} {leftRequest rightRequest : AccuracyRequest}
    (left : Result leftPolicy leftSchedule leftExtra leftIndex leftRequest)
    (right : Result rightPolicy rightSchedule rightExtra rightIndex rightRequest) :
    Fraction.abs (left.stage.sample.re - right.stage.sample.re) ≤
      (integralBound left.sourceResult.frontier.cells).width + (integralBound right.sourceResult.frontier.cells).width +
        (common left right).pointBudget :=
  (common left right).answers_difference_le left.stage.sample.re right.stage.sample.re
    left.sample_inside right.sample_inside

end Purelib.Integration.Exponential.Program.Source

end
