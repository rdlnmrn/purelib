import CCL.Riemann.ExplicitLegendreGeneratedBCertificate
import CCL.Riemann.ExplicitLegendreGeneratedBGeometryCertificate
import CCL.Riemann.ExplicitLegendreGeneratedBCycleProvenance
import CCL.Riemann.ExplicitLegendreGeneratedBPreparedRun

/-!
# Generated Legendre B-period base data

This module joins the two generated moving sheets with the two exact
stationary switches, retains the comparison-selected coefficient centres,
and exposes the resulting closed source-centred refinement program.  All
large numerical work is consumed through generated compact-total
checkpoints.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedLegendreBCertificateData
open CCL.Riemann.PreparedSwitchedRefinements

@[simp] theorem GeneratedCenteredRun.append_positionTrace
    (first second : GeneratedCenteredRun)
    (endpoint : first.finish = second.start) :
    (first.append second endpoint).positionTrace =
      CCL.Riemann.GeneratedCycleProvenance.PositionTrace.append
        first.positionTrace second.positionTrace := rfl

@[simp] theorem GeneratedCenteredRun.appendStationary_positionTrace
    (run : GeneratedCenteredRun)
    (coordinate : RFAP.ConstructiveGaussian.Gaussian) (sheet : Fin 2)
    (endpoint : run.finish =
      ({ coordinate := coordinate, sheet := sheet } :
        CCL.Riemann.LiftedPaths.LiftedPoint 2)) :
    (run.appendStationary coordinate sheet endpoint).positionTrace =
      run.positionTrace := rfl

def generatedRightSwitchCoordinate (token : Unit) : RFAP.ConstructiveGaussian.Gaussian :=
  (geometricCell0135 token).checked.data.finishValue

theorem generatedFirstSheetFinish (token : Unit) :
    (generatedFirstSheetRange token).run.finish =
      ({ coordinate := generatedRightSwitchCoordinate token, sheet := (0 : Fin 2) } :
        CCL.Riemann.LiftedPaths.LiftedPoint 2) := by
  rw [(generatedFirstSheetRange token).finish_eq]
  rfl

def generatedThroughRightSwitchRun (token : Unit) : GeneratedCenteredRun :=
  (generatedFirstSheetRange token).run.appendStationary
    (generatedRightSwitchCoordinate token) (0 : Fin 2)
      (generatedFirstSheetFinish token)

def generatedThroughRightSwitchRunSummary (token : Unit) :
    GeneratedCenteredRunSummary coefficientBits allowanceBits
      (generatedThroughRightSwitchRun token) :=
  (generatedFirstSheetSummaryRange token).summary.appendStationary
    (generatedRightSwitchCoordinate token) (0 : Fin 2)
      (generatedFirstSheetFinish token)

def generatedThroughRightSwitchParentAllowanceSummary (token : Unit) :
    GeneratedParentAllowanceSummary (generatedThroughRightSwitchRun token) :=
  (generatedFirstSheetSummaryRange token).parentAllowance.appendStationary
    (generatedRightSwitchCoordinate token) (0 : Fin 2)
      (generatedFirstSheetFinish token)

theorem generatedRightSwitch_endpoint (token : Unit) :
    (generatedThroughRightSwitchRun token).finish =
      (generatedSecondSheetRange token).run.start := by
  rw [generatedThroughRightSwitchRun,
    GeneratedCenteredRun.appendStationary_finish,
    (generatedSecondSheetRange token).start_eq]
  change CCL.Riemann.LiftedPaths.LiftedPoint.mk
      (generatedRightSwitchCoordinate token)
        (CCL.Riemann.BranchCutLifts.otherSheet (0 : Fin 2)) =
    CCL.Riemann.LiftedPaths.LiftedPoint.mk
      (geometricCell0136 token).checked.data.startValue
        (geometricCell0136 token).sheet
  have coordinate_eq : generatedRightSwitchCoordinate token =
      (geometricCell0136 token).checked.data.startValue := by
    unfold generatedRightSwitchCoordinate
    rw [geometricCell0135_checked, geometricCell0136_checked]
    rfl
  have sheet_eq : CCL.Riemann.BranchCutLifts.otherSheet (0 : Fin 2) =
      (geometricCell0136 token).sheet := by
    unfold CCL.Riemann.BranchCutLifts.otherSheet GeometricCheckedCell.sheet
    rw [geometricCell0136_checked]
    decide +revert
  exact congrArg₂ CCL.Riemann.LiftedPaths.LiftedPoint.mk coordinate_eq sheet_eq

def generatedThroughSecondSheetRun (token : Unit) : GeneratedCenteredRun :=
  (generatedThroughRightSwitchRun token).append
    (generatedSecondSheetRange token).run
    (generatedRightSwitch_endpoint token)

def generatedThroughSecondSheetRunSummary (token : Unit) :
    GeneratedCenteredRunSummary coefficientBits allowanceBits
      (generatedThroughSecondSheetRun token) :=
  (generatedThroughRightSwitchRunSummary token).append
    (generatedSecondSheetSummaryRange token).summary
      (generatedRightSwitch_endpoint token)

def generatedThroughSecondSheetParentAllowanceSummary (token : Unit) :
    GeneratedParentAllowanceSummary (generatedThroughSecondSheetRun token) :=
  (generatedThroughRightSwitchParentAllowanceSummary token).append
    (generatedSecondSheetSummaryRange token).parentAllowance
      (generatedRightSwitch_endpoint token)

def generatedLeftSwitchCoordinate (token : Unit) : RFAP.ConstructiveGaussian.Gaussian :=
  (geometricCell0271 token).checked.data.finishValue

theorem generatedSecondSheetFinish (token : Unit) :
    (generatedThroughSecondSheetRun token).finish =
      ({ coordinate := generatedLeftSwitchCoordinate token, sheet := (1 : Fin 2) } :
        CCL.Riemann.LiftedPaths.LiftedPoint 2) := by
  rw [generatedThroughSecondSheetRun, GeneratedCenteredRun.append_finish,
    (generatedSecondSheetRange token).finish_eq]
  rfl

def generatedClosedRun (token : Unit) : GeneratedCenteredRun :=
  (generatedThroughSecondSheetRun token).appendStationary
    (generatedLeftSwitchCoordinate token) (1 : Fin 2)
      (generatedSecondSheetFinish token)

def generatedClosedRunSummary (token : Unit) :
    GeneratedCenteredRunSummary coefficientBits allowanceBits
      (generatedClosedRun token) :=
  (generatedThroughSecondSheetRunSummary token).appendStationary
    (generatedLeftSwitchCoordinate token) (1 : Fin 2)
      (generatedSecondSheetFinish token)

def generatedClosedRunParentAllowanceRaw (token : Unit) :
    GeneratedParentAllowanceSummary (generatedClosedRun token) :=
  (generatedThroughSecondSheetParentAllowanceSummary token).appendStationary
    (generatedLeftSwitchCoordinate token) (1 : Fin 2)
      (generatedSecondSheetFinish token)

/-- Final numeric checkpoint for the prepared parent allowance.  Its proof
reduces only the two already-rebased sheet summaries. -/
def generatedClosedRunParentAllowanceSummary (token : Unit) :
    GeneratedParentAllowanceSummary (generatedClosedRun token) :=
  (generatedClosedRunParentAllowanceRaw token).rebase generatedParentCount
    2 generatedParentWeightedAllowanceUpper
    (by cases token; decide +revert)
    (by cases token; decide +revert)
    (by cases token; decide +revert)

theorem generatedClosedRun_closed (token : Unit) :
    (generatedClosedRun token).finish = (generatedClosedRun token).start := by
  have start_eq : (generatedClosedRun token).start =
      (generatedFirstSheetRange token).run.start := by
    calc
      (generatedClosedRun token).start =
          (generatedThroughSecondSheetRun token).start :=
        GeneratedCenteredRun.appendStationary_start
          (generatedThroughSecondSheetRun token)
            (generatedLeftSwitchCoordinate token)
            (1 : Fin 2) (generatedSecondSheetFinish token)
      _ = (generatedThroughRightSwitchRun token).start :=
        GeneratedCenteredRun.append_start (generatedThroughRightSwitchRun token)
          (generatedSecondSheetRange token).run
            (generatedRightSwitch_endpoint token)
      _ = (generatedFirstSheetRange token).run.start :=
        GeneratedCenteredRun.appendStationary_start
          (generatedFirstSheetRange token).run
            (generatedRightSwitchCoordinate token)
            (0 : Fin 2) (generatedFirstSheetFinish token)
  calc
    (generatedClosedRun token).finish =
        { coordinate := generatedLeftSwitchCoordinate token,
          sheet := CCL.Riemann.BranchCutLifts.otherSheet (1 : Fin 2) } :=
      GeneratedCenteredRun.appendStationary_finish
        (generatedThroughSecondSheetRun token)
          (generatedLeftSwitchCoordinate token)
          (1 : Fin 2) (generatedSecondSheetFinish token)
    _ = CompactCellData.liftedStart
          (geometricCell0000 token).checked.data
            (geometricCell0000 token).sheet := by
      change CCL.Riemann.LiftedPaths.LiftedPoint.mk
          (generatedLeftSwitchCoordinate token)
            (CCL.Riemann.BranchCutLifts.otherSheet (1 : Fin 2)) =
        CCL.Riemann.LiftedPaths.LiftedPoint.mk
          (geometricCell0000 token).checked.data.startValue
            (geometricCell0000 token).sheet
      have coordinate_eq : generatedLeftSwitchCoordinate token =
          (geometricCell0000 token).checked.data.startValue := by
        unfold generatedLeftSwitchCoordinate
        rw [geometricCell0271_checked, geometricCell0000_checked]
        rfl
      have sheet_eq : CCL.Riemann.BranchCutLifts.otherSheet (1 : Fin 2) =
          (geometricCell0000 token).sheet := by
        unfold CCL.Riemann.BranchCutLifts.otherSheet GeometricCheckedCell.sheet
        rw [geometricCell0000_checked]
        decide +revert
      exact congrArg₂ CCL.Riemann.LiftedPaths.LiftedPoint.mk coordinate_eq sheet_eq
    _ = (generatedFirstSheetRange token).run.start :=
      (generatedFirstSheetRange token).start_eq.symm
    _ = (generatedClosedRun token).start := start_eq.symm

private def generatedRunState (run : GeneratedCenteredRun) :
    DirectSwitchedState
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential where
  start := run.start
  finish := run.finish
  parents := run.parents
  chain := run.chain
  proper := run.proper
  initialAllowanceBound := fun differential =>
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((run.parents.map
        (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
          differential)).map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance
  initialAllowance_le := fun _ => le_rfl

@[simp] private theorem generatedRunState_start (run : GeneratedCenteredRun) :
    (generatedRunState run).start = run.start := rfl

@[simp] private theorem generatedRunState_finish (run : GeneratedCenteredRun) :
    (generatedRunState run).finish = run.finish := rfl

private theorem generatedRunState_switchCount (run : GeneratedCenteredRun) :
    (generatedRunState run).chain.switchCount = run.chain.switchCount := rfl

private theorem withSourceAllowanceBound_start
    {state : DirectSwitchedState
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential}
    {bound : RFAP.ConstructiveFraction.Rational}
    (boundLe :
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((state.parents.map
          (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
            CompactCellData.legendreDifferential)).map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
        bound) :
    (state.withSourceAllowanceBound bound boundLe).start = state.start := rfl

private theorem withSourceAllowanceBound_finish
    {state : DirectSwitchedState
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential}
    {bound : RFAP.ConstructiveFraction.Rational}
    (boundLe :
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((state.parents.map
          (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
            CompactCellData.legendreDifferential)).map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
        bound) :
    (state.withSourceAllowanceBound bound boundLe).finish = state.finish := rfl

private theorem withSourceAllowanceBound_switchCount
    {state : DirectSwitchedState
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential}
    {bound : RFAP.ConstructiveFraction.Rational}
    (boundLe :
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((state.parents.map
          (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
            CompactCellData.legendreDifferential)).map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
        bound) :
    (state.withSourceAllowanceBound bound boundLe).chain.switchCount =
      state.chain.switchCount := rfl

private theorem generatedRunState_sourceFlatModel_zero
    (run : GeneratedCenteredRun) :
    (generatedRunState run).sourceFlatModel 0 =
      CCL.ProgressiveGaussianIntegration.PathModel.mk
        (run.parents.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model) := rfl

theorem generatedClosedRun_parentAggregateAllowance_le (token : Unit) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((generatedClosedRun token).parents.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
      generatedParentAggregateAllowanceUpper := by
  change _ <= generatedParentCount * generatedParentWeightedAllowanceUpper
  exact (generatedClosedRunParentAllowanceSummary token).aggregateAllowance_le

private theorem generatedRunState_sourceAllowance_le (token : Unit) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (((generatedRunState (generatedClosedRun token)).parents.map
        (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
          CompactCellData.legendreDifferential)).map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
      generatedParentAggregateAllowanceUpper := by
  rw [DirectSwitchedState.recastCenteredEdges_self_aggregateAllowance]
  exact generatedClosedRun_parentAggregateAllowance_le token

/-- The generated comparison-selected parents as a closed source-centred
state for the standard differential `dx/y`. -/
def generatedInitialState (token : Unit) : DirectSwitchedState
    CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
    CompactCellData.legendreDifferential :=
  (generatedRunState (generatedClosedRun token)).withSourceAllowanceBound
    generatedParentAggregateAllowanceUpper
      (generatedRunState_sourceAllowance_le token)

private theorem generatedInitialState_sourceFlatModel_zero (token : Unit) :
    (generatedInitialState token).sourceFlatModel 0 =
      CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((generatedClosedRun token).parents.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model) := rfl

private theorem generatedInitialState_closed (token : Unit) :
    (generatedInitialState token).finish = (generatedInitialState token).start := by
  rw [generatedInitialState,
    withSourceAllowanceBound_finish,
    withSourceAllowanceBound_start,
    generatedRunState_finish, generatedRunState_start]
  exact generatedClosedRun_closed token

/-- Closed source-centred schedule generated entirely from the finite
certificate. -/
def generatedSourceSchedule (token : Unit) : SourceSwitchedClosedSchedule
    CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
    CompactCellData.legendreDifferential :=
  { initial := generatedInitialState token
    closed := generatedInitialState_closed token }

theorem generatedClosedRunTotals_checked (token : Unit) :
    (generatedClosedRunSummary token).totals = generatedRowTotals := by
  cases token
  decide +revert

theorem generatedClosedRun_literalSample (token : Unit) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (generatedClosedRun token).literalModels).integralSample = literalSample := by
  rw [(generatedClosedRunSummary token).integralSample_eq,
    generatedClosedRunTotals_checked token]
  rfl

theorem generatedClosedRun_literalAggregateAllowance_le (token : Unit) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (generatedClosedRun token).literalModels).aggregateAllowance <=
        aggregateAllowance := by
  rw [(generatedClosedRunSummary token).aggregateAllowance_eq,
    generatedClosedRunTotals_checked token]
  decide +revert

/-- The exact generated literal comparison is within the displayed movement
radius of the actual comparison-selected parent model. -/
theorem generatedClosedRun_literalDifference_le (token : Unit) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (literalSample -
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((generatedClosedRun token).parents.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).integralSample) <=
      movement ^ 2 := by
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (literalSample -
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            ((generatedClosedRun token).parents.map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).integralSample) =
      RFAP.ConstructiveGaussian.Gaussian.normSq
        ((CCL.ProgressiveGaussianIntegration.PathModel.mk
            (generatedClosedRun token).literalModels).integralSample -
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            ((generatedClosedRun token).parents.map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).integralSample) := by
        rw [generatedClosedRun_literalSample token]
    _ <= (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (generatedClosedRun token).literalModels).aggregateAllowance :=
      (generatedClosedRun token).literalRefinement.integral_difference_le
    _ <= aggregateAllowance :=
      generatedClosedRun_literalAggregateAllowance_le token
    _ <= movement ^ 2 := aggregateAllowance_le_movement_sq

/-- Explicit positive rational lower endpoint for the actual index-zero
source-centred model. -/
theorem generatedClosedRun_parentRealLower (token : Unit) :
    realLower <=
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((generatedClosedRun token).parents.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).integralSample.re := by
  change literalSample.re - movement <= _
  exact
    CCL.Riemann.PreparedSubdivisionModels.real_sub_radius_le_of_normSq_sub_le
      movement_positive.le (generatedClosedRun_literalDifference_le token)

/-- The generated summary records the two stationary sheet switches without
revisiting the moving chain. -/
theorem generatedInitialState_switchCount (token : Unit) :
    (generatedInitialState token).chain.switchCount = 2 := by
  rw [generatedInitialState,
    withSourceAllowanceBound_switchCount,
    generatedRunState_switchCount]
  exact (generatedClosedRunParentAllowanceSummary token).switchCount_eq

/-- Stored schedule base for constant-time generated preflight. -/
def generatedSourceScheduleBase : RFAP.ConstructiveFraction.Rational :=
  generatedParentAggregateAllowanceUpper + DirectSwitchedState.scheduleSlack

theorem generatedSourceScheduleBase_positive :
    0 < generatedSourceScheduleBase := by
  unfold generatedSourceScheduleBase
  exact add_pos_of_nonneg_of_pos
    ((CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance_nonneg _).trans
      (generatedClosedRun_parentAggregateAllowance_le ()))
    DirectSwitchedState.scheduleSlack_positive

theorem generatedInitialState_sourceScheduleBase (token : Unit) :
    (generatedInitialState token).sourceScheduleBase =
      generatedSourceScheduleBase := by
  rfl

/-- Exact generated switched error scale: two switches give factor three. -/
def generatedSourceErrorScale : RFAP.ConstructiveFraction.Rational :=
  3 * (4 * (3 * generatedSourceScheduleBase))

theorem generatedSourceErrorScale_nonnegative :
    0 <= generatedSourceErrorScale :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        generatedSourceScheduleBase_positive.le))

theorem generatedInitialState_sourceIntegral_errorScale (token : Unit) :
    (generatedInitialState token).sourceIntegral.errorScale =
      generatedSourceErrorScale := by
  unfold DirectSwitchedState.sourceIntegral
  simp only [
    CCL.ProgressiveGaussianIntegration.SequentialCompatibleConstantRefinementProgram.toRefinementProgram,
    CCL.ProgressiveGaussianIntegration.SequentialCompatibleConstantRefinementProgram.errorScale,
    DirectSwitchedState.sourceFlatSequentialProgram,
    SwitchedPathChain.switchFactor]
  rw [generatedInitialState_switchCount token,
    generatedInitialState_sourceScheduleBase token]
  rfl

/-- A compact norm bound for the comparison-selected index-zero sample. -/
def generatedInitialSampleNormSqBound : RFAP.ConstructiveFraction.Rational :=
  2 * (movement ^ 2 +
    RFAP.ConstructiveGaussian.Gaussian.normSq literalSample)

theorem generatedInitialSampleNormSqBound_nonnegative :
    0 <= generatedInitialSampleNormSqBound := by
  unfold generatedInitialSampleNormSqBound
  exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg
      (RFAP.ConstructiveFraction.pow_nonneg_direct movement_positive.le 2)
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _))

theorem generatedClosedRun_parentSample_normSq_le (token : Unit) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((generatedClosedRun token).parents.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).integralSample <=
      generatedInitialSampleNormSqBound := by
  let parentSample :=
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((generatedClosedRun token).parents.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).integralSample
  have reverseDifference : parentSample - literalSample =
      -(literalSample - parentSample) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.neg_re,
        RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
  have differenceBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (parentSample - literalSample) <= movement ^ 2 := by
    rw [reverseDifference,
      RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
    exact generatedClosedRun_literalDifference_le token
  have identity : (parentSample - literalSample) + literalSample =
      parentSample := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  change RFAP.ConstructiveGaussian.Gaussian.normSq parentSample <= _
  rw [← identity]
  exact
    (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two
      (parentSample - literalSample) literalSample).trans
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add differenceBound le_rfl) (by decide))

/-- Compact all-sample bound paired with the generated error scale. -/
def generatedSourceCenterBound : RFAP.ConstructiveFraction.Rational :=
  2 * (generatedInitialSampleNormSqBound + generatedSourceErrorScale)

theorem generatedSourceCenterBound_nonnegative :
    0 <= generatedSourceCenterBound := by
  unfold generatedSourceCenterBound
  exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg generatedInitialSampleNormSqBound_nonnegative
      generatedSourceErrorScale_nonnegative)

private theorem normSq_le_two_bounds
    (current initial : RFAP.ConstructiveGaussian.Gaussian)
    {movementBound initialBound : RFAP.ConstructiveFraction.Rational}
    (movement : RFAP.ConstructiveGaussian.Gaussian.normSq
      (current - initial) <= movementBound)
    (initial_bounded : RFAP.ConstructiveGaussian.Gaussian.normSq initial <=
      initialBound) :
    RFAP.ConstructiveGaussian.Gaussian.normSq current <=
      2 * (initialBound + movementBound) := by
  have identity : (current - initial) + initial = current := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  rw [← identity]
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((current - initial) + initial) <=
      2 * (RFAP.ConstructiveGaussian.Gaussian.normSq (current - initial) +
        RFAP.ConstructiveGaussian.Gaussian.normSq initial) :=
      RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _
    _ <= 2 * (movementBound + initialBound) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add movement initial_bounded) (by decide)
    _ = 2 * (initialBound + movementBound) := by ring1

/-- The full generated state is forced only when a finite model is requested,
and is thereafter shared by every model index in the compiled program. -/
def generatedSourceState (token : Unit) : Thunk (DirectSwitchedState
    CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
    CompactCellData.legendreDifferential) :=
  ⟨fun _ => generatedInitialState token⟩

def generatedSourceModel
    (state : Thunk (DirectSwitchedState
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential))
    (index : Nat) :
    CCL.ProgressiveGaussianIntegration.PathModel :=
  state.get.sourceModel index

@[simp] theorem generatedSourceModel_eq (token : Unit) (index : Nat) :
    generatedSourceModel (generatedSourceState token) index =
      (generatedInitialState token).sourceModel index := rfl

theorem generatedSourceModel_sample_bounded (token : Unit) (index : Nat) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (generatedSourceModel (generatedSourceState token) index).integralSample <=
      generatedSourceCenterBound := by
  let original := (generatedInitialState token).sourceIntegral
  let current :=
    (generatedSourceModel (generatedSourceState token) index).integralSample
  let initial :=
    (generatedSourceModel (generatedSourceState token) 0).integralSample
  have movementBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq (current - initial) <=
        generatedSourceErrorScale := by
    calc
      _ <= CCL.FiniteGeometric.quarterRadius original.errorScale 0 := by
        simpa only [current, initial, generatedSourceModel_eq, original,
          DirectSwitchedState.sourceIntegral_model] using
            original.later_close (Nat.zero_le index)
      _ = CCL.FiniteGeometric.quarterRadius
          generatedSourceErrorScale 0 := by
        rw [generatedInitialState_sourceIntegral_errorScale token]
      _ <= generatedSourceErrorScale :=
        CCL.FiniteGeometric.quarterRadius_le_scale
          generatedSourceErrorScale_nonnegative 0
  have initialBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq initial <=
        generatedInitialSampleNormSqBound := by
    dsimp only [initial]
    rw [generatedSourceModel_eq,
      DirectSwitchedState.sourceModel_integralSample_eq_flatModel,
      generatedInitialState_sourceFlatModel_zero]
    exact generatedClosedRun_parentSample_normSq_le token
  change RFAP.ConstructiveGaussian.Gaussian.normSq current <= _
  unfold generatedSourceCenterBound
  exact normSq_le_two_bounds current initial movementBound initialBound

/-- Generated source integral with all scalar preflight cached as small
rational data.  Its model family and estimates are exactly those of the
canonical source-centred construction. -/
def generatedSourceIntegral (token : Unit) :
    CCL.ProgressiveGaussianIntegration.RefinementProgram := by
  let original := (generatedInitialState token).sourceIntegral
  let state := generatedSourceState token
  exact
    { model := generatedSourceModel state
      errorScale := generatedSourceErrorScale
      errorScale_nonneg := generatedSourceErrorScale_nonnegative
      modelAllowance_le := by
        intro index
        simp only [state, generatedSourceModel_eq]
        calc
          _ <= CCL.FiniteGeometric.quarterRadius original.errorScale index :=
            original.modelAllowance_le index
          _ = CCL.FiniteGeometric.quarterRadius
              generatedSourceErrorScale index := by
            rw [generatedInitialState_sourceIntegral_errorScale token]
      later_close := by
        intro earlier later order
        simp only [state, generatedSourceModel_eq]
        calc
          _ <= CCL.FiniteGeometric.quarterRadius original.errorScale earlier :=
            original.later_close order
          _ = CCL.FiniteGeometric.quarterRadius
              generatedSourceErrorScale earlier := by
            rw [generatedInitialState_sourceIntegral_errorScale token]
      centerBound := generatedSourceCenterBound
      centerBound_nonneg := generatedSourceCenterBound_nonnegative
      sample_bounded := by
        intro index
        simpa only [state] using
          generatedSourceModel_sample_bounded token index }

/-- Delayed uniform certificates for the generated model family.  Naming this
function prevents construction of the complete state merely to close over a
certificate field that has not been requested. -/
def generatedSourceCertificates (token : Unit) (index : Nat) :
    CCL.Riemann.AlgebraicDifferentials.UniformPathCertificates
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential
      ((generatedSourceIntegral token).model index).cells
      ((generatedSourceSchedule token).cycle.liftedPath index).path :=
  ((generatedSourceSchedule token).certifiedModel index).certificates

/-- Public certified B-period program whose model state is lazy and whose
preflight projections are generated constant-time cache entries. -/
def generatedBPeriodProgram (token : Unit) :
    CCL.Riemann.AlgebraicDifferentials.CertifiedPeriodProgram
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential
      (generatedSourceSchedule token).cycle where
  integral := generatedSourceIntegral token
  certificates := generatedSourceCertificates token

/-- The headline finite result: the certified generated Legendre B-period
program has a strictly positive real index-zero sample. -/
theorem generatedBPeriodProgram_initialRealLower (token : Unit) :
    realLower <=
      ((generatedBPeriodProgram token).integral.model 0).integralSample.re := by
  calc
    realLower <=
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((generatedClosedRun token).parents.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).integralSample.re :=
      generatedClosedRun_parentRealLower token
    _ = ((generatedInitialState token).sourceFlatModel 0).integralSample.re := by
      rw [generatedInitialState_sourceFlatModel_zero]
    _ = ((generatedInitialState token).sourceModel 0).integralSample.re := by
      rw [DirectSwitchedState.sourceModel_integralSample_eq_flatModel]
    _ = ((generatedBPeriodProgram token).integral.model 0).integralSample.re := by
      rfl

theorem generatedBPeriodProgram_initialReal_positive (token : Unit) :
    0 < ((generatedBPeriodProgram token).integral.model 0).integralSample.re :=
  realLower_positive.trans_le (generatedBPeriodProgram_initialRealLower token)

/-! ## Sharp generated initialization -/

/-- A small displayed accuracy used both for the first semantic refinement
and for transport alignment against the generated coefficient rows. -/
def generatedSharpTarget : RFAP.ConstructiveFraction.Rational :=
  Dyadic.toCoordinate { numerator := 1, bits := 14 }

theorem generatedSharpTarget_positive : 0 < generatedSharpTarget := by
  exact CompactCellData.dyadicUnit_positive 14

theorem generatedSharpTarget_eq : generatedSharpTarget =
    (1 / 16384 : RFAP.ConstructiveFraction.Rational) := by
  unfold generatedSharpTarget Dyadic.toCoordinate Dyadic.toFraction
  rw [RFAP.ConstructiveFraction.ofFraction_eq_div]
  rfl

theorem generatedClosedRun_transportParentCount (token : Unit) :
    (generatedClosedRun token).transportParents.length =
      nonstationaryCellCount := by
  calc
    (generatedClosedRun token).transportParents.length =
        (generatedClosedRun token).parents.length := by
      have equal := congrArg List.length
        (generatedClosedRun token).transportParents_eq
      simpa only [List.length_map] using equal
    _ = generatedParentCount :=
      (generatedClosedRunParentAllowanceSummary token).count_eq
    _ = nonstationaryCellCount := rfl

/-- The cached trace of the actual closed B-period parent list is exactly the
full canonical mesh interval.  The two stationary sheet switches do not add
moving parents, so this composes the two independently checked sheet traces. -/
theorem generatedClosedRun_positionTrace (token : Unit) :
    (generatedClosedRun token).positionTrace =
      CCL.Riemann.GeneratedCycleProvenance.PositionTrace.consecutive
        0 nonstationaryCellCount := by
  rw [generatedClosedRun,
    GeneratedCenteredRun.appendStationary_positionTrace,
    generatedThroughSecondSheetRun,
    GeneratedCenteredRun.append_positionTrace,
    generatedThroughRightSwitchRun,
    GeneratedCenteredRun.appendStationary_positionTrace]
  rw [generatedFirstSheetRange_positionTrace,
    generatedSecondSheetRange_positionTrace]
  simpa only [nonstationaryCellCount, Nat.reduceAdd] using
    CCL.Riemann.GeneratedCycleProvenance.PositionTrace.append_consecutive
      0 136 136

/-- Inspectable data-level provenance for the generated B-period traversal:
the retained parent list contains every canonical generated row from `0`
through `271`, exactly once and in order. -/
theorem generatedClosedRun_positionCoverage (token : Unit) :
    CCL.Riemann.GeneratedCycleProvenance.PositionTrace.Coverage
      GeneratedTransportParent.position
      (generatedClosedRun token).transportParents
      0 nonstationaryCellCount where
  exact := (generatedClosedRun token).positionTrace_eq.symm.trans
    (generatedClosedRun_positionTrace token)

/-- Concrete list form of B-period coverage, derived for the retained data
rather than left as a consequence for callers to reconstruct. -/
theorem generatedClosedRun_positions_eq_range (token : Unit) :
    (generatedClosedRun token).transportParents.map
        GeneratedTransportParent.position =
      List.range' 0 nonstationaryCellCount :=
  (generatedClosedRun_positionCoverage token).positions_eq_range'

theorem generatedClosedRun_movementSqSum (token : Unit) :
    GeneratedTransportRefinement.movementSqSum
        (generatedClosedRun token).transportParents =
      generatedMovementSqSum := by
  rw [(generatedClosedRunSummary token).movementSqSum_eq,
    generatedClosedRunTotals_checked token]
  rfl

theorem generatedClosedRun_transportWeightedErrorSum (token : Unit) :
    GeneratedTransportRefinement.transportWeightedErrorSum
        (generatedClosedRun token).transportParents =
      generatedTransportWeightedErrorSum := by
  rw [(generatedClosedRunSummary token).transportWeightedErrorSum_eq,
    generatedClosedRunTotals_checked token]
  rfl

theorem generatedClosedRun_weightedTransportSum (token : Unit)
    (target : RFAP.ConstructiveFraction.Rational) :
    GeneratedTransportRefinement.weightedTransportSum target
        (generatedClosedRun token).transportParents =
      2 * (10 * target * generatedMovementSqSum +
        generatedTransportWeightedErrorSum) := by
  rw [GeneratedTransportRefinement.weightedTransportSum_eq,
    generatedClosedRun_movementSqSum token,
    generatedClosedRun_transportWeightedErrorSum token]

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
