import CCL.Riemann.ExplicitLegendreGeneratedAPeriodPrepared

/-!
# Sharp generated Legendre A-period

This module materializes the sharp transport refinement and packages the
final generated A-period bounds after the base run and scalar certificates
have been compacted into an imported module.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedLegendreCertificateData
open CCL.Riemann.PreparedSwitchedRefinements

/-- Source state whose cached starting allowance is the requested sharp
target rather than the much coarser generated-parent allowance. -/
def generatedSharpInitialState (token : Unit) : DirectSwitchedState
    CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
    CompactCellData.legendreDifferential :=
  (generatedSharpPreparedRun token).state

private theorem generatedSharpInitialState_closed (token : Unit) :
    (generatedSharpInitialState token).finish =
      (generatedSharpInitialState token).start := by
  calc
    (generatedSharpInitialState token).finish =
        (generatedSharpPreparedRun token).source.finish :=
      (generatedSharpPreparedRun token).state_finish_eq
    _ = (generatedSharpPreparedRun token).source.start := by
      rw [generatedSharpPreparedRun_source]
      exact generatedClosedRun_closed token
    _ = (generatedSharpInitialState token).start :=
      (generatedSharpPreparedRun token).state_start_eq.symm

theorem generatedSharpInitialState_switchCount (token : Unit) :
    (generatedSharpInitialState token).chain.switchCount = 2 := by
  calc
    (generatedSharpInitialState token).chain.switchCount =
        (generatedSharpPreparedRun token).source.chain.switchCount :=
      (generatedSharpPreparedRun token).switchCount_eq
    _ = (generatedClosedRun token).chain.switchCount := by
      rw [generatedSharpPreparedRun_source]
    _ = 2 := (generatedClosedRunParentAllowanceSummary token).switchCount_eq

/-- The sharp schedule base is a small displayed rational: the selected
initial allowance plus the ordinary source-schedule slack. -/
def generatedSharpSourceScheduleBase : RFAP.ConstructiveFraction.Rational :=
  generatedSharpTarget + DirectSwitchedState.scheduleSlack

theorem generatedSharpSourceScheduleBase_positive :
    0 < generatedSharpSourceScheduleBase := by
  unfold generatedSharpSourceScheduleBase
  exact add_pos_of_pos_of_nonneg generatedSharpTarget_positive
    DirectSwitchedState.scheduleSlack_positive.le

theorem generatedSharpInitialState_sourceScheduleBase (token : Unit) :
    (generatedSharpInitialState token).sourceScheduleBase =
      generatedSharpSourceScheduleBase := by
  calc
    (generatedSharpInitialState token).sourceScheduleBase =
        (generatedSharpPreparedRun token).target +
          DirectSwitchedState.scheduleSlack :=
      (generatedSharpPreparedRun token).sourceScheduleBase_eq
    _ = generatedSharpSourceScheduleBase := by
      rw [generatedSharpPreparedRun_target]
      rfl

/-- Exact finite Cauchy scale of the sharply initialized program.  Two
stationary switches contribute the factor three. -/
def generatedSharpSourceErrorScale : RFAP.ConstructiveFraction.Rational :=
  3 * (4 * (3 * generatedSharpSourceScheduleBase))

theorem generatedSharpSourceErrorScale_nonnegative :
    0 <= generatedSharpSourceErrorScale := by
  unfold generatedSharpSourceErrorScale
  exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        generatedSharpSourceScheduleBase_positive.le))

theorem generatedSharpInitialState_sourceIntegral_errorScale (token : Unit) :
    (generatedSharpInitialState token).sourceIntegral.errorScale =
      generatedSharpSourceErrorScale := by
  unfold DirectSwitchedState.sourceIntegral
  simp only [
    CCL.ProgressiveGaussianIntegration.SequentialCompatibleConstantRefinementProgram.toRefinementProgram,
    CCL.ProgressiveGaussianIntegration.SequentialCompatibleConstantRefinementProgram.errorScale,
    DirectSwitchedState.sourceFlatSequentialProgram,
    SwitchedPathChain.switchFactor]
  rw [generatedSharpInitialState_switchCount token,
    generatedSharpInitialState_sourceScheduleBase token]
  rfl

theorem generatedSharpSourceErrorScale_le_quarter :
    generatedSharpSourceErrorScale <=
      (1 / 2 : RFAP.ConstructiveFraction.Rational) ^ 2 := by
  decide +revert

def generatedSharpSchedule (token : Unit) : SourceSwitchedClosedSchedule
    CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
    CompactCellData.legendreDifferential :=
  { initial := generatedSharpInitialState token
    closed := generatedSharpInitialState_closed token }

/-- The sharp generated A-period uses the ordinary source-refinement process
after one transport-aligned initialization. -/
def generatedSharpAPeriodProgram (token : Unit) :
    CCL.Riemann.AlgebraicDifferentials.CertifiedPeriodProgram
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential
      (generatedSharpSchedule token).cycle :=
  (generatedSharpSchedule token).certifiedPeriodProgram

/-- The sharp index-zero sample is close to the externally generated literal
sample, with no parent-allowance or dyadic-depth term. -/
theorem generatedSharpInitial_difference_le (token : Unit) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (((generatedSharpAPeriodProgram token).integral.model 0).integralSample -
        literalSample) <=
      generatedTransportAggregate generatedSharpTarget := by
  change
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (((generatedSharpPreparedRun token).state.sourceModel 0).integralSample -
        literalSample) <= _
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (((generatedSharpPreparedRun token).state.sourceModel 0).integralSample -
          literalSample) =
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (((generatedSharpPreparedRun token).state.sourceModel 0).integralSample -
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (generatedSharpPreparedRun token).source.literalModels
          ).integralSample) := by
      rw [generatedSharpPreparedRun_source,
        generatedClosedRun_literalSample]
    _ <= ((generatedSharpPreparedRun token).source.transportParents.length :
          RFAP.ConstructiveFraction.Rational) *
        GeneratedTransportRefinement.weightedTransportSum
          (generatedSharpPreparedRun token).target
          (generatedSharpPreparedRun token).source.transportParents :=
      (generatedSharpPreparedRun token).literalDifference_le
    _ = generatedTransportAggregate generatedSharpTarget := by
      rw [generatedSharpPreparedRun_source,
        generatedSharpPreparedRun_target,
        generatedClosedRun_transportParentCount,
        generatedClosedRun_weightedTransportSum]
      unfold generatedTransportAggregate
      ring1

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
