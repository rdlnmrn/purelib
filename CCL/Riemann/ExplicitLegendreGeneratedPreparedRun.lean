import CCL.Riemann.ExplicitLegendreGeneratedCertificateSemantics

/-!
# Transport-prepared generated Legendre runs

This downstream module turns a symbolic generated run into one sharply
refined source state.  Keeping the constructor out of the per-shard semantics
module means changes to theorem-facing A-period packaging do not invalidate
the generated certificate shards.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedLegendreCertificateData

open CCL.Riemann.PreparedSwitchedRefinements in
/-- A transport-aligned source state together with the small theorem API
needed by concrete generated clients.  The result intentionally hides the
dependent child list and synchronized block refinement behind one generic
constructor boundary. -/
structure GeneratedTransportPreparedRun where
  source : GeneratedCenteredRun
  target : RFAP.ConstructiveFraction.Rational
  targetPositive : 0 < target
  state : DirectSwitchedState
    CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
    CompactCellData.legendreDifferential
  state_start_eq : state.start = source.start
  state_finish_eq : state.finish = source.finish
  switchCount_eq : state.chain.switchCount = source.chain.switchCount
  sourceAllowance_le :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (state.parents.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      ).aggregateAllowance <= target
  sourceScheduleBase_eq :
    state.sourceScheduleBase = target + DirectSwitchedState.scheduleSlack
  literalDifference_le :
    RFAP.ConstructiveGaussian.Gaussian.normSq
      ((state.sourceModel 0).integralSample -
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          source.literalModels).integralSample) <=
      (source.transportParents.length : RFAP.ConstructiveFraction.Rational) *
        GeneratedTransportRefinement.weightedTransportSum target
          source.transportParents

namespace GeneratedCenteredRun

open CCL.Riemann.PreparedSwitchedRefinements

/-- Perform one synchronized direct refinement and immediately package its
transport semantics.  This theorem is elaborated once for a symbolic run;
large generated clients consume only the resulting record fields. -/
def prepareTransport (run : GeneratedCenteredRun)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) : GeneratedTransportPreparedRun := by
  let result :=
    CCL.Riemann.PreparedDirectDyadicRefinements.accurateDirectRefinement
      (run.transportParents.map GeneratedTransportParent.centeredEdge)
      run.transportProper target targetPositive
  let parents := GeneratedTransportRefinement.children target targetPositive
    run.transportParents result.blocks
  have parentsProper :
      CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents :=
    GeneratedTransportRefinement.childrenProper target targetPositive
      run.transportParents result.blocks
  let chain : CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain
      parents (start := run.start) (finish := run.finish) :=
    GeneratedTransportRefinement.switchedChain target targetPositive
      run.transportParents run.transportChain result.blocks
  have allowance :
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (parents.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
        ).aggregateAllowance <= target := by
    dsimp only [parents]
    rw [GeneratedTransportRefinement.childrenAggregateAllowance_eq]
    exact result.modelAllowance_le
  let raw : DirectSwitchedState
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential :=
    { start := run.start
      finish := run.finish
      parents := parents
      proper := parentsProper
      chain := chain
      initialAllowanceBound := fun differential =>
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (((parents.map
            (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
              differential)).map
                CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model))
          ).aggregateAllowance
      initialAllowance_le := fun _ => le_rfl }
  have recastAllowance :
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((raw.parents.map
          (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
            CompactCellData.legendreDifferential)).map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
        ).aggregateAllowance <= target := by
    rw [DirectSwitchedState.recastCenteredEdges_self_aggregateAllowance]
    exact allowance
  let state := raw.withSourceAllowanceBound target recastAllowance
  have initialSample_eq :
      (state.sourceModel 0).integralSample =
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (GeneratedTransportRefinement.comparisonCells target targetPositive
            run.transportParents result.blocks)).integralSample := by
    rw [DirectSwitchedState.sourceModel_integralSample_eq_flatModel]
    change
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (parents.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
        ).integralSample = _
    dsimp only [parents]
    exact GeneratedTransportRefinement.children_integralSample_eq_comparisonCells
      target targetPositive run.transportParents result.blocks
  exact
    { source := run
      target := target
      targetPositive := targetPositive
      state := state
      state_start_eq := rfl
      state_finish_eq := rfl
      switchCount_eq := by
        change chain.switchCount = run.chain.switchCount
        dsimp only [chain]
        exact
          (GeneratedTransportRefinement.switchedChain_switchCount
            target targetPositive run.transportParents run.transportChain
              result.blocks).trans
            run.transportChain_switchCount
      sourceAllowance_le := by
        change
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (parents.map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
            ).aggregateAllowance <= target
        exact allowance
      sourceScheduleBase_eq := by
        unfold DirectSwitchedState.sourceScheduleBase state
          DirectSwitchedState.withSourceAllowanceBound
        simp only [if_pos]
      literalDifference_le := by
        rw [initialSample_eq, ← run.transportLiteralModels_eq]
        exact
          (GeneratedTransportRefinement.literalRefinement target targetPositive
            run.transportParents result.blocks).integral_difference_le.trans
          (GeneratedTransportRefinement.comparisonAggregateAllowance_le target
            targetPositive run.transportParents result.blocks) }

@[simp] theorem prepareTransport_source (run : GeneratedCenteredRun)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    (run.prepareTransport target targetPositive).source = run := rfl

@[simp] theorem prepareTransport_target (run : GeneratedCenteredRun)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    (run.prepareTransport target targetPositive).target = target := rfl

end GeneratedCenteredRun

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
