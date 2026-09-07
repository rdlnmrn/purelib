import CCL.Riemann.ExplicitQuarticPreparedData

namespace CCL.Riemann.ExplicitQuarticBranches

open CCL.Riemann.FinitePeriodExamples

private theorem canonicalACycle_eq_rawData :
    (((CCL.Riemann.BranchCutLifts.symplecticBasisOfData
      quarticCurve branchData).cycles.aCycle (0 : Fin 1)).liftedPath 0) =
        rawACycleTarget := by
  change ((branchFamily.symplecticCycles.aCycle (0 : Fin 1)).liftedPath 0) =
    rawACycleTarget
  unfold rawACycleTarget
  unfold branchFamily
  rw [CCL.Riemann.BranchCutLifts.canonicalACycle_liftedPath_ofData]
  rfl

private theorem canonicalBCycle_eq_rawData :
    (((CCL.Riemann.BranchCutLifts.symplecticBasisOfData
      quarticCurve branchData).cycles.bCycle (0 : Fin 1)).liftedPath 0) =
        rawBCycleTarget := by
  change ((branchFamily.symplecticCycles.bCycle (0 : Fin 1)).liftedPath 0) =
    rawBCycleTarget
  unfold rawBCycleTarget
  unfold branchFamily
  rfl

theorem preparedACycle_realizes_basis :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw
      (preparedACycleWitness ()).data
      (((CCL.Riemann.BranchCutLifts.symplecticBasisOfData
        quarticCurve branchData).cycles.aCycle (0 : Fin 1)).liftedPath 0) := by
  rw [canonicalACycle_eq_rawData]
  exact (preparedACycleWitness ()).realizes

theorem preparedBCycle_realizes_basis :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw
      (preparedBCycleWitness ()).data
      (((CCL.Riemann.BranchCutLifts.symplecticBasisOfData
        quarticCurve branchData).cycles.bCycle (0 : Fin 1)).liftedPath 0) := by
  rw [canonicalBCycle_eq_rawData]
  exact (preparedBCycleWitness ()).realizes

end CCL.Riemann.ExplicitQuarticBranches
