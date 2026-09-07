import CCL.Riemann.ExplicitLegendrePreparedData

namespace CCL.Riemann.ExplicitLegendreBranches

private theorem canonicalACycle_eq_rawData :
    (((CCL.Riemann.BranchCutLifts.symplecticBasisOfData
      curve branchData).cycles.aCycle (0 : Fin 1)).liftedPath 0) =
        rawACycleTarget := by
  change ((branchFamily.symplecticCycles.aCycle (0 : Fin 1)).liftedPath 0) =
    rawACycleTarget
  unfold rawACycleTarget
  unfold branchFamily
  rw [CCL.Riemann.BranchCutLifts.canonicalACycle_liftedPath_ofData]
  rfl

private theorem canonicalBCycle_eq_rawData :
    (((CCL.Riemann.BranchCutLifts.symplecticBasisOfData
      curve branchData).cycles.bCycle (0 : Fin 1)).liftedPath 0) =
        rawBCycleTarget := by
  change ((branchFamily.symplecticCycles.bCycle (0 : Fin 1)).liftedPath 0) =
    rawBCycleTarget
  unfold rawBCycleTarget
  unfold branchFamily
  rfl

/-- The cached prepared Legendre A-cycle realizes the displayed basis cycle. -/
theorem preparedACycle_realizes_basis :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw
      (preparedACycleWitness ()).data
      (((CCL.Riemann.BranchCutLifts.symplecticBasisOfData
        curve branchData).cycles.aCycle (0 : Fin 1)).liftedPath 0) := by
  rw [canonicalACycle_eq_rawData]
  exact (preparedACycleWitness ()).realizes

/-- The cached prepared Legendre B-cycle realizes the displayed basis cycle. -/
theorem preparedBCycle_realizes_basis :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw
      (preparedBCycleWitness ()).data
      (((CCL.Riemann.BranchCutLifts.symplecticBasisOfData
        curve branchData).cycles.bCycle (0 : Fin 1)).liftedPath 0) := by
  rw [canonicalBCycle_eq_rawData]
  exact (preparedBCycleWitness ()).realizes

end CCL.Riemann.ExplicitLegendreBranches
