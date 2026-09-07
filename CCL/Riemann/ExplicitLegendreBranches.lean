import CCL.Riemann.ExplicitLegendreCycleRealizations

namespace CCL.Riemann.ExplicitLegendreBranches

/-- The complete genus-one schedule using the cached prepared Legendre A/B
cycles. -/
def periodSchedule (_token : Unit) :
    CCL.Riemann.PreparedRefinementPrograms.StandardSwitchedSymplecticSchedule
      curve :=
  CCL.Riemann.PreparedRefinementPrograms.StandardSwitchedSymplecticSchedule.ofGenusOnePrepared
    curve (preparedACycleWitness ()).data (preparedBCycleWitness ()).data

/-- The cached Legendre schedule realizes the displayed symplectic branch-cut
basis at every finite refinement. -/
theorem periodSchedule_realizes_basis :
    CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization
      curve
        (CCL.Riemann.PreparedRefinementPrograms.StandardSwitchedSymplecticSchedule.ofGenusOnePrepared
          curve (preparedACycleWitness ()).data
            (preparedBCycleWitness ()).data).cycles
        (CCL.Riemann.BranchCutLifts.symplecticBasisOfData
          curve branchData).cycles :=
  CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization.ofGenusOnePrepared
    (preparedACycleWitness ()).data (preparedBCycleWitness ()).data
      preparedACycle_realizes_basis preparedBCycle_realizes_basis

/-- Canonical switched period programs built from the displayed Legendre
branch and quadratic-owner boxes. -/
def periodData (_token : Unit) : CCL.Riemann.PeriodMatrix.PeriodData curve :=
  (CCL.Riemann.PreparedRefinementPrograms.StandardSwitchedSymplecticSchedule.ofGenusOnePrepared
    curve (preparedACycleWitness ()).data
      (preparedBCycleWitness ()).data).periodData

/-- The explicit Legendre programs trace their displayed symplectic
branch-cut basis at every finite refinement. -/
theorem periodData_realizes_basis :
    CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization
      curve
        (CCL.Riemann.PreparedRefinementPrograms.StandardSwitchedSymplecticSchedule.ofGenusOnePrepared
          curve (preparedACycleWitness ()).data
            (preparedBCycleWitness ()).data).periodData.cycles
        (CCL.Riemann.BranchCutLifts.symplecticBasisOfData
          curve branchData).cycles :=
  CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization.periodDataOfGenusOnePrepared
    (preparedACycleWitness ()).data (preparedBCycleWitness ()).data
      preparedACycle_realizes_basis preparedBCycle_realizes_basis

end CCL.Riemann.ExplicitLegendreBranches
