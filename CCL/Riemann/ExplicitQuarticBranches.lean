import CCL.Riemann.ExplicitQuarticCycleRealizations

namespace CCL.Riemann.ExplicitQuarticBranches

open CCL.Riemann.FinitePeriodExamples

/-- The complete genus-one schedule using the cached prepared quartic A/B
cycles.  Its generic constructor keeps the large executable seed values
opaque while the schedule is assembled. -/
def periodSchedule (_token : Unit) :
    CCL.Riemann.PreparedRefinementPrograms.StandardSwitchedSymplecticSchedule
      quarticCurve :=
  CCL.Riemann.PreparedRefinementPrograms.StandardSwitchedSymplecticSchedule.ofGenusOnePrepared
    quarticCurve (preparedACycleWitness ()).data
      (preparedBCycleWitness ()).data

/-- The cached quartic schedule realizes the displayed symplectic branch-cut
basis at every finite refinement. -/
theorem periodSchedule_realizes_basis :
    CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization
      quarticCurve
        (CCL.Riemann.PreparedRefinementPrograms.StandardSwitchedSymplecticSchedule.ofGenusOnePrepared
          quarticCurve (preparedACycleWitness ()).data
            (preparedBCycleWitness ()).data).cycles
        (CCL.Riemann.BranchCutLifts.symplecticBasisOfData
          quarticCurve branchData).cycles :=
  CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization.ofGenusOnePrepared
    (preparedACycleWitness ()).data (preparedBCycleWitness ()).data
      preparedACycle_realizes_basis preparedBCycle_realizes_basis

/-- Canonical switched period programs built from the displayed branch and
quadratic-owner boxes. -/
def periodData (_token : Unit) :
    CCL.Riemann.PeriodMatrix.PeriodData quarticCurve :=
  (CCL.Riemann.PreparedRefinementPrograms.StandardSwitchedSymplecticSchedule.ofGenusOnePrepared
    quarticCurve (preparedACycleWitness ()).data
      (preparedBCycleWitness ()).data).periodData

/-- The explicit programs trace the explicit-data symplectic branch-cut
basis at every finite refinement. -/
theorem periodData_realizes_basis :
    CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization
      quarticCurve
        (CCL.Riemann.PreparedRefinementPrograms.StandardSwitchedSymplecticSchedule.ofGenusOnePrepared
          quarticCurve (preparedACycleWitness ()).data
            (preparedBCycleWitness ()).data).periodData.cycles
        (CCL.Riemann.BranchCutLifts.symplecticBasisOfData
          quarticCurve branchData).cycles :=
  CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization.periodDataOfGenusOnePrepared
    (preparedACycleWitness ()).data (preparedBCycleWitness ()).data
      preparedACycle_realizes_basis preparedBCycle_realizes_basis

end CCL.Riemann.ExplicitQuarticBranches
