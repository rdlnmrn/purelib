module
public import Purelib.Examples.Curves.Legendre.Prepared.RealMinusOne

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Riemann.Periods.PeriodTheorem
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Examples.Curves.Legendre.CycleRealizations

public section

namespace Purelib.Examples.Curves.Legendre.Branches

open Purelib.Curves
open Purelib.Examples
open Purelib.Riemann

open Purelib.Examples.Curves.Legendre.Prepared

open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank.PreparedCycleModels (RootClosedPeriodBank)

open Purelib.Examples.Curves.Legendre.Prepared.RealMinusOne (curve branchData)

/-- The retained root-closed standard period bank for the displayed Legendre branch owners. -/
@[expose] def periodSchedule (_token : Unit) :
    RootClosedPeriodBank curve :=
  RootClosedPeriodBank.ofData
    RealMinusOne.curve RealMinusOne.branchData

/-- The root-closed schedule realizes the raw standard symplectic branch-cut tours. -/
theorem periodSchedule_realizes_basis :
    Integration.PreparedRefinementPrograms.SymplecticCycleRealization
      RealMinusOne.curve (periodSchedule ()).cycles
      (Hyperelliptic.Branches.BranchCutLifts.symplecticBasisOfData RealMinusOne.curve
        RealMinusOne.branchData).cycles :=
  Integration.PreparedRefinementPrograms.SymplecticCycleRealization.ofData
    RealMinusOne.curve RealMinusOne.branchData

/-- The standard period data projected from the retained root-closed schedule. -/
@[expose] def periodData (_token : Unit) : Periods.PeriodMatrix.PeriodData curve :=
  (periodSchedule ()).periodData

/-- The retained standard period data realizes the original symplectic branch-cut basis. -/
theorem periodData_realizes_basis :
    Integration.PreparedRefinementPrograms.SymplecticCycleRealization
      RealMinusOne.curve (periodData ()).cycles
      (Hyperelliptic.Branches.BranchCutLifts.symplecticBasisOfData RealMinusOne.curve
        RealMinusOne.branchData).cycles :=
  periodSchedule_realizes_basis

/-- The unconditional period-theorem result for the displayed squarefree Legendre curve. -/
@[expose] def periodTheorem (_token : Unit) :
    Periods.PeriodTheorem.Result curve :=
  Periods.PeriodTheorem.riemann_period_theorem RealMinusOne.curve

end Purelib.Examples.Curves.Legendre.Branches
