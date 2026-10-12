module
public import Purelib.Riemann.Periods.PeriodCurves
public import Purelib.Curves.Hyperelliptic.Integration.Surface.Energy
public import Purelib.Riemann.Periods.PeriodTheorem

@[expose] public section

namespace Purelib.Examples.Curves.Hyperelliptic.Quartic.Branches

open Purelib.Riemann

open Purelib.Riemann.Periods.PeriodCurves

/-- The unconditional curve theorem uses the corrected automatic standard bank. -/
def periodTheorem (_token : Unit) :
    Periods.PeriodTheorem.Result quarticCurve :=
  Periods.PeriodTheorem.riemann_period_theorem Periods.PeriodCurves.quarticCurve

end Purelib.Examples.Curves.Hyperelliptic.Quartic.Branches
