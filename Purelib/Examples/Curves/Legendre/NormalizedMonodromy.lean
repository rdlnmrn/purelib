module
import Purelib.Examples.Curves.Legendre.Crossings.UpperZero
import Purelib.Examples.Curves.Legendre.Loops.One
public import Purelib.Examples.Curves.Legendre.PeriodTransport

import Purelib.Examples.Riemann.ExplicitLegendreNormalizedAcquisition
public import Purelib.Curves.Legendre.PeriodMonodromy
import Purelib.Curves.Legendre.Periods.Fibre

public section

/-! Standard-loop monodromy of the corrected periods normalized by the
unconditional curve theorem. -/
namespace Purelib.Examples.Curves.Legendre.NormalizedMonodromy

open Purelib.Curves
open Purelib.Examples

/-- The normalized period owner retained at the common Legendre base frame. -/
@[expose] def base (token : Unit) :
    Legendre.PeriodMonodromy.NormalizedData Curves.Legendre.Crossings.UpperZero.sourceFrame where
  normalized := Riemann.ExplicitLegendreNormalizedAcquisition.normalized token

/-- Normalized monodromy and raw period transport retain exactly the same original fibre data. -/
theorem base_toFibreData (token : Unit) :
    (base token).toFibreData = Curves.Legendre.PeriodTransport.baseFibre token := by
  cases token
  rfl

/-- The normalized monodromy data for the displayed common-base standard Legendre loops. -/
@[expose] def monodromyData (token : Unit) :
    Legendre.PeriodMonodromy.Data Curves.Legendre.Loops.One.standardLoops where
  base := base token

/-- The fraction-free monodromy certificate of the original normalized standard-loop data. -/
@[expose] def fractionFreeCertificate (token : Unit) :
    Legendre.PeriodMonodromy.FractionFreeCertificate (monodromyData token) :=
  Legendre.PeriodMonodromy.certificate (monodromyData token)

end Purelib.Examples.Curves.Legendre.NormalizedMonodromy
