module
import Purelib.Data.Rat.Fraction
public import Purelib.Examples.Curves.Legendre.LoopBaseBranches

public import Purelib.Riemann.Periods.PeriodTheorem
import Purelib.Curves.Hyperelliptic.Periods.PreparedNormalization
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Periods.PeriodMatrix

@[expose] public section

/-! Unconditional normalization of the corrected standard Legendre periods.
The curve theorem computes the inverse tail and positive energy requests;
no caller scan or fixture A-period certificate is needed. -/
namespace Purelib.Examples.Riemann.ExplicitLegendreNormalizedAcquisition

open Purelib.Data.Rat
open Purelib.Examples

open Purelib.Examples.Curves.Legendre

open Purelib.Riemann.Periods.PeriodMatrix (NormalizedPeriodData)
open Purelib.Riemann.Periods.PeriodTheorem (Result riemann_period_theorem)
/-- The displayed rational coordinate type. -/
abbrev Coordinate := Fraction.Rational

/-- The retained Riemann period-theorem result for the original base Legendre curve.

The unit argument delays the finite construction until requested. -/
def periodTheorem (_token : Unit) :
    Result LoopBaseBranches.baseCurve :=
  riemann_period_theorem LoopBaseBranches.baseCurve

/-- The normalized period data projected from the retained curve theorem. -/
def normalized (token : Unit) :
    NormalizedPeriodData LoopBaseBranches.baseCurve :=
  (periodTheorem token).normalized

/-- The sole normalized period ratio projected from an already retained curve theorem. -/
def ratio (result : Result LoopBaseBranches.baseCurve) := result.normalization.omega 0 0

/-- Prepare the genus-one normalized ratio once from the retained theorem result.

The result supplies its center, squared radius and strict accuracy directly from
one cached ball, retaining the theorem's actual inverse and shared factors. -/
def prepareRatio (result : Result LoopBaseBranches.baseCurve)
    (target : Coordinate) (positive : 0 < target) :=
  result.normalization.prepareEntry target positive 0 0

end Purelib.Examples.Riemann.ExplicitLegendreNormalizedAcquisition
