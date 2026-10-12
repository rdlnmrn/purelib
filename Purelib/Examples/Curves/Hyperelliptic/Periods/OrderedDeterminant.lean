module
import Purelib.Data.Rat.Fraction

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
public import Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveOrderedDeterminantRequest
public import Purelib.Riemann.Periods.PeriodCurves
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-! Nonvacuous strict-upper requests on the concrete odd- and even-degree
genus-two curves. These constructors need no caller analytic certificate. -/
namespace Purelib.Examples.Curves.Hyperelliptic.Periods.OrderedDeterminant

open Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveOrderedDeterminantRequest.PairedPeriodBank (OrderedRequest)
open Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveOrderedDeterminantRequest

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Periods.Normalization.CurveOrderedDeterminantRequest.ClearGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank (PairedPeriodBank)
open Purelib.Riemann.Periods.PeriodCurves

open Purelib.Curves.Hyperelliptic
open Purelib.Data.Rat
open Purelib.Riemann.Periods
/-- An ordered determinant request for the displayed quintic's original paired period bank.

Retains differential indices zero and one, the positive rational error target and the requested minimum numerical index.
-/
def quinticOrderedDeterminantRequest (error : Fraction.Rational) (positive : 0 < error) (minimum : Nat) :
    OrderedRequest
      (PairedPeriodBank.ofCurve PeriodCurves.quinticCurve) (0 : Fin 2) (1 : Fin
        2) error minimum :=
  ClearGrid.curveOrderedDeterminantRequest
    PeriodCurves.quinticCurve 0 1 error positive minimum

/-- An ordered determinant request for the displayed sextic's original paired period bank.

Retains differential indices zero and one, the positive rational error target and the requested minimum numerical index.
-/
def sexticOrderedDeterminantRequest (error : Fraction.Rational) (positive : 0 < error) (minimum : Nat) :
    OrderedRequest
      (PairedPeriodBank.ofCurve PeriodCurves.sexticCurve) (0 : Fin 2) (1 : Fin 2)
        error minimum :=
  ClearGrid.curveOrderedDeterminantRequest PeriodCurves.sexticCurve
    0 1 error positive minimum

end Purelib.Examples.Curves.Hyperelliptic.Periods.OrderedDeterminant
