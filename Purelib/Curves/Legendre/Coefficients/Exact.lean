module
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Name.Coherent.State.Exact
public import Purelib.Curves.Legendre.Paths
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Coherent.State
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib

open Purelib.Approximation.Gaussian.Name.Coherent.State.Exact

open Purelib.Curves.Legendre

open Purelib.Data.Rat

open Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table

section
@[expose] public section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

namespace Purelib.Curves.Legendre.Coefficients.Exact

/-- The three lower coefficients of the monic Legendre cubic, in descending order. -/
def coefficientValues (lambda : Data.Gaussian.Basic.Canonical) : List
  Data.Gaussian.Basic.Canonical :=
  [-(1 + lambda), lambda, 0]

/-- Retain exact coefficient states for the displayed Legendre cubic at the chosen parameter. -/
def coefficientTable (lambda : Data.Gaussian.Basic.Canonical) :
  ExplicitLegendreSegment.CoefficientTable where
  entries := coefficientValues lambda |>.map
    ExplicitLegendreFrame.exactCoefficientState

/-- The exact retained Legendre coefficient table has degree three. -/
@[simp] theorem coefficientTable_degree (lambda :
  Data.Gaussian.Basic.Canonical) :
    (coefficientTable lambda).degree = 3 := rfl

/-- The retained coefficient table reads back to the exact displayed Legendre polynomial. -/
@[simp] theorem coefficientTable_polynomial (lambda :
  Data.Gaussian.Basic.Canonical) :
    (coefficientTable lambda).polynomial = Paths.polynomial lambda := rfl

/-- Every exact coefficient allowance is below any strictly positive rational target. -/
theorem coefficientTable_allowances_lt (lambda :
  Data.Gaussian.Basic.Canonical)
    {target : Fraction.Rational} (positive : 0 < target) :
    CoefficientTable.AllowancesLt
      (coefficientTable lambda).entries target := by
  simp only [coefficientTable, coefficientValues,
    List.map_cons, List.map_nil,
    CoefficientTable.AllowancesLt,
    ExplicitLegendreFrame.exactCoefficientState_allowance]
  exact ⟨positive, positive, positive, trivial⟩
end Purelib.Curves.Legendre.Coefficients.Exact

end
