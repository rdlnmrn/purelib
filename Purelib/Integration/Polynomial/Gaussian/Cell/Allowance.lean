module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Progressive finite integration with Gaussian coefficients

This is the period-facing integration kernel.  Every model is still a finite
list of rationally parameterized cells, but its local polynomial coefficients
are Gaussian rationals.  Hence a cell can approximate a genuinely complex
coefficient before multiplication by the complex path displacement.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Cell.Basic
namespace CellModel

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- The original displacement squared norm times the cell's retained local allowance. -/
def weightedAllowance (cell : Basic.CellModel) :
  Fraction.Rational :=
  Basic.Canonical.normSq cell.displacement * cell.localAllowance

section
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Cell
/-- Replace the local allowance with the supplied nonnegative allowance, retaining the original endpoints and
polynomial.

The constructed cell has an empty observation list rather than retaining observations indexed by the previous allowance.
-/
def withAllowance (cell : Basic.CellModel)
  (allowance : Fraction.Rational)
    (allowanceNonnegative : 0 <= allowance) : Basic.CellModel :=
  { start := cell.start
    finish := cell.finish
    polynomial := cell.polynomial
    localAllowance := allowance
    localAllowance_nonneg := allowanceNonnegative
    observations := [] }

/-- Replacing the local allowance preserves the original displacement. -/
@[simp] theorem withAllowance_displacement (cell :
  Basic.CellModel)
    (allowance : Fraction.Rational) (allowanceNonnegative : 0 <= allowance) :
    (cell.withAllowance allowance allowanceNonnegative).displacement =
      cell.displacement := rfl

/-- Replacing the local allowance preserves the exact original integral sample. -/
@[simp] theorem withAllowance_integralSample (cell :
  Basic.CellModel)
    (allowance : Fraction.Rational) (allowanceNonnegative : 0 <= allowance) :
    (cell.withAllowance allowance allowanceNonnegative).integralSample =
      cell.integralSample := rfl

end

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Cell
/-- Every Gaussian cell's displacement-weighted allowance is nonnegative. -/
theorem weightedAllowance_nonneg (cell :
  Basic.CellModel) :
    0 <= cell.weightedAllowance :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Basic.Canonical.normSq_nonneg cell.displacement) cell.localAllowance_nonneg

/-- A local squared-error bound becomes the retained weighted allowance after multiplication by the original cell
displacement. -/
theorem weighted_error_le (cell : Basic.CellModel)
  {error : Basic.Canonical}
    (bounded : Basic.Canonical.normSq error <= cell.localAllowance) :
    Basic.Canonical.normSq (cell.displacement * error) <= cell.weightedAllowance := by
  rw [Basic.Canonical.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded
    (Basic.Canonical.normSq_nonneg cell.displacement)
end CellModel

end Purelib.Integration.Polynomial.Gaussian.Cell.Basic

end

public section

namespace Purelib.Integration.Polynomial.Gaussian.Cell.Basic

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial.Ascending

namespace LocalObservation

/-- Retain the same actual observation while increasing its certified local error allowance. -/
@[expose] def weakenAllowance {polynomial : Gaussian.CoefficientPolynomial} {first last : Fraction.Rational}
    (observation : LocalObservation polynomial first) (order : first ≤ last) : LocalObservation polynomial last :=
  ⟨observation.parameter, observation.integrandReading, observation.error, observation.decomposition,
    observation.error_le.trans order⟩

/-- Increasing an observation allowance preserves its actual parameter. -/
theorem weakenAllowance_parameter {polynomial : Gaussian.CoefficientPolynomial} {first last : Fraction.Rational}
    (observation : LocalObservation polynomial first) (order : first ≤ last) :
    (observation.weakenAllowance order).parameter = observation.parameter := rfl

/-- Increasing an observation allowance preserves its complete actual integrand reading. -/
theorem weakenAllowance_reading {polynomial : Gaussian.CoefficientPolynomial} {first last : Fraction.Rational}
    (observation : LocalObservation polynomial first) (order : first ≤ last) :
    (observation.weakenAllowance order).integrandReading = observation.integrandReading := rfl

/-- Increasing an observation allowance preserves its actual retained residual. -/
theorem weakenAllowance_error {polynomial : Gaussian.CoefficientPolynomial} {first last : Fraction.Rational}
    (observation : LocalObservation polynomial first) (order : first ≤ last) :
    (observation.weakenAllowance order).error = observation.error := rfl

/-- Retaining the original allowance preserves the complete original local observation. -/
theorem weakenAllowance_self {polynomial : Gaussian.CoefficientPolynomial} {allowance : Fraction.Rational}
    (observation : LocalObservation polynomial allowance) :
    observation.weakenAllowance (Fraction.Order.Basic.le_refl allowance) = observation := by
  cases observation
  rfl

end LocalObservation

namespace CellModel

/-- Increase the original cell allowance while retaining every original ordered observation and coefficient.

Each original observation keeps its actual parameter, integrand reading,
residual and polynomial decomposition. Its bound is transported along the
same supplied allowance inequality; no observation is discarded or repaid.
-/
@[expose] def weakenAllowance (cell : CellModel) (allowance : Fraction.Rational)
    (order : cell.localAllowance ≤ allowance) : CellModel where
  start := cell.start
  finish := cell.finish
  polynomial := cell.polynomial
  localAllowance := allowance
  localAllowance_nonneg := cell.localAllowance_nonneg.trans order
  observations := cell.observations.map (fun observation => observation.weakenAllowance order)

/-- The weakened cell retains the actual transported observations in their original occurrence order. -/
theorem weakenAllowance_observations (cell : CellModel) (allowance : Fraction.Rational)
    (order : cell.localAllowance ≤ allowance) :
    (cell.weakenAllowance allowance order).observations =
      cell.observations.map (fun observation => observation.weakenAllowance order) := rfl

/-- Increasing the retained allowance preserves the same complete original cell displacement. -/
theorem weakenAllowance_displacement (cell : CellModel) (allowance : Fraction.Rational)
    (order : cell.localAllowance ≤ allowance) :
    (cell.weakenAllowance allowance order).displacement = cell.displacement := rfl

/-- Increasing the retained allowance preserves the same actual original finite integral sample. -/
theorem weakenAllowance_integralSample (cell : CellModel) (allowance : Fraction.Rational)
    (order : cell.localAllowance ≤ allowance) :
    (cell.weakenAllowance allowance order).integralSample = cell.integralSample := rfl

/-- Retaining the original allowance preserves the whole original cell and every original observation. -/
theorem weakenAllowance_self (cell : CellModel) :
    cell.weakenAllowance cell.localAllowance (Fraction.Order.Basic.le_refl _) = cell := by
  cases cell with
  | mk start finish polynomial allowance nonnegative observations =>
      have same : observations.map (fun observation =>
          observation.weakenAllowance (Fraction.Order.Basic.le_refl allowance)) = observations := by
        induction observations with
        | nil => rfl
        | cons head tail previous =>
            change head.weakenAllowance (Fraction.Order.Basic.le_refl allowance) :: _ = head :: tail
            rewrite [LocalObservation.weakenAllowance_self, previous]
            rfl
      change CellModel.mk start finish polynomial allowance _ _ =
        CellModel.mk start finish polynomial allowance _ observations
      exact congrArg (fun actual => CellModel.mk start finish polynomial allowance nonnegative actual) same

end CellModel

end Purelib.Integration.Polynomial.Gaussian.Cell.Basic

end
