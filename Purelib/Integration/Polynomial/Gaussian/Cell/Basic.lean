module
public import Purelib.Data.Gaussian.Scale

import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
public import Purelib.Polynomial.Ascending.Gaussian.Integral
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Ascending.Gaussian (CoefficientPolynomial)

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

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial.Ascending in
set_option genInjectivity false in
/-- A retained local integrand reading with exact polynomial residual and squared-error allowance.

The parameter, reading and error are stored explicitly and tied to the original polynomial and rational allowance by
their decomposition and norm bound. -/
structure LocalObservation (polynomial :
  CoefficientPolynomial)
    (allowance : Fraction.Rational) where
  /-- The retained rational local parameter of this observation. -/ parameter : Fraction.Rational
  /-- The original Gaussian integrand reading. -/ integrandReading : Basic.Canonical
  /-- The retained Gaussian residual from the polynomial reading. -/ error : Basic.Canonical
  /-- The integrand reading minus the original polynomial evaluation equals the retained residual. -/ decomposition :
    integrandReading - Gaussian.Evaluation.eval polynomial
      ⟨parameter, 0⟩ = error
  /-- The retained residual's squared norm is at most the original allowance. -/ error_le : Basic.Canonical.normSq error
    <= allowance

constructive_injectivity LocalObservation

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial.Ascending in
set_option genInjectivity false in
/-- A polynomial integration cell with endpoints, nonnegative local allowance and retained certified observations.

The polynomial is expressed in the cell's local parameter; its integral sample is multiplied by the exact endpoint
displacement. -/
structure CellModel where
  /-- The cell's retained Gaussian starting endpoint. -/ start : Basic.Canonical
  /-- The cell's retained Gaussian finishing endpoint. -/ finish : Basic.Canonical
  /-- The exact polynomial in the cell's local parameter. -/ polynomial :
    CoefficientPolynomial
  /-- The retained rational bound on squared local errors. -/ localAllowance : Fraction.Rational
  /-- The retained local allowance is nonnegative. -/ localAllowance_nonneg : 0 <= localAllowance
  /-- The original ordered observations certified against this exact polynomial and allowance. -/ observations : List
    (LocalObservation polynomial localAllowance)

constructive_injectivity CellModel

namespace CellModel

section
open Purelib
open Purelib.Data.Gaussian
/-- The exact Gaussian difference from the retained start to finish. -/
def displacement (cell :
  Integration.Polynomial.Gaussian.Cell.Basic.CellModel) : Basic.Canonical := cell.finish - cell.start

section
open Purelib.Polynomial.Ascending
/-- Multiply the exact endpoint displacement by the polynomial's unit-parameter integral. -/
def integralSample (cell :
  Integration.Polynomial.Gaussian.Cell.Basic.CellModel) : Basic.Canonical :=
  cell.displacement *
    Gaussian.Integral.definiteIntegral cell.polynomial 0 1

/-- Construct a polynomial cell with zero local allowance and an empty observation list. -/
def exact (start finish : Basic.Canonical)
  (polynomial : CoefficientPolynomial) :
    Integration.Polynomial.Gaussian.Cell.Basic.CellModel :=
  { start := start
    finish := finish
    polynomial := polynomial
    localAllowance := 0
    localAllowance_nonneg := le_rfl
    observations := [] }

/-- An exact cell's integral sample is its endpoint displacement times the original polynomial's unit integral. -/
theorem exact_integralSample (start finish :
  Basic.Canonical)
    (polynomial : CoefficientPolynomial) :
    (Integration.Polynomial.Gaussian.Cell.Basic.CellModel.exact start finish polynomial).integralSample =
      (finish - start) *
        Gaussian.Integral.definiteIntegral polynomial 0 1 := rfl

end

/-- A Gaussian polynomial cell with identical endpoints has zero integral sample. -/
theorem integralSample_eq_zero_of_start_eq_finish
  (cell : Integration.Polynomial.Gaussian.Cell.Basic.CellModel)
    (equal : cell.start = cell.finish) : cell.integralSample = 0 := by
  unfold Integration.Polynomial.Gaussian.Cell.Basic.CellModel.integralSample
    Integration.Polynomial.Gaussian.Cell.Basic.CellModel.displacement
  rw [equal, Basic.sub_self,
    Basic.zero_mul]
end

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- Read the retained observation's point on the original cell segment. -/
def observationPoint
    (cell : Basic.CellModel)
    (observation : Basic.LocalObservation cell.polynomial cell.localAllowance) : Basic.Canonical :=
  cell.start + Scale.scale observation.parameter cell.displacement

end CellModel

end Purelib.Integration.Polynomial.Gaussian.Cell.Basic

end
