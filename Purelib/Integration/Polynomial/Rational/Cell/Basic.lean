module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
public import Purelib.Polynomial.Ascending.Rational.Integral
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Ascending.Rational.Basic (CoefficientPolynomial)

section
@[expose] public section

/-!
# General certified integration by finite path refinements

An integrand is supplied operationally: at each natural refinement it returns
one finite path of rational polynomial cell models and finite rational sample
certificates.  The integration program sums the exact polynomial cell
integrals.  A rational geometric modulus and a finite later-refinement
certificate turn those displayed sums into an ordinary productive CCL name.

There is no measure, completed partition, function-as-an-infinite-set, or
infinitesimal.  The only universal refinements are natural-number calls to the
supplied finite program.
-/

namespace Purelib.Integration.Polynomial.Rational.Cell.Basic

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
    integrandReading - Rational.GaussianEvaluation.eval polynomial
      ⟨parameter, 0⟩ = error
  /-- The retained residual's squared norm is at most the original allowance. -/ error_le : Basic.Canonical.normSq error
    ≤ allowance

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
  /-- The exact polynomial in the cell's local parameter. -/ polynomial : CoefficientPolynomial
  /-- The retained rational bound on squared local errors. -/ localAllowance : Fraction.Rational
  /-- The retained local allowance is nonnegative. -/ localAllowance_nonneg : 0 ≤ localAllowance
  /-- The original ordered observations certified against this exact polynomial and allowance. -/ observations : List
    (LocalObservation polynomial localAllowance)

constructive_injectivity CellModel

namespace CellModel

section
open Purelib
open Purelib.Data.Gaussian
/-- The exact Gaussian difference from the retained start to finish. -/
def displacement (cell :
  Integration.Polynomial.Rational.Cell.Basic.CellModel) : Basic.Canonical := cell.finish - cell.start

open Purelib.Polynomial.Ascending in
/-- Multiply the exact endpoint displacement by the polynomial's unit-parameter integral. -/
def integralSample (cell :
  Integration.Polynomial.Rational.Cell.Basic.CellModel) : Basic.Canonical :=
  cell.displacement *
    Rational.Integral.definiteIntegral cell.polynomial 0 1

open Purelib.Data.Rat in
/-- Multiply the local squared-error allowance by the exact endpoint displacement's squared norm. -/
def weightedAllowance (cell :
  Integration.Polynomial.Rational.Cell.Basic.CellModel) : Fraction.Rational :=
  Basic.Canonical.normSq cell.displacement * cell.localAllowance

open Purelib.Polynomial.Ascending
/-- Construct a polynomial cell with zero local allowance and an empty observation list. -/
def exact (start finish : Basic.Canonical)
  (polynomial : CoefficientPolynomial) : Integration.Polynomial.Rational.Cell.Basic.CellModel :=
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
    (Integration.Polynomial.Rational.Cell.Basic.CellModel.exact start finish polynomial).integralSample =
      (finish - start) *
        Rational.Integral.definiteIntegral polynomial 0 1 :=
  rfl
end

end CellModel

end Purelib.Integration.Polynomial.Rational.Cell.Basic

end
