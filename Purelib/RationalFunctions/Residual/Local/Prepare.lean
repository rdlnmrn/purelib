module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Box
public import Purelib.RationalFunctions.Residual.Local.Basic
public import Purelib.RootIsolation.Isolation.Coprime.Protection
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box

section
@[expose] public section

/-!
# Two-way residual and chordal bounds for rational functions

For a reduced coprime pair, a protectedState source track has a uniform positive
margin for the opposite polynomial.  This converts the polynomial
box-to-residual and residual-to-box theorems into corresponding theorems for
the quotient.  Swapping source and opposite gives the pole statements.
-/

namespace Purelib.RationalFunctions.Residual.Local.Basic
namespace LocalQuotientContext

variable {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box}

open Purelib.RootIsolation in
open Purelib.RationalFunctions in
/-- Refine the retained source state to the coprimality-protected state.

The construction uses the context's exact coprimality certificate, source track and current state, retaining the
original source and ambient box. -/
def protectedState (context :
  Residual.Local.Basic.LocalQuotientContext source opposite ambient) :
    State.WindingOne.Basic.WindingOneState source ambient :=
  Isolation.Coprime.Protection.protectedState context.coprime
    context.track context.current

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- Compute the rational opposite-polynomial quadrance margin from the coprimality certificate and ambient box. -/
def oppositeMargin
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient) : Rat.Fraction.Rational :=
  Dense.Gaussian.Coprime.Bounds.Box.rightMargin context.coprime ambient

open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- The computed opposite-polynomial margin is positive. -/
theorem oppositeMargin_pos
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient) :
    0 < context.oppositeMargin :=
  Dense.Gaussian.Coprime.Bounds.Box.rightMargin_pos context.coprime ambient

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- Compute the opposite-polynomial quadrance majorant on the retained ambient box. -/
def oppositeMajorant
    (_context : Residual.Local.Basic.LocalQuotientContext source opposite ambient) : Rat.Fraction.Rational :=
  Dense.Gaussian.Bounds.Box.denseEvalNormMajorant opposite ambient

open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- The computed opposite-polynomial majorant is positive. -/
theorem oppositeMajorant_pos
    (context : Residual.Local.Basic.LocalQuotientContext source opposite ambient) :
    0 < context.oppositeMajorant :=
  Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos opposite ambient
end LocalQuotientContext

end Purelib.RationalFunctions.Residual.Local.Basic

end
