module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Ascending.Rational.Basic
public import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
public import Purelib.Polynomial.Ascending.Rational.Composition
import Purelib.Polynomial.Ascending.Rational.Derivative
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite higher, Taylor, directional, and multivariable jets

The one-variable Taylor object below is a wrapper around the repository's
low-to-high finite rational polynomial program.  Repeated differentiation is
structural recursion on a requested natural order.  Multivariable first jets
store a displayed finite list of Gaussian-rational partial coefficients; a
directional coefficient is a finite dot-product recursion.

These are finite tables, not function spaces or infinite formal series.
-/

namespace Purelib.Polynomial.Ascending.Rational.Jet.Basic

set_option genInjectivity false in
/-- A finite one-variable Taylor jet, represented by its displayed
low-to-high rational coefficient list. -/
structure TaylorJet where
  /-- The retained finite rational polynomial underlying this Taylor jet. -/ polynomial :
    Ascending.Rational.Basic.CoefficientPolynomial
deriving DecidableEq

constructive_injectivity TaylorJet

namespace TaylorJet

/-- Construct a Taylor jet from an ascending rational coefficient list. -/
def ofCoefficients (coefficients : List
  Fraction.Rational) : TaylorJet :=
  ⟨⟨coefficients⟩⟩

/-- Return the jet's retained ascending coefficient list. -/
def coefficients (jet :
  TaylorJet) : List Fraction.Rational :=
  jet.polynomial.coefficients

/-- Read a jet coefficient, using zero beyond its retained table. -/
def coefficient (jet :
  TaylorJet) (degree : Nat) : Fraction.Rational :=
  Ascending.Rational.Basic.coefficient jet.polynomial degree

/-- Evaluate the finite Taylor jet at a Gaussian increment. -/
def evaluate (jet :
  TaylorJet) (increment : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  Ascending.Rational.GaussianEvaluation.eval jet.polynomial increment

/-- Retain only the jet coefficients below the requested count. -/
def truncate (count : Nat) (jet :
  TaylorJet) : TaylorJet :=
  ⟨Ascending.Rational.Basic.truncate count jet.polynomial⟩

/-- Add two finite jets by padded coefficient addition. -/
def add (left right :
  TaylorJet) : TaylorJet :=
  ⟨Ascending.Rational.Basic.add left.polynomial right.polynomial⟩

/-- Scale every retained Taylor coefficient by the rational factor. -/
def scale (factor : Fraction.Rational) (jet :
  TaylorJet) : TaylorJet :=
  ⟨Ascending.Rational.Basic.scale factor jet.polynomial⟩

/-- Truncated or untruncated multiplication is selected explicitly by the
caller; this constructor retains the whole finite Cauchy product. -/
def mul (left right :
  TaylorJet) : TaylorJet :=
  ⟨Ascending.Rational.Basic.mul left.polynomial right.polynomial⟩

/-- Compose the underlying finite Taylor polynomials by Horner substitution. -/
def compose (outer inner :
  TaylorJet) : TaylorJet :=
  ⟨Ascending.Rational.Composition.compose
    outer.polynomial inner.polynomial⟩

/-- Differentiate the finite Taylor coefficient table. -/
def derivative (jet :
  TaylorJet) : TaylorJet :=
  ⟨Ascending.Rational.Derivative.derivative jet.polynomial⟩
end TaylorJet

end Purelib.Polynomial.Ascending.Rational.Jet.Basic

end
