module

public import Purelib.Data.Gaussian.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

@[expose] public section

/-!
# Finite Gaussian-coefficient polynomials

The general transcendental Taylor kernel deliberately uses rational-real
coefficients.  Period integration needs a separate, equally finite kernel:
the coefficient of `dx` along a complex path is Gaussian-valued even when the
path parameter is rational.  Coefficients here are therefore displayed
Gaussian rationals, stored from constant term upward.
-/

namespace Purelib.Polynomial.Ascending.Gaussian

set_option genInjectivity false in
/-- A finite Gaussian-rational coefficient table in ascending degree order.

The list retains its length and trailing zeros. Coefficientwise equality separately expresses equality of the
zero-extended coefficients. -/
structure CoefficientPolynomial where
  /-- The retained Gaussian coefficients, starting with the constant term. -/ coefficients : List
    Gaussian.Basic.Canonical
deriving DecidableEq

constructive_injectivity CoefficientPolynomial

namespace CoefficientPolynomial.mk

end CoefficientPolynomial.mk

namespace CoefficientPolynomial.mk

end CoefficientPolynomial.mk

open Purelib.Polynomial
namespace Basic

/-- The zero Gaussian polynomial represented by an empty coefficient list. -/
def zero : CoefficientPolynomial := ⟨[]⟩

end Basic

namespace Basic

/-- Represent a Gaussian constant by its singleton coefficient table. -/
def constant (value : Gaussian.Basic.Canonical) :
  CoefficientPolynomial := ⟨[value]⟩

end Basic

end Purelib.Polynomial.Ascending.Gaussian

end
