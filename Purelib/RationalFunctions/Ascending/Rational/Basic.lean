module

public import Purelib.Polynomial.Ascending.Rational.Basic

import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Finite divided differences and limit-free algebraic calculus

The derivative in this module is obtained by constructing a secant kernel
before putting its two displayed arguments equal.  No quotient by `x-y`,
limit, infinitesimal, or completed function graph is used.  Ordinary finite
polynomials, signed powers, and finite Laurent term lists are all evaluated by
structural recursion.
-/

namespace Purelib.RationalFunctions.Ascending.Rational.Basic

/-! ## Rational polynomial expressions -/

open Purelib.Polynomial in
set_option genInjectivity false in
/-- A displayed numerator and denominator in ascending rational coefficient order.

The pair stores finite polynomial data. Nonzero-denominator evidence is supplied separately to the identities that need
cancellation. -/
structure RationalPolynomial where
  /-- The finite numerator polynomial in ascending coefficient order. -/ numerator :
    Ascending.Rational.Basic.CoefficientPolynomial
  /-- The finite denominator polynomial in ascending coefficient order. -/ denominator :
    Ascending.Rational.Basic.CoefficientPolynomial

constructive_injectivity RationalPolynomial

end Purelib.RationalFunctions.Ascending.Rational.Basic

end
