module

public import Purelib.Data.Rat.Fraction
public import Purelib.Data.Int.Exponent

import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Rat

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

namespace Purelib.Polynomial.Laurent.Rational.Basic

set_option genInjectivity false in
/-- One displayed Laurent term with a rational coefficient. -/
structure LaurentTerm where
  /-- The rational coefficient of this displayed Laurent term. -/ coefficient : Fraction.Rational
  /-- The retained signed integer exponent. -/ exponent : Data.Int.Exponent
deriving DecidableEq

constructive_injectivity LaurentTerm

open Purelib.Polynomial in
set_option genInjectivity false in
/-- A Laurent polynomial is finite syntax, not a function represented by an
infinite set of input-output pairs.  Repeated exponents are harmless. -/
structure LaurentPolynomial where
  /-- The finite ordered Laurent term list; repeated exponents are retained. -/ terms : List
    LaurentTerm
deriving DecidableEq

constructive_injectivity LaurentPolynomial

end Purelib.Polynomial.Laurent.Rational.Basic

end
