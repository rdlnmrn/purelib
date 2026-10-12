module

import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Derivative
public import Purelib.Polynomial.Dense.Rational.Bezout.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial

section
@[expose] public section

/-!
# Common finite event partitions for curve roots and box edges

The root-event polynomial of a boundary chart and the four cleared box-edge
polynomials must be classified on the same parameter cells.  This module
forms one product of their complete reduced-chain guards, uses it for every
central-third cut, and chooses a coefficient-computed depth below all of the
individual event-resolution widths.

Consequently every emitted leaf has, simultaneously:

* a finite Cauchy--Sturm event record for the chart root polynomial; and
* a finite event record for every nontrivial box-edge condition.

Identically-zero box conditions are retained separately by
`CurveBoxConditions.condition_zero_or_active`; they never make
the common cut guard vanish.
-/

namespace Purelib.Polynomial.Dense.Rational.Squarefree.BoundaryPartition

/-! ## Squarefree/Taylor refinement -/

/-- A retained unit Bezout certificate between a rational polynomial and its automatic derivative. -/
abbrev SquarefreeCertificate (event :
  Dense.Basic.RationalPolynomial) :=
  Dense.Rational.Bezout.Basic.CoprimeCertificate event
    (Dense.Derivative.derivative event)
end Purelib.Polynomial.Dense.Rational.Squarefree.BoundaryPartition

end

section
@[expose] public section

/-!
# Finite squarefree decomposition of coordinate polynomials

A boundary-curve gcd can have repeated parameter factors even when the
original Gaussian polynomial is squarefree.  This module removes that
special-case obligation: finite extended Euclid recursively decomposes any
nonzero positive-degree constructive-rational polynomial into displayed
squarefree occurrences.  The product identity and root coverage are proved
from finite coefficient candidates, never from evaluation over a carrier.
-/

namespace Purelib.Polynomial.Dense.Rational.Squarefree
/-- A retained unit Bezout certificate between a rational polynomial and its automatic derivative. -/
abbrev SquarefreeCertificate (p :
  Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial) :=
  Dense.Rational.Bezout.Basic.CoprimeCertificate p
    (Dense.Derivative.derivative p)

set_option genInjectivity false in
/-- One positive-degree squarefree occurrence. -/
structure Factor where
  /-- The retained rational polynomial for this squarefree occurrence. -/ polynomial :
    Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial
  /-- The retained polynomial is already normalized. -/ normalized : polynomial.normalize = polynomial
  /-- The retained polynomial is represented as nonzero. -/ nonzero : polynomial.isZero = false
  /-- The retained polynomial has strictly positive natural degree. -/ degreePositive : 0 < polynomial.natDegree
  /-- The retained Bezout data certifies coprimality of the polynomial and its derivative. -/ squarefree :
    SquarefreeCertificate polynomial

constructive_injectivity Factor

end Purelib.Polynomial.Dense.Rational.Squarefree

end
