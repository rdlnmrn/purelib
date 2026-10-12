module

import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Polynomial.Dense.Rational.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

namespace Purelib.Polynomial.Dense.Rational.Bezout.Basic

set_option genInjectivity false in
/-- Explicit finite Bézout data.  Keeping the two cofactors in the certificate
lets determinant and Euclidean constructions share the same clearance path. -/
structure CoprimeCertificate (p q :
  CoordinatePolynomial) where
  /-- The coefficient multiplying the first retained polynomial in the unit identity. -/ left :
    CoordinatePolynomial
  /-- The coefficient multiplying the second retained polynomial in the unit identity. -/ right :
    CoordinatePolynomial
  /-- The displayed linear combination of the two polynomial values equals one at every rational point. -/ identity : ∀
    x : Fraction.Rational,
    1 = left.eval x * p.eval x + right.eval x * q.eval x

constructive_injectivity CoprimeCertificate

namespace CoprimeCertificate

/-- Swap the retained polynomials and their Bezout coefficients while preserving the unit identity. -/
def swap {p q :
  CoordinatePolynomial}
    (certificate : CoprimeCertificate p q) : CoprimeCertificate
      q p where
  left := certificate.right
  right := certificate.left
  identity := by
    intro x
    rw [certificate.identity]
    ring1

/-- A retained unit Bezout identity prevents simultaneous zero evaluations at any supplied rational point. -/
theorem eval_ne_zero {p q :
  CoordinatePolynomial}
    (certificate : CoprimeCertificate p q) (x : Fraction.Rational) :
    p.eval x ≠ 0 ∨ q.eval x ≠ 0 := by
  by_cases hp : p.eval x = 0
  · right
    intro hq
    have contradiction := certificate.identity x
    rw [hp, hq, Fraction.Field.mul_zero_direct,
      Fraction.Field.mul_zero_direct,
      Fraction.Field.zero_add] at contradiction
    exact Fraction.Field.zero_ne_one contradiction.symm
  · exact Or.inl hp
end CoprimeCertificate
end Purelib.Polynomial.Dense.Rational.Bezout.Basic

end

section
/-!
Checked finite witnesses for the original separated-Sylvester clearances.
An untrusted column solves the evaluated matrix equation. The original scaled
inverse proves uniqueness, so the saved column supplies the original normalized
cofactors, rather than merely some valid Bezout coefficients. Equality of the
resulting rational polynomials uses the existing explicit finite-grid theorem.
-/

@[expose] public section

namespace Purelib.Polynomial.Dense.Rational.Bezout.Basic

/-- Two Bezout certificates for the same inputs are equal when their two retained coefficient polynomials are equal. -/
theorem coprime_eq {p q :
  CoordinatePolynomial}
    (left right : CoprimeCertificate p q)
    (first : left.left = right.left) (second : left.right = right.right) : left = right := by
  cases left
  cases right
  cases first
  cases second
  rfl
end Purelib.Polynomial.Dense.Rational.Bezout.Basic

end

section
@[expose] public section

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

namespace Purelib.RootIsolation.Sturm.CoordinateTaylor

/-! ## A uniform squarefree root-orientation width -/

end Purelib.RootIsolation.Sturm.CoordinateTaylor

end

section
@[expose] public section

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

namespace Purelib.RootIsolation.Sturm.RootCount
end Purelib.RootIsolation.Sturm.RootCount

end
