module

import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Dense.Rational.Basic
import Mathlib.Data.List.Basic
import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

namespace Purelib.Polynomial.Dense.Rational.Pair

/-- Two dense coordinate polynomials never vanish simultaneously. -/
def NoCommonZero (p q :
  Dense.Rational.Basic.CoordinatePolynomial) :
  Prop :=
  ∀ x : Fraction.Rational, p.eval x ≠ 0 ∨ q.eval x ≠ 0
end Purelib.Polynomial.Dense.Rational.Pair

end
