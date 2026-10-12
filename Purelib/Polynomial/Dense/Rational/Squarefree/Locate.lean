module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
public import Purelib.Polynomial.Dense.Rational.Squarefree.Product

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Rational.Squarefree (Factor)

open Purelib.Data.Rat

open Purelib.Polynomial

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

set_option genInjectivity false in
/-- Proof-bearing output of the executable first-zero-factor scan. -/
structure LocatedFactor (factors : List
  Factor) (point : Fraction.Rational) where
  /-- The retained squarefree factor selected by the scan. -/ factor : Factor
  /-- The selected factor occurs in the original list. -/ member : factor ∈ factors
  /-- The selected polynomial vanishes at the displayed rational point. -/ zero : factor.polynomial.eval point = 0

constructive_injectivity LocatedFactor

/-- Select the first displayed squarefree factor vanishing at a certified product root.

The finite recursive scan retains its exact factor, list membership and zero evaluation; the product-zero hypothesis
rules out exhausting the list. -/
def locateFactor
    (factors : List Factor) (point : Fraction.Rational)
    (productZero : (Dense.Rational.Squarefree.factorProduct factors).eval point = 0) :
    LocatedFactor factors point := by
  match factors with
  | [] =>
      simp only [Dense.Rational.Squarefree.factorProduct, Dense.Basic.DensePolynomial.eval_constant] at productZero
      exact (Fraction.Field.zero_ne_one productZero.symm).elim
  | factor :: remaining =>
      by_cases headZero : factor.polynomial.eval point = 0
      · exact ⟨factor, List.mem_cons_self, headZero⟩
      · have tailZero : (Dense.Rational.Squarefree.factorProduct remaining).eval point = 0 := by
          rw [Dense.Rational.Squarefree.factorProduct, Dense.Basic.DensePolynomial.eval_mul] at productZero
          by_cases tailZero : (Dense.Rational.Squarefree.factorProduct remaining).eval point = 0
          · exact tailZero
          · exact (Fraction.Field.mul_ne_zero_direct
              headZero tailZero productZero).elim
        let located := locateFactor remaining point tailZero
        exact ⟨located.factor, List.mem_cons_of_mem factor located.member,
          located.zero⟩
end Purelib.Polynomial.Dense.Rational.Squarefree

end

section
@[expose] public section

/-!
# Constructive root events on rationally parameterized curves

The constant-gcd branch of `CurveClear` excludes a polynomial
root everywhere on a rational curve.  This module handles the complementary
finite cases.  If both cleared coordinates vanish identically it records that
degeneracy explicitly.  Otherwise a nonconstant gcd is an ordinary nonzero
coordinate polynomial, so its derivative/gcd Sturm chain has the executable
event partition constructed in `ConstructiveSturmEventPartition`.
-/

namespace Purelib.CCL.Boundary.Curve.Events
end Purelib.CCL.Boundary.Curve.Events

end
