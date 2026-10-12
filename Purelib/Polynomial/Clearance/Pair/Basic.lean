module

import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Interval.Basic
public import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

open Purelib

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

namespace Purelib.Polynomial.Clearance.Pair.Basic

set_option genInjectivity false in
/-- Positive uniform sum-of-squares clearance on a finite interval. -/
structure Certificate (p q : Dense.Rational.Basic.CoordinatePolynomial)
  (interval : Data.Rat.Interval.Bounds) where
  /-- The uniform sum-of-squares lower bound for the polynomial pair. -/ bound : Fraction.Rational
  /-- The retained pair clearance is positive. -/ positive : 0 < bound
  /-- Every parameter in the retained interval satisfies the sum-of-squares bound. -/ lower : ∀ x : Fraction.Rational,
    interval.Contains x →
    bound ≤ p.eval x ^ 2 + q.eval x ^ 2

constructive_injectivity Certificate

namespace Certificate

/-- A positive sum-of-squares lower bound makes the displayed coordinate
pair pointwise nonzero throughout the certified interval. -/
theorem eval_ne_zero {p q :
  Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (certificate : Certificate p q interval) {x : Fraction.Rational}
    (inside : interval.Contains x) : p.eval x ≠ 0 ∨ q.eval x ≠ 0 := by
  by_cases pZero : p.eval x = 0
  · right
    intro qZero
    have lower := certificate.lower x inside
    rw [pZero, qZero] at lower
    have boundLeZero : certificate.bound ≤ 0 :=
      lower.trans_eq (by ring1)
    exact (not_lt_of_ge boundLeZero) certificate.positive
  · exact Or.inl pZero
end Certificate
end Purelib.Polynomial.Clearance.Pair.Basic

end
