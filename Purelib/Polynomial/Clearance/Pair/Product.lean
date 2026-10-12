module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Clearance.Pair.Basic (Certificate)

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

namespace Purelib.Polynomial.Clearance.Pair.Basic.Certificate
section

/-- Multiply two complex-coordinate clearances using the exact finite
sum-of-two-squares identity. -/
def complexProduct
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (left : Certificate A B interval)
    (right : Certificate C D interval)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    Certificate E H interval where
  bound := left.bound * right.bound
  positive := Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_pos_direct
    left.positive right.positive
  lower := by
    intro x inside
    have leftLower := left.lower x inside
    have rightLower := right.lower x inside
    have productLower : left.bound * right.bound ≤
        (A.eval x ^ 2 + B.eval x ^ 2) *
          (C.eval x ^ 2 + D.eval x ^ 2) :=
      Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_direct leftLower rightLower
        right.positive.le
        (add_nonneg (Purelib.Data.Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _)
          (Purelib.Data.Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _))
    calc
      left.bound * right.bound ≤
          (A.eval x ^ 2 + B.eval x ^ 2) *
            (C.eval x ^ 2 + D.eval x ^ 2) := productLower
      _ = E.eval x ^ 2 + H.eval x ^ 2 := by
        rw [realIdentity x, imagIdentity x]
        ring1

end
end Purelib.Polynomial.Clearance.Pair.Basic.Certificate

end
