module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Polynomial.Clearance.Pair.Basic
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Rational.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Mathlib.Algebra.Ring.Commute
import Purelib.Tactic.Ring

namespace Purelib.Polynomial.Clearance.Pair.Basic.Certificate

open Purelib.Data.Rat
open Purelib.Polynomial

/-- Exchange the coordinate polynomials while retaining the exact positive sum-of-squares bound.

The coordinate order changes while the original interval and cached positive
bound remain the same. Commutativity of the two displayed rational squares
transports the certificate lower bound without selecting new data. -/
@[expose] public def swap {p q : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (certificate : Clearance.Pair.Basic.Certificate p q interval) : Clearance.Pair.Basic.Certificate q p interval where
  bound := certificate.bound
  positive := certificate.positive
  lower := by
    intro x inside
    calc
      certificate.bound ≤ p.eval x ^ 2 + q.eval x ^ 2 :=
        certificate.lower x inside
      _ = q.eval x ^ 2 + p.eval x ^ 2 :=
        Fraction.Field.add_comm _ _

/-- Negating the second coordinate preserves a sum-of-squares clearance.

The first coordinate and interval stay fixed, while dense negation supplies
the second coordinate. Its evaluated square equals the original second
coordinate square, so the exact cached bound and its positivity are retained. -/
@[expose] public def negSecond {p q : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (certificate : Clearance.Pair.Basic.Certificate p q interval) :
    Clearance.Pair.Basic.Certificate p (-q) interval where
  bound := certificate.bound
  positive := certificate.positive
  lower := by
    intro x inside
    calc
      certificate.bound ≤ p.eval x ^ 2 + q.eval x ^ 2 :=
        certificate.lower x inside
      _ = p.eval x ^ 2 + (-q).eval x ^ 2 := by
        rw [Dense.Basic.DensePolynomial.eval_neg]
        ring1

/-- Reuse a uniform clearance certificate on a displayed subinterval.

The supplied refinement contains the new interval in the original root.
Every point of that interval retains its original membership evidence, so
the same cached bound and positivity certify the restricted polynomial pair. -/
@[expose] public def restrict {p q : Dense.Rational.Basic.CoordinatePolynomial} {root interval :
  Data.Rat.Interval.Bounds}
    (certificate : Clearance.Pair.Basic.Certificate p q root) (refines : interval.Refines root) :
    Clearance.Pair.Basic.Certificate p q interval where
  bound := certificate.bound
  positive := certificate.positive
  lower := by
    intro x inside
    exact certificate.lower x
      ⟨refines.1.trans inside.1, inside.2.trans refines.2⟩

end Purelib.Polynomial.Clearance.Pair.Basic.Certificate
