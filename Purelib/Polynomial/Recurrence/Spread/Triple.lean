module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Spread.Basic
public import Purelib.Geometry.Trigonometry.Spread.Triple

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: spread polynomials

Spread polynomials are primitive-recursive finite expressions.  No sequence
or limit object is introduced: evaluating index `n` performs exactly `n`
finite recurrence steps in the coefficient field.
-/

namespace Purelib.Geometry

variable {K : Type*} [ExplicitField K]

end Purelib.Geometry

section
variable {K : Type*} [ExplicitField K]

namespace Purelib.Polynomial.Recurrence.Spread.Triple

open _root_.Purelib.Geometry
/-- The spread recurrence preserves the triple-spread relation.

A triple formed by the previous term, the fixed spread and the current term yields a triple containing the next
recurrence term. -/
private theorem spreadTriple_next
    (previous current value : K)
    (triple : Geometry.Trigonometry.Spread.Triple.TripleSpread.SpreadTriple previous value current) :
    Geometry.Trigonometry.Spread.Triple.TripleSpread.SpreadTriple current value
      (2 * (1 - 2 * value) * current - previous + 2 * value) := by
  unfold Geometry.Trigonometry.Spread.Triple.TripleSpread.SpreadTriple
    Geometry.Trigonometry.Spread.Triple.TripleSpread.tripleSpreadFunction at triple ⊢
  calc
    (current + value +
            (2 * (1 - 2 * value) * current - previous + 2 * value)) ^ 2 -
          2 * (current ^ 2 + value ^ 2 +
            (2 * (1 - 2 * value) * current - previous + 2 * value) ^ 2) -
          4 * current * value *
            (2 * (1 - 2 * value) * current - previous + 2 * value) =
      (previous + value + current) ^ 2 -
        2 * (previous ^ 2 + value ^ 2 + current ^ 2) -
        4 * previous * value * current := by ring1
    _ = 0 := triple
end Purelib.Polynomial.Recurrence.Spread.Triple
end

namespace Purelib.Polynomial.Recurrence.Spread.Triple

variable {K : Type*} [ExplicitField K]

/-- Consecutive spread polynomials and their argument form a spread triple.

The triple-spread identity holds at every natural index in the supplied explicit field. -/
theorem recursive_spreads (index : Nat) (value : K) :
    Geometry.Trigonometry.Spread.Triple.TripleSpread.SpreadTriple (Recurrence.Spread.Basic.spreadPolynomial index value)
      value
      (Recurrence.Spread.Basic.spreadPolynomial (index + 1) value) := by
  induction index with
  | zero =>
      unfold Recurrence.Spread.Basic.spreadPolynomial Geometry.Trigonometry.Spread.Triple.TripleSpread.SpreadTriple
        Geometry.Trigonometry.Spread.Triple.TripleSpread.tripleSpreadFunction
      ring1
  | succ index inductionHypothesis =>
      have next := spreadTriple_next
        (Recurrence.Spread.Basic.spreadPolynomial index value)
        (Recurrence.Spread.Basic.spreadPolynomial (index + 1) value) value inductionHypothesis
      simpa only [Nat.succ_eq_add_one, Recurrence.Spread.Basic.spreadPolynomial_succ_succ] using next
end Purelib.Polynomial.Recurrence.Spread.Triple

end
