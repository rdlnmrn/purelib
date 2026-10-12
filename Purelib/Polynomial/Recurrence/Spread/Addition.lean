module
import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Triple

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

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

namespace Purelib.Polynomial.Recurrence.Spread.Addition

open _root_.Purelib.Geometry
/-- The even and odd addition seeds for the spread-polynomial recurrence.
Both identities are proved together by finite induction; the only geometric
input is the already algebraic `SpreadTriple` recurrence invariant. -/
private theorem
  spreadPolynomial_double_and_odd
  (index : Nat) (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial (index + index) value =
        4 * Recurrence.Spread.Basic.spreadPolynomial index value *
          (1 - Recurrence.Spread.Basic.spreadPolynomial index value) ∧
      Recurrence.Spread.Basic.spreadPolynomial (index + index + 1) value + value =
        2 * (Recurrence.Spread.Basic.spreadPolynomial (index + 1) value +
          Recurrence.Spread.Basic.spreadPolynomial index value -
          2 * Recurrence.Spread.Basic.spreadPolynomial (index + 1) value *
            Recurrence.Spread.Basic.spreadPolynomial index value) := open Purelib in by
  induction index with
  | zero =>
      constructor <;> unfold Recurrence.Spread.Basic.spreadPolynomial <;> ring1
  | succ index inductionHypothesis =>
      rcases inductionHypothesis with ⟨evenFormula, oddFormula⟩
      have triple := Recurrence.Spread.Triple.recursive_spreads index value
      unfold Geometry.Trigonometry.Spread.Triple.TripleSpread.SpreadTriple at triple
      have oddResolved :
          Recurrence.Spread.Basic.spreadPolynomial (index + index + 1) value =
            2 * (Recurrence.Spread.Basic.spreadPolynomial (index + 1) value +
              Recurrence.Spread.Basic.spreadPolynomial index value -
              2 * Recurrence.Spread.Basic.spreadPolynomial (index + 1) value *
                Recurrence.Spread.Basic.spreadPolynomial index value) - value := by
        calc
          Recurrence.Spread.Basic.spreadPolynomial (index + index + 1) value =
              (Recurrence.Spread.Basic.spreadPolynomial (index + index + 1) value + value) -
                value := by ring1
          _ = 2 * (Recurrence.Spread.Basic.spreadPolynomial (index + 1) value +
                Recurrence.Spread.Basic.spreadPolynomial index value -
                2 * Recurrence.Spread.Basic.spreadPolynomial (index + 1) value *
                  Recurrence.Spread.Basic.spreadPolynomial index value) - value := by
              rw [oddFormula]
      have nextEven :
          Recurrence.Spread.Basic.spreadPolynomial (Nat.succ index + Nat.succ index) value =
            4 * Recurrence.Spread.Basic.spreadPolynomial (Nat.succ index) value *
              (1 - Recurrence.Spread.Basic.spreadPolynomial (Nat.succ index) value) := by
        rw [show Nat.succ index + Nat.succ index =
          index + index + 2 by
            simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm, -eq_self, -iff_self]
            rfl]
        rw [Recurrence.Spread.Basic.spreadPolynomial_succ_succ, oddResolved, evenFormula]
        calc
          2 * (1 - 2 * value) *
                (2 * (Recurrence.Spread.Basic.spreadPolynomial (index + 1) value +
                    Recurrence.Spread.Basic.spreadPolynomial index value -
                    2 * Recurrence.Spread.Basic.spreadPolynomial (index + 1) value *
                      Recurrence.Spread.Basic.spreadPolynomial index value) - value) -
              4 * Recurrence.Spread.Basic.spreadPolynomial index value *
                (1 - Recurrence.Spread.Basic.spreadPolynomial index value) + 2 * value =
            4 * Recurrence.Spread.Basic.spreadPolynomial (index + 1) value *
                (1 - Recurrence.Spread.Basic.spreadPolynomial (index + 1) value) -
              4 * Geometry.Trigonometry.Spread.Triple.TripleSpread.tripleSpreadFunction
                (Recurrence.Spread.Basic.spreadPolynomial index value) value
                (Recurrence.Spread.Basic.spreadPolynomial (index + 1) value) := by
                  unfold Geometry.Trigonometry.Spread.Triple.TripleSpread.tripleSpreadFunction
                  ring1
          _ = 4 * Recurrence.Spread.Basic.spreadPolynomial (Nat.succ index) value *
                (1 - Recurrence.Spread.Basic.spreadPolynomial (Nat.succ index) value) := by
              rw [triple]
              simp only [mul_zero, Nat.succ_eq_add_one, -eq_self, -iff_self]
              ring1
      have nextEvenNormalized :
          Recurrence.Spread.Basic.spreadPolynomial (index + index + 2) value =
            4 * Recurrence.Spread.Basic.spreadPolynomial (index + 1) value *
              (1 - Recurrence.Spread.Basic.spreadPolynomial (index + 1) value) := by
        rw [show index + index + 2 =
          Nat.succ index + Nat.succ index by
            simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm, -eq_self, -iff_self]
            rfl]
        simpa only [Nat.succ_eq_add_one, -eq_self, -iff_self]  using nextEven
      have nextOdd :
          Recurrence.Spread.Basic.spreadPolynomial
              (Nat.succ index + Nat.succ index + 1) value + value =
            2 * (Recurrence.Spread.Basic.spreadPolynomial (Nat.succ index + 1) value +
              Recurrence.Spread.Basic.spreadPolynomial (Nat.succ index) value -
              2 * Recurrence.Spread.Basic.spreadPolynomial (Nat.succ index + 1) value *
                Recurrence.Spread.Basic.spreadPolynomial (Nat.succ index) value) := by
        rw [show Nat.succ index + Nat.succ index + 1 =
          (index + index + 1) + 2 by
            simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm, -eq_self, -iff_self]
            rfl]
        rw [Recurrence.Spread.Basic.spreadPolynomial_succ_succ, nextEvenNormalized, oddResolved]
        rw [show Nat.succ index + 1 = index + 2 by rfl]
        rw [Recurrence.Spread.Basic.spreadPolynomial_succ_succ]
        ring1
      exact ⟨nextEven, nextOdd⟩
/-- The addition-law statement at one displayed offset.  Keeping the offset
as an explicit argument avoids reasoning about equality of proposition-valued
functions in the simultaneous induction below. -/
private def
  spreadPolynomialAdditionAt
    (step : Nat) (value : K) (current : Nat) : Prop :=
  Recurrence.Spread.Basic.spreadPolynomial (current + step + step) value +
      Recurrence.Spread.Basic.spreadPolynomial current value =
    2 * (Recurrence.Spread.Basic.spreadPolynomial (current + step) value +
      Recurrence.Spread.Basic.spreadPolynomial step value -
      2 * Recurrence.Spread.Basic.spreadPolynomial (current + step) value *
        Recurrence.Spread.Basic.spreadPolynomial step value)
end Purelib.Polynomial.Recurrence.Spread.Addition
end

namespace Purelib.Polynomial.Recurrence.Spread.Addition

variable {K : Type*} [ExplicitField K]

/-- Finite addition law for spread polynomials.  In the usual symmetric
notation this is
`S_(a+2b) + S_a = 2(S_(a+b) + S_b - 2 S_(a+b) S_b)`.
It is the recurrence identity needed for composition and is valid in every
constructive explicit field, without a characteristic restriction. -/
theorem spread_polynomial_addition
    (offset step : Nat) (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial (offset + step + step) value +
        Recurrence.Spread.Basic.spreadPolynomial offset value =
      2 * (Recurrence.Spread.Basic.spreadPolynomial (offset + step) value +
        Recurrence.Spread.Basic.spreadPolynomial step value -
        2 * Recurrence.Spread.Basic.spreadPolynomial (offset + step) value *
          Recurrence.Spread.Basic.spreadPolynomial step value) := by
  have allPairs : ∀ current : Nat,
      spreadPolynomialAdditionAt step value current ∧
        spreadPolynomialAdditionAt step value (current + 1) :=
          by
    intro current
    induction current with
    | zero =>
        rcases spreadPolynomial_double_and_odd step value with
          ⟨evenFormula, oddFormula⟩
        constructor
        · unfold spreadPolynomialAdditionAt
          simp only [Nat.zero_add, Recurrence.Spread.Basic.spreadPolynomial_zero, add_zero, -eq_self, -iff_self] 
          rw [evenFormula]
          ring1
        · unfold spreadPolynomialAdditionAt
          rw [show 0 + 1 + step + step = step + step + 1 by
            simp only [Nat.zero_add, Nat.add_assoc, Nat.add_comm, -eq_self, -iff_self]
            rfl]
          rw [show 0 + 1 + step = step + 1 by
            simp only [Nat.zero_add, Nat.add_comm, -eq_self, -iff_self]
            rfl]
          rw [Recurrence.Spread.Basic.spreadPolynomial_one]
          exact oddFormula
    | succ current inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one, -eq_self, -iff_self]  using inductionHypothesis.2
        · change spreadPolynomialAdditionAt step value
            (Nat.succ current + 1)
          have currentFormula :
              Recurrence.Spread.Basic.spreadPolynomial (current + step + step) value +
                  Recurrence.Spread.Basic.spreadPolynomial current value =
                2 * (Recurrence.Spread.Basic.spreadPolynomial (current + step) value +
                  Recurrence.Spread.Basic.spreadPolynomial step value -
                  2 * Recurrence.Spread.Basic.spreadPolynomial (current + step) value *
                    Recurrence.Spread.Basic.spreadPolynomial step value) := by
            exact inductionHypothesis.1
          have nextFormula :
              Recurrence.Spread.Basic.spreadPolynomial (current + step + step + 1) value +
                  Recurrence.Spread.Basic.spreadPolynomial (current + 1) value =
                2 * (Recurrence.Spread.Basic.spreadPolynomial (current + step + 1) value +
                  Recurrence.Spread.Basic.spreadPolynomial step value -
                  2 * Recurrence.Spread.Basic.spreadPolynomial (current + step + 1) value *
                    Recurrence.Spread.Basic.spreadPolynomial step value) := by
            simpa only [spreadPolynomialAdditionAt,
              Nat.add_assoc,
              Nat.add_left_comm,
              Nat.add_comm, -eq_self, -iff_self]  using inductionHypothesis.2
          unfold spreadPolynomialAdditionAt
          rw [show Nat.succ current + 1 + step + step =
            (current + step + step) + 2 by
              simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm, -eq_self, -iff_self]
              rfl]
          rw [show Nat.succ current + 1 = current + 2 by rfl]
          rw [show Nat.succ current + 1 + step =
            (current + step) + 2 by
              simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm, -eq_self, -iff_self]
              rfl]
          rw [Recurrence.Spread.Basic.spreadPolynomial_succ_succ,
            Recurrence.Spread.Basic.spreadPolynomial_succ_succ,
            Recurrence.Spread.Basic.spreadPolynomial_succ_succ]
          calc
            (2 * (1 - 2 * value) *
                    Recurrence.Spread.Basic.spreadPolynomial (current + step + step + 1) value -
                  Recurrence.Spread.Basic.spreadPolynomial (current + step + step) value +
                  2 * value) +
                (2 * (1 - 2 * value) *
                    Recurrence.Spread.Basic.spreadPolynomial (current + 1) value -
                  Recurrence.Spread.Basic.spreadPolynomial current value + 2 * value) =
              2 * (1 - 2 * value) *
                  (Recurrence.Spread.Basic.spreadPolynomial (current + step + step + 1) value +
                    Recurrence.Spread.Basic.spreadPolynomial (current + 1) value) -
                (Recurrence.Spread.Basic.spreadPolynomial (current + step + step) value +
                  Recurrence.Spread.Basic.spreadPolynomial current value) + 4 * value := by ring1
            _ = 2 * (1 - 2 * value) *
                  (2 * (Recurrence.Spread.Basic.spreadPolynomial (current + step + 1) value +
                    Recurrence.Spread.Basic.spreadPolynomial step value -
                    2 * Recurrence.Spread.Basic.spreadPolynomial (current + step + 1) value *
                      Recurrence.Spread.Basic.spreadPolynomial step value)) -
                2 * (Recurrence.Spread.Basic.spreadPolynomial (current + step) value +
                  Recurrence.Spread.Basic.spreadPolynomial step value -
                  2 * Recurrence.Spread.Basic.spreadPolynomial (current + step) value *
                    Recurrence.Spread.Basic.spreadPolynomial step value) + 4 * value := by
                      rw [nextFormula, currentFormula]
            _ = 2 *
                ((2 * (1 - 2 * value) *
                    Recurrence.Spread.Basic.spreadPolynomial (current + step + 1) value -
                    Recurrence.Spread.Basic.spreadPolynomial (current + step) value + 2 * value) +
                  Recurrence.Spread.Basic.spreadPolynomial step value -
                  2 *
                    (2 * (1 - 2 * value) *
                        Recurrence.Spread.Basic.spreadPolynomial (current + step + 1) value -
                      Recurrence.Spread.Basic.spreadPolynomial (current + step) value + 2 * value) *
                    Recurrence.Spread.Basic.spreadPolynomial step value) := by ring1
  exact (allPairs offset).1
end Purelib.Polynomial.Recurrence.Spread.Addition

end
