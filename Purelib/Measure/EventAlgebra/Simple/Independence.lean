module
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.EventAlgebra.Basic
public import Purelib.Measure.EventAlgebra.Independence
import Purelib.Measure.EventAlgebra.Simple.Basic
public import Purelib.Measure.EventAlgebra.Simple.Distribution
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Distribution.Moments.Covariance
import Purelib.Data.Rat.Fraction.Arithmetic

@[expose] public section

/-!
# Independent finite simple observables

Independence of two finitely presented event algebras makes the expectation
of a product of their displayed simple observables factor exactly.  The proof
is finite distributivity over indicator terms.
-/

namespace Purelib.Measure

namespace SimpleObservable

/-- For independent event algebras, the expectation of one weighted left indicator times a right simple observable
factors into their original expectations.

Finite induction separates every retained right indicator term and uses the supplied independence witness for its exact
product probability. -/
private theorem expectation_term_mul_evaluate
    {α : Type} (distribution : Distribution α)
    {leftAlgebra rightAlgebra : EventAlgebra α}
    (independent : distribution.IndependentEventAlgebras
      leftAlgebra rightAlgebra)
    (leftTerm : SimpleTerm leftAlgebra) :
    ∀ right : SimpleObservable rightAlgebra,
      distribution.expectation (fun item =>
          (Distribution.indicator
              (leftAlgebra.evaluate leftTerm.event) item *
            leftTerm.coefficient) * right.evaluate item) =
        (distribution.probability
            (leftAlgebra.evaluate leftTerm.event) *
          leftTerm.coefficient) * right.expectation distribution
  | [] => by
      rw [expectation_eq_sum distribution []]
      simp only [List.map_nil, List.sum_nil]
      calc
        distribution.expectation (fun item =>
              (Distribution.indicator
                  (leftAlgebra.evaluate leftTerm.event) item *
                leftTerm.coefficient) * evaluate [] item) =
            distribution.expectation (fun _ => 0) :=
          distribution.expectation_congr _ _ (fun item => by
            simp only [evaluate, mul_zero, -eq_self, -iff_self]
            rfl)
        _ = 0 := distribution.expectation_constant 0
        _ = (distribution.probability
              (leftAlgebra.evaluate leftTerm.event) *
            leftTerm.coefficient) * 0 := by ring1
  | rightTerm :: remaining => by
      have pointwise (item : α) :
          (Distribution.indicator
              (leftAlgebra.evaluate leftTerm.event) item *
            leftTerm.coefficient) *
              evaluate (rightTerm :: remaining) item =
            (Distribution.indicator
                (leftAlgebra.evaluate leftTerm.event) item *
              Distribution.indicator
                (rightAlgebra.evaluate rightTerm.event) item) *
                (leftTerm.coefficient * rightTerm.coefficient) +
            (Distribution.indicator
              (leftAlgebra.evaluate leftTerm.event) item *
              leftTerm.coefficient) * evaluate remaining item := by
        simp only [evaluate]
        ring1
      have head : distribution.expectation (fun item =>
          (Distribution.indicator
              (leftAlgebra.evaluate leftTerm.event) item *
            Distribution.indicator
              (rightAlgebra.evaluate rightTerm.event) item) *
              (leftTerm.coefficient * rightTerm.coefficient)) =
          (distribution.probability
              (leftAlgebra.evaluate leftTerm.event) *
            distribution.probability
              (rightAlgebra.evaluate rightTerm.event)) *
              (leftTerm.coefficient * rightTerm.coefficient) := by
        have reorderedExpectation :
            distribution.expectation (fun item =>
              (Distribution.indicator
                  (leftAlgebra.evaluate leftTerm.event) item *
                Distribution.indicator
                  (rightAlgebra.evaluate rightTerm.event) item) *
                    (leftTerm.coefficient * rightTerm.coefficient)) =
              distribution.expectation (fun item =>
                (leftTerm.coefficient * rightTerm.coefficient) *
                  (Distribution.indicator
                      (leftAlgebra.evaluate leftTerm.event) item *
                    Distribution.indicator
                      (rightAlgebra.evaluate rightTerm.event) item)) :=
          distribution.expectation_congr _ _ (fun item => by ring1)
        rw [reorderedExpectation, distribution.expectation_scale,
          distribution.expectation_indicator_mul_indicator,
          independent leftTerm.event rightTerm.event]
        ring1
      have rightExpectation :
          expectation (rightTerm :: remaining) distribution =
            distribution.probability
                (rightAlgebra.evaluate rightTerm.event) *
              rightTerm.coefficient + expectation remaining distribution := by
        rw [expectation_eq_sum distribution (rightTerm :: remaining),
          expectation_eq_sum distribution remaining]
        simp only [List.map_cons, List.sum_cons, -eq_self, -iff_self]
        rfl
      have decomposedExpectation :
          distribution.expectation (fun item =>
            (Distribution.indicator
                (leftAlgebra.evaluate leftTerm.event) item *
              leftTerm.coefficient) *
                evaluate (rightTerm :: remaining) item) =
            distribution.expectation (fun item =>
              (Distribution.indicator
                  (leftAlgebra.evaluate leftTerm.event) item *
                Distribution.indicator
                  (rightAlgebra.evaluate rightTerm.event) item) *
                    (leftTerm.coefficient * rightTerm.coefficient) +
              (Distribution.indicator
                (leftAlgebra.evaluate leftTerm.event) item *
                leftTerm.coefficient) * evaluate remaining item) :=
        distribution.expectation_congr _ _ pointwise
      rw [decomposedExpectation, distribution.expectation_add, head,
        expectation_term_mul_evaluate distribution independent leftTerm
          remaining,
        rightExpectation]
      ring1

/-- Simple observables over independent event algebras have product expectation equal to the product of their exact
expectations.

The original finite coefficient tables are expanded into indicator terms, each paired using the supplied event-algebra
independence witness. -/
theorem expectation_mul_eq_mul_expectation_of_independent
    {α : Type} (distribution : Distribution α)
    {leftAlgebra rightAlgebra : EventAlgebra α}
    (independent : distribution.IndependentEventAlgebras
      leftAlgebra rightAlgebra) :
    ∀ (left : SimpleObservable leftAlgebra)
      (right : SimpleObservable rightAlgebra),
      distribution.expectation (fun item =>
          left.evaluate item * right.evaluate item) =
        left.expectation distribution * right.expectation distribution
  | [], right => by
      rw [expectation_eq_sum distribution []]
      simp only [List.map_nil, List.sum_nil]
      calc
        distribution.expectation (fun item =>
              evaluate [] item * right.evaluate item) =
            distribution.expectation (fun _ => 0) :=
          distribution.expectation_congr _ _ (fun item => by
            simp only [evaluate, zero_mul, -eq_self, -iff_self]
            rfl)
        _ = 0 := distribution.expectation_constant 0
        _ = 0 * right.expectation distribution := by ring1
  | leftTerm :: remaining, right => by
      have pointwise (item : α) :
          evaluate (leftTerm :: remaining) item * right.evaluate item =
            (Distribution.indicator
              (leftAlgebra.evaluate leftTerm.event) item *
              leftTerm.coefficient) * right.evaluate item +
            evaluate remaining item * right.evaluate item := by
        simp only [evaluate]
        ring1
      have leftExpectation :
          expectation (leftTerm :: remaining) distribution =
            distribution.probability
                (leftAlgebra.evaluate leftTerm.event) *
              leftTerm.coefficient + expectation remaining distribution := by
        rw [expectation_eq_sum distribution (leftTerm :: remaining),
          expectation_eq_sum distribution remaining]
        simp only [List.map_cons, List.sum_cons, -eq_self, -iff_self]
        rfl
      have decomposedExpectation :
          distribution.expectation (fun item =>
            evaluate (leftTerm :: remaining) item * right.evaluate item) =
            distribution.expectation (fun item =>
              (Distribution.indicator
                (leftAlgebra.evaluate leftTerm.event) item *
                leftTerm.coefficient) * right.evaluate item +
              evaluate remaining item * right.evaluate item) :=
        distribution.expectation_congr _ _ pointwise
      rw [decomposedExpectation, distribution.expectation_add,
        expectation_term_mul_evaluate distribution independent leftTerm right,
        expectation_mul_eq_mul_expectation_of_independent distribution
          independent remaining right,
        leftExpectation]
      ring1

/-- Simple observables over independent event algebras have covariance zero. -/
theorem covariance_eq_zero_of_independent
    {α : Type} (distribution : Distribution α)
    {leftAlgebra rightAlgebra : EventAlgebra α}
    (independent : distribution.IndependentEventAlgebras
      leftAlgebra rightAlgebra)
    (left : SimpleObservable leftAlgebra)
    (right : SimpleObservable rightAlgebra) :
    distribution.covariance left.evaluate right.evaluate = 0 := by
  rw [distribution.covariance_eq_productMoment_sub_means,
    expectation_mul_eq_mul_expectation_of_independent distribution
      independent left right]
  unfold expectation
  ring1

end SimpleObservable

end Purelib.Measure
