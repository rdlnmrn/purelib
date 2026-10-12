module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Finite expectation stability

These estimates turn supplied pointwise rational error budgets into exact
finite expectation bounds.  A second form permits a larger error on one
displayed exceptional event and charges exactly its finite probability.
-/

namespace Purelib.Measure

open Distribution (expectationWeight)

open Purelib.Data.Rat in
/-- Bound both signed differences of the two observables by the retained pointwise allowance on every occurrence. -/
def SymmetricErrorOn {α : Type} (atoms : List (Weighted α))
    (allowance left right : α → Fraction.Rational) : Prop :=
  ∀ atom, atom ∈ atoms →
    right atom.item - left atom.item ≤ allowance atom.item ∧
      left atom.item - right atom.item ≤ allowance atom.item

section Distribution

open Purelib.Data.Rat in
/-- The exact finite weighted integral preserves pointwise subtraction of rational observables. -/
theorem expectationWeight_sub {α : Type}
    (atoms : List (Weighted α)) (left right : α → Fraction.Rational) :
    expectationWeight atoms (fun item => left item - right item) =
      expectationWeight atoms left - expectationWeight atoms right := by
  induction atoms with
  | nil =>
      simp only [expectationWeight]
      ring1
  | cons atom remaining inductionHypothesis =>
      simp only [expectationWeight, inductionHypothesis]
      ring1

end Distribution

namespace Content
end Content

namespace Distribution
end Distribution

end Purelib.Measure

end
