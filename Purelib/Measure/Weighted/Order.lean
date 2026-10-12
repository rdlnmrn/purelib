module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Finite convergence certificates

The usual monotone, Fatou, and dominated convergence theorems concern
completed limits.  This module retains their executable finite content:
displayed monotone chains have monotone rational integrals, displayed lower
envelopes satisfy the finite Fatou inequality, and an integrable rational
error envelope gives an explicit accuracy certificate.

No sequence, limit, supremum, extended value, or completed function space is
formed.
-/

namespace Purelib.Measure

open Purelib.Data.Rat in
/-- Require the lower observable to be at most the upper at every exact retained occurrence. -/
def PointwiseLeOn {α : Type} (atoms : List (Weighted α))
    (lower upper : α → Fraction.Rational) : Prop :=
  ∀ atom, atom ∈ atoms → lower atom.item ≤ upper atom.item

section
open Purelib.Data.Rat
/-- Every observable is pointwise at most itself on the retained occurrence list. -/
theorem PointwiseLeOn.refl {α : Type} (atoms : List (Weighted α))
    (value : α → Fraction.Rational) : PointwiseLeOn atoms value value := by
  intro atom member
  exact le_rfl

/-- Compose pointwise comparisons through the same middle observable on the retained list. -/
theorem PointwiseLeOn.trans {α : Type} {atoms : List (Weighted α)}
    {first second third : α → Fraction.Rational}
    (firstSecond : PointwiseLeOn atoms first second)
    (secondThird : PointwiseLeOn atoms second third) :
    PointwiseLeOn atoms first third := by
  intro atom member
  exact (firstSecond atom member).trans (secondThird atom member)

end

open Purelib.Data.Rat in
/-- Require successive observables in the finite list to increase on every retained weighted occurrence.

Empty and singleton lists satisfy the condition. Longer lists retain each adjacent comparison and the same condition on
the tail. -/
def PointwiseMonotoneChainOn {α : Type} (atoms : List (Weighted α)) :
    List (α → Fraction.Rational) → Prop
  | [] => True
  | [_] => True
  | first :: second :: remaining =>
      PointwiseLeOn atoms first second ∧
        PointwiseMonotoneChainOn atoms (second :: remaining)
namespace Content
end Content
namespace Content
end Content
namespace Content
namespace IntegralErrorBudget
end IntegralErrorBudget
namespace MonotoneIntegralBudget
end MonotoneIntegralBudget

end Content

end Purelib.Measure

end
