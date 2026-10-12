module
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Conditioning.CauchySchwarz
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Distribution.Partition.Expectation

section
@[expose] public section

/-!
# Finite conditional Cauchy--Schwarz inequalities

Conditioning on one explicitly positive event produces another displayed
finite rational distribution.  Applying the root-free powered-L2 inequality
to that table gives conditional Cauchy--Schwarz without choosing square roots.
Centering the two observables gives the corresponding conditional covariance
bound.  The same eventwise calculation is exposed pointwise over a displayed
positive partition.
-/

namespace Purelib.Measure

namespace Distribution
end Distribution

namespace PositiveEventPartition

open Purelib.Data.Rat in
/-- At each retained atom, squared partition-conditional product expectation is bounded by the product of the two
partition-conditional square expectations. -/
theorem conditionalExpectation_mul_sq_le {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Fraction.Rational) (atom : Weighted α)
    (member : atom ∈ distribution.atoms) :
    partition.conditionalExpectation
          (fun item => left item * right item) atom.item ^ 2 ≤
      partition.conditionalExpectation
          (fun item => left item ^ 2) atom.item *
        partition.conditionalExpectation
          (fun item => right item ^ 2) atom.item := by
  rcases partition.toEventPartition.exists_selected_event atom member with
    ⟨event, eventMember, selected⟩
  rw [partition.conditionalExpectation_eq_conditionalMean_on_cell
      (fun item => left item * right item) event eventMember atom member
      selected,
    partition.conditionalExpectation_eq_conditionalMean_on_cell
      (fun item => left item ^ 2) event eventMember atom member selected,
    partition.conditionalExpectation_eq_conditionalMean_on_cell
      (fun item => right item ^ 2) event eventMember atom member selected]
  exact distribution.conditionalMean_mul_sq_le event
    (partition.positive event eventMember) left right

end PositiveEventPartition

end Purelib.Measure

end
