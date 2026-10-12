module
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic

public import Purelib.Measure.Distribution.Equivalence

section
@[expose] public section

/-!
# Products of finite couplings

Two displayed law couplings can be sampled independently and their
coordinates regrouped.  Under equality, the product mismatches exactly when
at least one component mismatches, giving the rational formula
`1 - (1 - d₁) * (1 - d₂)`.  Product maximal couplings therefore sharpen the
additive total-variation tensorization bound.
-/

namespace Purelib.Measure

namespace Distribution

/-- Mapping product coordinates separately gives the same evaluations as taking the product of the two original
pushforwards. -/
theorem productMap_evaluationEquivalent {α β γ δ : Type}
    (left : Distribution α) (right : Distribution β)
    (leftMap : α → γ) (rightMap : β → δ) :
    EvaluationEquivalent
      ((left.product right).map fun pair =>
        (leftMap pair.1, rightMap pair.2))
      ((left.map leftMap).product (right.map rightMap)) := by
  apply EvaluationEquivalent.of_expectation_eq
  intro value
  rw [(left.product right).map_expectation,
    left.product_expectation_iterated,
    (left.map leftMap).product_expectation_iterated,
    left.map_expectation]
  exact left.expectation_congr _ _ (fun leftItem => by
    rw [right.map_expectation])

end Distribution

namespace LawCoupling
end LawCoupling

namespace Distribution
end Distribution

end Purelib.Measure

end
