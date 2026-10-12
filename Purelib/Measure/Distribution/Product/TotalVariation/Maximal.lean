module
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Distribution.TotalVariation.Basic

import Purelib.Data.Bool.Relation
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Coupling.Law.Basic
import Purelib.Measure.Coupling.Law.Product
import Purelib.Measure.MaximalCoupling
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.Coupling.Law.TotalVariation
import Purelib.Measure.Coupling.Basic
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

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
end Distribution

namespace LawCoupling
end LawCoupling

namespace Distribution

open Purelib in
/-- Bound product-law total variation by one minus the product of the two corresponding marginal overlap probabilities.
-/
theorem totalVariationDistance_product_le_one_sub_mul
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (leftFirst rightFirst : Measure.Distribution α)
    (leftSecond rightSecond : Measure.Distribution β) :
    (leftFirst.product leftSecond).totalVariationDistance
        (rightFirst.product rightSecond) ≤
      1 - (1 - leftFirst.totalVariationDistance rightFirst) *
        (1 - leftSecond.totalVariationDistance rightSecond) := by
  let first := leftFirst.maximalLawCoupling rightFirst
  let second := leftSecond.maximalLawCoupling rightSecond
  have coupled := (first.product second)
    |>.totalVariationDistance_le_mismatchProbability
  rw [first.product_mismatchProbability_eq second,
    leftFirst.maximalLawCoupling_mismatchProbability rightFirst,
    leftSecond.maximalLawCoupling_mismatchProbability rightSecond] at coupled
  exact coupled
end Distribution

end Purelib.Measure

end
