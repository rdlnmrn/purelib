module
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Distribution.Sampling.Basic
public import Purelib.Measure.Distribution.TotalVariation.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Product.TotalVariation.Maximal
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
import Purelib.Measure.Distribution.Pushforward.TotalVariation
import Purelib.Measure.Coupling.Law.Basic
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Data.List.BinaryPrefix.Gauge
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

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
open Purelib.Data.Rat in
/-- Independent samples have total variation at most one minus the corresponding power of one minus the original
distance.

Both sample laws retain the same supplied count; the bound follows by iterating the product contraction for the original
finite distributions. -/
theorem iidSamples_totalVariationDistance_le_one_sub_pow
    {α : Type} [DecidableEq α] (left right : Measure.Distribution α) :
    ∀ count : Nat,
      (left.iidSamples count).totalVariationDistance
          (right.iidSamples count) ≤
        1 - (1 - left.totalVariationDistance right) ^ count
  | 0 => by
      have zero : (left.iidSamples 0).totalVariationDistance
          (right.iidSamples 0) = 0 := by
        apply (left.iidSamples 0)
          |>.totalVariationDistance_eq_zero_iff_evaluationEquivalent
            (right.iidSamples 0) |>.2
        rw [left.iidSamples_zero, right.iidSamples_zero]
        exact EvaluationEquivalent.refl (Distribution.pure [])
      rw [zero, pow_zero]
      change (0 : Fraction.Rational) ≤ 0
      exact le_rfl
  | count + 1 => by
      rw [left.iidSamples_succ, right.iidSamples_succ]
      let distance := left.totalVariationDistance right
      let tailDistance := (left.iidSamples count).totalVariationDistance
        (right.iidSamples count)
      let tailBound : Fraction.Rational := 1 - (1 - distance) ^ count
      have distanceAtMostOne : distance ≤ 1 :=
        left.totalVariationDistance_le_one right
      have complementNonnegative : 0 ≤ 1 - distance :=
        Fraction.Order.Arithmetic.sub_nonneg_direct distanceAtMostOne
      have tailLe : tailDistance ≤ tailBound := by
        exact iidSamples_totalVariationDistance_le_one_sub_pow
          left right count
      have complementOrder : 1 - tailBound ≤ 1 - tailDistance := by
        exact Fraction.Order.Arithmetic.sub_le_sub_left_direct tailLe 1
      have productOrder :
          (1 - distance) * (1 - tailBound) ≤
            (1 - distance) * (1 - tailDistance) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          complementOrder complementNonnegative
      calc
        ((left.product (left.iidSamples count)).map fun pair =>
              pair.1 :: pair.2).totalVariationDistance
            ((right.product (right.iidSamples count)).map fun pair =>
              pair.1 :: pair.2) ≤
          (left.product (left.iidSamples count)).totalVariationDistance
            (right.product (right.iidSamples count)) :=
          (left.product (left.iidSamples count)).totalVariationDistance_map_le
            (right.product (right.iidSamples count))
            (fun pair => pair.1 :: pair.2)
        _ ≤ 1 - (1 - distance) * (1 - tailDistance) := by
          exact left.totalVariationDistance_product_le_one_sub_mul right
            (left.iidSamples count) (right.iidSamples count)
        _ ≤ 1 - (1 - distance) * (1 - tailBound) :=
          Fraction.Order.Arithmetic.sub_le_sub_left_direct productOrder 1
        _ = 1 - (1 - left.totalVariationDistance right) ^ (count + 1) := by
          dsimp only [distance, tailBound]
          rw [pow_succ]
          generalize powerEqual : (1 - left.totalVariationDistance right) ^ count = power
          ring1

end Distribution

end Purelib.Measure

end
