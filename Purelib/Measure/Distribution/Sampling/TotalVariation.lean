module
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Distribution.Sampling.Basic
public import Purelib.Measure.Distribution.TotalVariation.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Product.TotalVariation
import Purelib.Data.List.Event
import Purelib.Measure.Distribution.Pushforward.TotalVariation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Product and finite-sample total variation bounds

Tensoring two finite rational laws with a common probability factor preserves
total variation exactly.  Changing both factors costs at most the sum of the
two component distances.  Iterating this finite tensorization gives the
explicit `n * TV` bound for exactly `n` IID samples.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib in
open Purelib.Data.Rat in
/-- Total variation between equal-length independent-sample laws is at most draw count times the original source-law
distance.

Both sample laws retain their original source distributions and the same exact number of ordered draws. -/
theorem iidSamples_totalVariationDistance_le
    {α : Type} [DecidableEq α] (left right : Measure.Distribution α) :
    ∀ count : Nat,
      (left.iidSamples count).totalVariationDistance
          (right.iidSamples count) ≤
        (count : Fraction.Rational) * left.totalVariationDistance right
  | 0 => by
      have zero : (left.iidSamples 0).totalVariationDistance
          (right.iidSamples 0) = 0 := by
        apply (left.iidSamples 0).totalVariationDistance_eq_zero_iff_evaluationEquivalent
          (right.iidSamples 0) |>.2
        rw [left.iidSamples_zero, right.iidSamples_zero]
        exact EvaluationEquivalent.refl (Distribution.pure [])
      rw [zero, Nat.cast_zero, zero_mul]
  | count + 1 => by
      rw [left.iidSamples_succ, right.iidSamples_succ]
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
        _ ≤ left.totalVariationDistance right +
            (left.iidSamples count).totalVariationDistance
              (right.iidSamples count) :=
          left.totalVariationDistance_product_le_add right
            (left.iidSamples count) (right.iidSamples count)
        _ ≤ left.totalVariationDistance right +
            (count : Fraction.Rational) * left.totalVariationDistance right :=
          Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
            (iidSamples_totalVariationDistance_le left right count)
        _ = ((count + 1 : Nat) : Fraction.Rational) *
            left.totalVariationDistance right := by
          rw [Fraction.Cast.natCast_add_direct, Nat.cast_one]
          ring1

end Distribution

end Purelib.Measure

end
