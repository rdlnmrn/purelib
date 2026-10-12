module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Distribution.Content
import Purelib.Measure.Weighted.EssentialBound
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
public import Purelib.Measure.Distribution.EssentialMaximum.Basic
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Content.Lp.L1
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Content.EssentialMaximum.Lp
import Purelib.Data.List.BinaryPrefix.Gauge
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Essential bounds under finite conditional expectation

Conditional averaging ignores displayed zero-weight rows and preserves every
explicit essential magnitude ceiling.  Consequently the computed finite
essential maximum cannot increase.  This is the constructive finite
`L∞`-contraction theorem; no supremum or completed function space is used.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib
open Purelib.Data.Rat
/-- A ceiling on all nonzero-weight original occurrences bounds the conditional mean on every positive-probability
event. -/
theorem conditionalMean_le_of_boundedAboveOffZeroWeightOn {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Fraction.Rational) (ceiling : Fraction.Rational)
    (bounded : BoundedAboveOffZeroWeightOn distribution.atoms value ceiling) :
    distribution.conditionalMean event value ≤ ceiling := by
  calc
    distribution.conditionalMean event value ≤
        distribution.conditionalMean event (fun _ => ceiling) :=
      distribution.conditionalMean_mono_off_zero event positive value
        (fun _ => ceiling) bounded
    _ = ceiling :=
      distribution.conditionalMean_constant event positive ceiling

/-- Event-integral separation is bounded by original event probability times the observables' essential maximum
distance. -/
theorem eventIntegral_separation_le_probability_mul_essentialMaximumDistance
    {α : Type} (distribution : Measure.Distribution α) (event : α → Bool)
    (left right : α → Fraction.Rational) :
    Distance.rationalSeparation (distribution.eventIntegral event left)
        (distribution.eventIntegral event right) ≤
      distribution.probability event *
        distribution.essentialMaximumDistance left right := by
  have expectationBound := distribution.expectation_separation_le_l1Distance
    (fun item => indicator event item * left item)
    (fun item => indicator event item * right item)
  change Distance.rationalSeparation (distribution.eventIntegral event left)
      (distribution.eventIntegral event right) ≤
    distribution.l1Distance
      (fun item => indicator event item * left item)
      (fun item => indicator event item * right item) at expectationBound
  have l1Identity :
      distribution.l1Distance
          (fun item => indicator event item * left item)
          (fun item => indicator event item * right item) =
        distribution.poweredL1
          (fun item => indicator event item * (left item - right item)) := by
    rw [← distribution.poweredL1_sub_eq_l1Distance]
    exact distribution.toContent.poweredL1_congr _ _
      (fun item => by ring1)
  have restrictedBound :=
    Content.poweredL1_indicator_mul_le_essentialMaximum_mul_measure
      distribution.toContent event
        (fun item => left item - right item)
  calc
    Distance.rationalSeparation (distribution.eventIntegral event left)
          (distribution.eventIntegral event right) ≤
        distribution.l1Distance
          (fun item => indicator event item * left item)
          (fun item => indicator event item * right item) := expectationBound
    _ = distribution.poweredL1
          (fun item => indicator event item * (left item - right item)) :=
      l1Identity
    _ ≤ distribution.essentialMaximumDistance left right *
          distribution.probability event := restrictedBound
    _ = distribution.probability event *
          distribution.essentialMaximumDistance left right := by
      ring1

/-- Conditional means on a positive-probability event are separated by at most the original essential maximum distance.
-/
theorem conditionalMean_separation_le_essentialMaximumDistance {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Fraction.Rational) :
    Distance.rationalSeparation (distribution.conditionalMean event left)
        (distribution.conditionalMean event right) ≤
      distribution.essentialMaximumDistance left right := by
  let probability := distribution.probability event
  let leftIntegral := distribution.eventIntegral event left
  let rightIntegral := distribution.eventIntegral event right
  let distance := distribution.essentialMaximumDistance left right
  have eventBound :
      Distance.rationalSeparation leftIntegral rightIntegral ≤
        probability * distance := by
    exact
      Distribution.eventIntegral_separation_le_probability_mul_essentialMaximumDistance
        distribution event left right
  have inversePositive : 0 < probability⁻¹ :=
    Fraction.Order.Field.inv_pos_direct positive
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    eventBound (Distance.rationalSeparation_nonneg probability⁻¹ 0)
  have inverseMagnitude :
      Distance.rationalSeparation probability⁻¹ 0 = probability⁻¹ :=
    Distance.rationalSeparation_zero_of_nonneg inversePositive.le
  unfold conditionalMean
  change Distance.rationalSeparation (leftIntegral / probability)
      (rightIntegral / probability) ≤ distance
  rw [Fraction.Field.div_eq_mul_inv_direct,
    Fraction.Field.div_eq_mul_inv_direct]
  calc
    Distance.rationalSeparation (leftIntegral * probability⁻¹)
          (rightIntegral * probability⁻¹) =
        Distance.rationalSeparation (probability⁻¹ * leftIntegral)
          (probability⁻¹ * rightIntegral) := by
      rw [mul_comm leftIntegral probability⁻¹,
        mul_comm rightIntegral probability⁻¹]
    _ = Distance.rationalSeparation probability⁻¹ 0 *
          Distance.rationalSeparation leftIntegral rightIntegral :=
      Distance.rationalSeparation_scale probability⁻¹ leftIntegral rightIntegral
    _ ≤ Distance.rationalSeparation probability⁻¹ 0 *
          (probability * distance) := scaled
    _ = distance := by
      rw [inverseMagnitude]
      calc
        probability⁻¹ * (probability * distance) =
            (probability⁻¹ * probability) * distance := by
          rw [mul_assoc]
        _ = distance := by
          rw [Fraction.Field.inv_mul_cancel probability
            positive.ne', one_mul]

end Distribution

namespace PositiveEventPartition
end PositiveEventPartition

end Purelib.Measure

end
