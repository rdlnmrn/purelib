module
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
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

open Purelib.Data.Rat in
/-- Take the conditional mean of the product of the two observables centered at their respective conditional means.

The original law and Boolean event determine all three conditional means; positivity is imposed only on results
requiring a normalized conditional law. -/
def conditionalCovariance {α : Type} (distribution : Distribution α)
    (event : α → Bool) (left right : α → Fraction.Rational) : Fraction.Rational :=
  distribution.conditionalMean event fun item =>
    (left item - distribution.conditionalMean event left) *
      (right item - distribution.conditionalMean event right)

open Purelib.Data.Rat in
open Purelib.Measure in
/-- On a positive-probability event, conditional covariance equals conditional product mean minus the product of
conditional means. -/
theorem conditionalCovariance_eq_product_sub_mul {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Fraction.Rational) :
    distribution.conditionalCovariance event left right =
      distribution.conditionalMean event
          (fun item => left item * right item) -
        distribution.conditionalMean event left *
          distribution.conditionalMean event right := by
  unfold Distribution.conditionalCovariance
  let leftMean := distribution.conditionalMean event left
  let rightMean := distribution.conditionalMean event right
  have expansion : distribution.conditionalMean event (fun item =>
      (left item - leftMean) * (right item - rightMean)) =
      distribution.conditionalMean event (fun item =>
        left item * right item - leftMean * right item -
          rightMean * left item + leftMean * rightMean) :=
    distribution.conditionalMean_congr event _ _ (fun item => by ring1)
  rw [expansion, distribution.conditionalMean_add,
    distribution.conditionalMean_sub, distribution.conditionalMean_sub,
    distribution.conditionalMean_scale,
    distribution.conditionalMean_scale,
    distribution.conditionalMean_constant event positive]
  dsimp only [leftMean, rightMean]
  ring1
end Distribution

namespace PositiveEventPartition
end PositiveEventPartition

end Purelib.Measure

end

end

section
@[expose] public section

/-!
# Finite law of total covariance

For a displayed positive event partition, exact covariance splits into the
weighted within-cell conditional covariances and the covariance of the
displayed conditional means.  The proof is finite linearity over the listed
partition cells.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat in
/-- On a positive-probability event, the globally centered product mean splits into conditional covariance and the
product of conditional mean offsets. -/
public theorem conditionalMean_centeredProduct {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Fraction.Rational) :
    distribution.conditionalMean event (fun item =>
        (left item - distribution.expectation left) *
          (right item - distribution.expectation right)) =
      distribution.conditionalCovariance event left right +
        (distribution.conditionalMean event left -
          distribution.expectation left) *
        (distribution.conditionalMean event right -
          distribution.expectation right) := by
  let leftMean := distribution.expectation left
  let rightMean := distribution.expectation right
  rw [distribution.conditionalCovariance_eq_product_sub_mul
      event positive left right]
  change distribution.conditionalMean event (fun item =>
      (left item - leftMean) * (right item - rightMean)) = _
  calc
    distribution.conditionalMean event (fun item =>
          (left item - leftMean) * (right item - rightMean)) =
        distribution.conditionalMean event (fun item =>
          (left item * right item - leftMean * right item) -
            rightMean * left item + leftMean * rightMean) :=
      distribution.conditionalMean_congr event _ _
        (fun item => by ring1)
    _ = _ := by
      rw [distribution.conditionalMean_add,
        distribution.conditionalMean_sub,
        distribution.conditionalMean_sub,
        distribution.conditionalMean_scale,
        distribution.conditionalMean_scale,
        distribution.conditionalMean_constant event positive]
      dsimp only [leftMean, rightMean]
      ring1

end Distribution

end Purelib.Measure

end
