module
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Distribution.Conditioning.Covariance.Basic
import Purelib.Measure.Distribution.Basic
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
import Purelib.Measure.Distribution.Lp.L2
public import Purelib.Measure.Distribution.Conditioning.Moments
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Distribution.Conditioning.Basic
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

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

open Purelib
open Purelib.Data.Rat
/-- On a positive-probability event, the squared conditional product mean is bounded by the product of conditional
square means. -/
theorem conditionalMean_mul_sq_le {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Fraction.Rational) :
    distribution.conditionalMean event
          (fun item => left item * right item) ^ 2 ≤
      distribution.conditionalMean event (fun item => left item ^ 2) *
        distribution.conditionalMean event (fun item => right item ^ 2) := by
  have bounded := (distribution.conditioned event positive)
    |>.productExpectation_sq_le_poweredL2_mul left right
  change (distribution.conditioned event positive).expectation
        (fun item => left item * right item) ^ 2 ≤
      (distribution.conditioned event positive).expectation
          (fun item => left item ^ 2) *
        (distribution.conditioned event positive).expectation
          (fun item => right item ^ 2) at bounded
  rw [distribution.conditioned_expectation_eq_conditionalMean
      event positive (fun item => left item * right item),
    distribution.conditioned_expectation_eq_conditionalMean
      event positive (fun item => left item ^ 2),
    distribution.conditioned_expectation_eq_conditionalMean
      event positive (fun item => right item ^ 2)] at bounded
  exact bounded

/-- On a positive-probability event, squared conditional covariance is bounded by the product of the two conditional
variances. -/
theorem conditionalCovariance_sq_le_variance_mul {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Fraction.Rational) :
    distribution.conditionalCovariance event left right ^ 2 ≤
      distribution.conditionalVariance event left *
        distribution.conditionalVariance event right := by
  exact distribution.conditionalMean_mul_sq_le event positive
    (fun item => left item - distribution.conditionalMean event left)
    (fun item => right item - distribution.conditionalMean event right)

end Distribution

namespace PositiveEventPartition
end PositiveEventPartition

end Purelib.Measure

end
