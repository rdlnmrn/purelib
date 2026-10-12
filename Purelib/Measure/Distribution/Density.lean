module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Weighted.Density
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic

section
@[expose] public section

/-!
# Finite rational change of measure

A rational density reweights a displayed finite atom list by multiplication.
The resulting change-of-measure identities are exact finite sums.  There is
no almost-everywhere quotient, measurable function space, or Radon--Nikodym
existence theorem.
-/

namespace Purelib.Measure
namespace Content
end Content

namespace Distribution

open Purelib.Data.Rat
/-- Multiply each original occurrence weight by the supplied nonnegative density with expectation one.

Retain the original payload order and occurrence multiplicities. The density normalization certificate proves unit total
for this exact reweighted list. -/
def reweight {α : Type} (distribution : Distribution α)
    (density : α → Fraction.Rational) (nonnegative : ∀ item, 0 ≤ density item)
    (normalizes : distribution.expectation density = 1) : Distribution α where
  atoms := densityAtoms density nonnegative distribution.atoms
  total_one := by
    rw [totalWeight_densityAtoms]
    exact normalizes

/-- The reweighted event probability is the original expectation of density times its indicator. -/
theorem reweight_probability {α : Type} (distribution : Distribution α)
    (density : α → Fraction.Rational) (nonnegative : ∀ item, 0 ≤ density item)
    (normalizes : distribution.expectation density = 1)
    (event : α → Bool) :
    (distribution.reweight density nonnegative normalizes).probability event =
      distribution.expectation
        (fun item => density item * indicator event item) :=
  eventWeight_densityAtoms distribution.atoms density nonnegative event

/-- The reweighted observable expectation is the original expectation of density times that observable. -/
theorem reweight_expectation {α : Type} (distribution : Distribution α)
    (density : α → Fraction.Rational) (nonnegative : ∀ item, 0 ≤ density item)
    (normalizes : distribution.expectation density = 1)
    (value : α → Fraction.Rational) :
    (distribution.reweight density nonnegative normalizes).expectation value =
      distribution.expectation
        (fun item => density item * value item) :=
  expectationWeight_densityAtoms distribution.atoms density value nonnegative

end Distribution

end Purelib.Measure

end
