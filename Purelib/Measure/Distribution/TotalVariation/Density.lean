module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Density
import Purelib.Measure.Distribution.Density.Difference
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Lp.L1
public import Purelib.Measure.Distribution.TotalVariation.Basic
import Purelib.Measure.Event.RationalOrder
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.PositiveNegativePart
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Finite Scheffé identities

Two nonnegative rational densities of expectation one define finite
reweighted probability laws.  The executable event where the first density
dominates the second attains their event-probability discrepancy.  Its mass is
the integral of the positive density difference, which equals the negative
part because both densities normalise.  Consequently atomic total variation
is exactly half the original-law L1 density separation.
-/

namespace Purelib.Measure
namespace Distribution

open Purelib in
open Purelib.Data.Rat in
/-- Total variation between normalized nonnegative reweightings is the expected positive density difference.

Both densities have unit expectation under the same original finite law, whose atoms and weights determine the
positive-part integral. -/
theorem totalVariationDistance_reweight_eq_positivePart
    {α : Type} [DecidableEq α] (source : Distribution α)
    (first second : α → Fraction.Rational)
    (firstNonnegative : ∀ item, 0 ≤ first item)
    (secondNonnegative : ∀ item, 0 ≤ second item)
    (firstNormalizes : source.expectation first = 1)
    (secondNormalizes : source.expectation second = 1) :
    (source.reweight first firstNonnegative firstNormalizes).totalVariationDistance
          (source.reweight second secondNonnegative secondNormalizes) =
      source.expectation (fun item =>
        Data.Rat.positiveWeight (first item - second item)) := by
  let firstLaw := source.reweight first firstNonnegative firstNormalizes
  let secondLaw := source.reweight second secondNonnegative secondNormalizes
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · let event := firstLaw.totalVariationEvent secondLaw
    calc
      firstLaw.totalVariationDistance secondLaw =
          firstLaw.probability event - secondLaw.probability event :=
        (firstLaw.probability_sub_at_totalVariationEvent secondLaw).symm
      _ ≤ source.expectation (fun item =>
          Data.Rat.positiveWeight (first item - second item)) :=
        source.reweight_probability_sub_le_positivePart first second
          firstNonnegative secondNonnegative firstNormalizes secondNormalizes
          event
  · let event := densityDominanceEvent first second
    calc
      source.expectation (fun item =>
            Data.Rat.positiveWeight (first item - second item)) =
          firstLaw.probability event - secondLaw.probability event :=
        (source.reweight_probability_sub_densityDominanceEvent first second
          firstNonnegative secondNonnegative firstNormalizes
          secondNormalizes).symm
      _ ≤ Distance.rationalSeparation (firstLaw.probability event)
          (secondLaw.probability event) := Fraction.Order.Basic.le_max_left _ _
      _ ≤ firstLaw.totalVariationDistance secondLaw :=
        firstLaw.probability_separation_le_totalVariationDistance
          secondLaw event

open Purelib.Data.Rat in
/-- The original law's L1 distance between two normalized nonnegative densities is twice their reweighted total
variation. -/
theorem l1Distance_eq_two_mul_totalVariationDistance_reweight
    {α : Type} [DecidableEq α] (source : Distribution α)
    (first second : α → Fraction.Rational)
    (firstNonnegative : ∀ item, 0 ≤ first item)
    (secondNonnegative : ∀ item, 0 ≤ second item)
    (firstNormalizes : source.expectation first = 1)
    (secondNormalizes : source.expectation second = 1) :
    source.l1Distance first second =
      2 * (source.reweight first firstNonnegative firstNormalizes).totalVariationDistance
          (source.reweight second secondNonnegative secondNormalizes) := by
  rw [source.l1Distance_eq_expectation_positivePart_add_negativePart
      first second,
    ← source.expectation_positivePart_eq_negativePart_of_normalized
      first second firstNormalizes secondNormalizes,
    source.totalVariationDistance_reweight_eq_positivePart first second
      firstNonnegative secondNonnegative firstNormalizes secondNormalizes]
  ring1

end Distribution

end Purelib.Measure

end
