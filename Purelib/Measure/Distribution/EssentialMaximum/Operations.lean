module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Conditioning.Basic
import Purelib.Measure.Distribution.Density
public import Purelib.Measure.Distribution.EssentialMaximum.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Content.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Content.Density.Aligned
import Purelib.Measure.Distribution.Content
import Purelib.Measure.Content.EssentialMaximum.Operations
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
/-!
# Essential maxima under finite measure operations

Restriction and nonnegative reweighting can only remove nonzero rows from
the support relevant to the executable essential maximum.  Consequently
restriction, change of density, and positive-event conditioning are exact
finite `L∞` contractions.
-/

@[expose] public section

namespace Purelib.Measure

namespace Distribution

open Purelib
open Purelib.Data.Rat
/-- Normalized reweighting by a nonnegative density cannot increase essential maximum magnitude. -/
theorem reweight_essentialMaximumMagnitude_le {α : Type}
    (distribution : Measure.Distribution α) (density : α → Fraction.Rational)
    (densityNonnegative : ∀ item, 0 ≤ density item)
    (normalizes : distribution.expectation density = 1)
    (value : α → Fraction.Rational) :
    (distribution.reweight density densityNonnegative normalizes).essentialMaximumMagnitude
        value ≤
      distribution.essentialMaximumMagnitude value :=
  distribution.toContent.reweight_essentialMaximumMagnitude_le
    density densityNonnegative value

/-- Normalized reweighting by a nonnegative density cannot increase essential maximum distance. -/
theorem reweight_essentialMaximumDistance_le {α : Type}
    (distribution : Measure.Distribution α) (density : α → Fraction.Rational)
    (densityNonnegative : ∀ item, 0 ≤ density item)
    (normalizes : distribution.expectation density = 1)
    (left right : α → Fraction.Rational) :
    (distribution.reweight density densityNonnegative normalizes).essentialMaximumDistance
        left right ≤
      distribution.essentialMaximumDistance left right :=
  distribution.toContent.reweight_essentialMaximumDistance_le
    density densityNonnegative left right

/-- Conditioning on a positive-probability event cannot increase essential maximum magnitude. -/
theorem conditioned_essentialMaximumMagnitude_le {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Fraction.Rational) :
    (distribution.conditioned event positive).essentialMaximumMagnitude
        value ≤
      distribution.essentialMaximumMagnitude value := by
  unfold conditioned
  exact distribution.reweight_essentialMaximumMagnitude_le
    (distribution.conditioningDensity event positive)
    (distribution.conditioningDensity_nonnegative event positive)
    (distribution.conditioningDensity_normalizes event positive) value

/-- Conditioning on a positive-probability event cannot increase essential maximum distance. -/
theorem conditioned_essentialMaximumDistance_le {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Fraction.Rational) :
    (distribution.conditioned event positive).essentialMaximumDistance
        left right ≤
      distribution.essentialMaximumDistance left right := by
  unfold conditioned
  exact distribution.reweight_essentialMaximumDistance_le
    (distribution.conditioningDensity event positive)
    (distribution.conditioningDensity_nonnegative event positive)
    (distribution.conditioningDensity_normalizes event positive)
    left right

end Distribution

end Purelib.Measure

end
