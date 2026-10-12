module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Content
public import Purelib.Measure.Distribution.EssentialMaximum.Basic
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Lp.AlmostEverywhere
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Content.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Content.Pushforward.EssentialMaximum

section
/-!
# Finite pushforward laws for powered Lp and essential maxima

An executable pushforward retains every displayed source row and merely
changes its payload.  Consequently rational L1, natural-powered Lp, finite
almost-everywhere equality, and computed essential maxima all obey exact
change-of-variables laws.  No quotient function space or measurable-map
side condition is needed on a displayed finite table.
-/

public section

namespace Purelib.Measure
namespace Distribution

open Purelib
open Purelib.Data.Rat
/-- An observable's pushforward essential maximum equals its pullback essential maximum under the original distribution.
-/
theorem map_essentialMaximumMagnitude {α β : Type}
    (source : Measure.Distribution α) (function : α → β)
    (value : β → Fraction.Rational) :
    (source.map function).essentialMaximumMagnitude value =
      source.essentialMaximumMagnitude
        (fun item => value (function item)) := by
  unfold essentialMaximumMagnitude
  rw [source.map_toContent function]
  exact source.toContent.map_essentialMaximumMagnitude function value

/-- Two observables' pushforward essential distance equals the distance of their pullbacks under the original
distribution. -/
theorem map_essentialMaximumDistance {α β : Type}
    (source : Measure.Distribution α) (function : α → β)
    (left right : β → Fraction.Rational) :
    (source.map function).essentialMaximumDistance left right =
      source.essentialMaximumDistance
        (fun item => left (function item))
        (fun item => right (function item)) := by
  unfold essentialMaximumDistance
  rw [source.map_toContent function]
  exact source.toContent.map_essentialMaximumDistance
    function left right

/-- Two observables agree almost everywhere under the pushforward exactly when their pullbacks agree under the original
distribution. -/
theorem map_equalAlmostEverywhere_iff {α β : Type}
    (source : Measure.Distribution α) (function : α → β)
    (left right : β → Fraction.Rational) :
    (source.map function).EqualAlmostEverywhere left right ↔
      source.EqualAlmostEverywhere
        (fun item => left (function item))
        (fun item => right (function item)) := by
  constructor
  · intro equal
    have distanceZero := ((source.map function).essentialMaximumDistance_eq_zero_iff left right).mpr equal
    rw [source.map_essentialMaximumDistance] at distanceZero
    exact (source.essentialMaximumDistance_eq_zero_iff
      (fun item => left (function item)) (fun item => right (function item))).mp distanceZero
  · intro equal
    have distanceZero := (source.essentialMaximumDistance_eq_zero_iff
      (fun item => left (function item)) (fun item => right (function item))).mpr equal
    rw [← source.map_essentialMaximumDistance function left right] at distanceZero
    exact ((source.map function).essentialMaximumDistance_eq_zero_iff left right).mp distanceZero

end Distribution

end Purelib.Measure

end
