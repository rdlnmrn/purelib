module
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Weighted.EssentialMaximum
import Purelib.Measure.Content.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.List.Event
public import Purelib.Measure.Content.EssentialMaximum.Basic
import Purelib.Measure.Content.Lp.AlmostEverywhere
import Purelib.Measure.Content.Operations

section
/-!
# Finite pushforward laws for powered Lp and essential maxima

An executable pushforward retains every displayed source row and merely
changes its payload.  Consequently rational L1, natural-powered Lp, finite
almost-everywhere equality, and computed essential maxima all obey exact
change-of-variables laws.  No quotient function space or measurable-map
side condition is needed on a displayed finite table.
-/

@[expose] public section

namespace Purelib.Measure
namespace Content

open Purelib in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- Essential maximum under mapped content equals the original essential maximum after composing the observable with the
exact payload map. -/
theorem map_essentialMaximumMagnitude {α β : Type}
    (content : Measure.Content α) (function : α → β)
    (value : β → Fraction.Rational) :
    (content.map function).essentialMaximumMagnitude value =
      content.essentialMaximumMagnitude
        (fun item => value (function item)) :=
  essentialMaximumMagnitudeOn_mapAtoms function value content.atoms

open Purelib
open Purelib.Data.Rat
/-- Essential maximum distance under mapped content equals the original distance of the two composed observables. -/
theorem map_essentialMaximumDistance {α β : Type}
    (content : Measure.Content α) (function : α → β)
    (left right : β → Fraction.Rational) :
    (content.map function).essentialMaximumDistance left right =
      content.essentialMaximumDistance
        (fun item => left (function item))
        (fun item => right (function item)) := by
  unfold essentialMaximumDistance
  exact content.map_essentialMaximumMagnitude function _

/-- Agreement away from zero-weight occurrences after mapping is equivalent to such agreement of the two composed
observables on original content. -/
theorem map_equalAlmostEverywhere_iff {α β : Type}
    (content : Measure.Content α) (function : α → β)
    (left right : β → Fraction.Rational) :
    (content.map function).EqualAlmostEverywhere left right ↔
      content.EqualAlmostEverywhere
        (fun item => left (function item))
        (fun item => right (function item)) := by
  constructor
  · intro equal
    have zero :=
      ((content.map function).essentialMaximumDistance_eq_zero_iff
        left right).mpr equal
    rw [content.map_essentialMaximumDistance function left right] at zero
    exact (content.essentialMaximumDistance_eq_zero_iff _ _).mp zero
  · intro equal
    apply ((content.map function).essentialMaximumDistance_eq_zero_iff
      left right).mp
    rw [content.map_essentialMaximumDistance function left right]
    exact (content.essentialMaximumDistance_eq_zero_iff _ _).mpr equal

end Content

end Purelib.Measure

end
