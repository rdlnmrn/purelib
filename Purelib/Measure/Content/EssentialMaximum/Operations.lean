module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Density.Basic
public import Purelib.Measure.Content.EssentialMaximum.Basic
import Purelib.Measure.Content.Operations
import Purelib.Measure.Weighted.EssentialMaximum
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Event
import Purelib.Measure.Content.Density.Aligned
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Transform
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
namespace Content

section
open Purelib
open Purelib.Data.Rat
/-- Appending contents takes the maximum of their two essential maximum magnitudes. -/
theorem append_essentialMaximumMagnitude {α : Type}
    (left right : Measure.Content α) (value : α → Fraction.Rational) :
    (left.append right).essentialMaximumMagnitude value =
      max (left.essentialMaximumMagnitude value)
        (right.essentialMaximumMagnitude value) :=
  Measure.essentialMaximumMagnitudeOn_append value left.atoms right.atoms

/-- Appending contents takes the maximum of their two essential maximum distances. -/
theorem append_essentialMaximumDistance {α : Type}
    (left right : Measure.Content α) (first second : α → Fraction.Rational) :
    (left.append right).essentialMaximumDistance first second =
      max (left.essentialMaximumDistance first second)
        (right.essentialMaximumDistance first second) := by
  unfold essentialMaximumDistance
  exact left.append_essentialMaximumMagnitude right
    (fun item => first item - second item)

/-- Scaling all content weights by zero makes every essential maximum magnitude vanish. -/
theorem scale_essentialMaximumMagnitude_of_eq_zero {α : Type}
    (content : Measure.Content α) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor) (factorZero : factor = 0)
    (value : α → Fraction.Rational) :
    (content.scale factor factorNonnegative).essentialMaximumMagnitude value =
      0 :=
  Measure.essentialMaximumMagnitudeOn_scaleAtoms_of_eq_zero value factor
    factorNonnegative factorZero content.atoms

/-- Scaling all content weights by a nonnegative nonzero factor preserves essential maximum magnitude. -/
theorem scale_essentialMaximumMagnitude_of_ne {α : Type}
    (content : Measure.Content α) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor) (factorNonzero : factor ≠ 0)
    (value : α → Fraction.Rational) :
    (content.scale factor factorNonnegative).essentialMaximumMagnitude value =
      content.essentialMaximumMagnitude value :=
  Measure.essentialMaximumMagnitudeOn_scaleAtoms_of_ne value factor
    factorNonnegative factorNonzero content.atoms

/-- Nonnegative scaling of content weights cannot increase essential maximum magnitude. -/
theorem scale_essentialMaximumMagnitude_le {α : Type}
    (content : Measure.Content α) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor) (value : α → Fraction.Rational) :
    (content.scale factor factorNonnegative).essentialMaximumMagnitude value ≤
      content.essentialMaximumMagnitude value := by
  by_cases factorZero : factor = 0
  · rw [content.scale_essentialMaximumMagnitude_of_eq_zero factor
      factorNonnegative factorZero value]
    exact content.essentialMaximumMagnitude_nonnegative value
  · rw [content.scale_essentialMaximumMagnitude_of_ne factor
      factorNonnegative factorZero value]

/-- Nonnegative scaling of content weights cannot increase essential maximum distance. -/
theorem scale_essentialMaximumDistance_le {α : Type}
    (content : Measure.Content α) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor) (first second : α → Fraction.Rational) :
    (content.scale factor factorNonnegative).essentialMaximumDistance
        first second ≤
      content.essentialMaximumDistance first second := by
  unfold essentialMaximumDistance
  exact content.scale_essentialMaximumMagnitude_le factor
    factorNonnegative (fun item => first item - second item)

/-- Restricting the exact content to a Boolean event cannot increase essential maximum magnitude. -/
theorem restrict_essentialMaximumMagnitude_le {α : Type}
    (content : Measure.Content α) (event : α → Bool)
    (value : α → Fraction.Rational) :
    (content.restrict event).essentialMaximumMagnitude value ≤
      content.essentialMaximumMagnitude value := by
  apply (content.restrict event).essentialMaximumMagnitude_le value
    (content.essentialMaximumMagnitude value)
    (content.essentialMaximumMagnitude_nonnegative value)
  intro atom member
  exact content.essentiallyBoundedBy_essentialMaximumMagnitude value atom
    (Measure.mem_restrictAtoms content.atoms event atom member)

/-- Restricting the exact content to a Boolean event cannot increase essential maximum distance. -/
theorem restrict_essentialMaximumDistance_le {α : Type}
    (content : Measure.Content α) (event : α → Bool)
    (left right : α → Fraction.Rational) :
    (content.restrict event).essentialMaximumDistance left right ≤
      content.essentialMaximumDistance left right := by
  unfold essentialMaximumDistance
  exact content.restrict_essentialMaximumMagnitude_le event
    (fun item => left item - right item)

/-- Reweighting the exact content by a nonnegative density cannot increase essential maximum magnitude. -/
theorem reweight_essentialMaximumMagnitude_le {α : Type}
    (content : Measure.Content α) (density : α → Fraction.Rational)
    (densityNonnegative : ∀ item, 0 ≤ density item)
    (value : α → Fraction.Rational) :
    (content.reweight density densityNonnegative).essentialMaximumMagnitude
        value ≤
      content.essentialMaximumMagnitude value := by
  apply (content.reweight density densityNonnegative)
    |>.essentialMaximumMagnitude_le value
      (content.essentialMaximumMagnitude value)
      (content.essentialMaximumMagnitude_nonnegative value)
  exact Measure.essentiallyBoundedByOn_densityAtoms density densityNonnegative
    value (content.essentialMaximumMagnitude value) content.atoms
      (content.essentiallyBoundedBy_essentialMaximumMagnitude value)

/-- Reweighting the exact content by a nonnegative density cannot increase essential maximum distance. -/
theorem reweight_essentialMaximumDistance_le {α : Type}
    (content : Measure.Content α) (density : α → Fraction.Rational)
    (densityNonnegative : ∀ item, 0 ≤ density item)
    (left right : α → Fraction.Rational) :
    (content.reweight density densityNonnegative).essentialMaximumDistance
        left right ≤
      content.essentialMaximumDistance left right := by
  unfold essentialMaximumDistance
  exact content.reweight_essentialMaximumMagnitude_le
    density densityNonnegative (fun item => left item - right item)

end

end Content

end Purelib.Measure

end
