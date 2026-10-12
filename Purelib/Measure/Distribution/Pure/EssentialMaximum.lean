module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.EssentialMaximum.Basic
public import Purelib.Measure.Distribution.EssentialMaximum.Basic
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Weighted.EssentialMaximum
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Content.Basic
import Purelib.Measure.Distribution.Content
import Purelib.Data.Rat.Fraction.Arithmetic

section
/-!
# Lp quantities of one-point finite distributions

The one-point distribution is the base constructor for finite bind and
sampling.  All powered and essential-maximum quantities reduce exactly to
the displayed rational value at that point.
-/

public section

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat
/-- A pure distribution's essential maximum is the observable magnitude at its sole payload. -/
@[simp] theorem pure_essentialMaximumMagnitude {α : Type} (item : α)
    (value : α → Fraction.Rational) :
    (Distribution.pure item).essentialMaximumMagnitude value =
      Distance.rationalSeparation (value item) 0 := by
  unfold Distribution.essentialMaximumMagnitude
    Content.essentialMaximumMagnitude Distribution.toContent
    Distribution.pure
  have oneNonzero : (1 : Fraction.Rational) ≠ 0 := by decide
  simp only [-eq_self, -iff_self, essentialMaximumMagnitudeOn, if_neg oneNonzero]
  exact Fraction.Order.Basic.max_eq_left (Distance.rationalSeparation_nonneg _ _)

/-- A pure distribution's essential maximum distance is the observable separation at its sole payload. -/
@[simp] theorem pure_essentialMaximumDistance {α : Type} (item : α)
    (left right : α → Fraction.Rational) :
    (Distribution.pure item).essentialMaximumDistance left right =
      Distance.rationalSeparation (left item) (right item) := by
  change (Distribution.pure item).essentialMaximumMagnitude
    (fun point => left point - right point) = _
  rw [Distribution.pure_essentialMaximumMagnitude]
  exact (Distance.rationalSeparation_eq_sub_zero (left item) (right item)).symm

end Distribution

end Purelib.Measure

end
