module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Operations
import Purelib.Measure.Weighted.IntegralTransform
import Purelib.Measure.Weighted.Operations
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Exact integration against finite contents

A finite-content integral is an exact rational weighted sum.  The usual
linearity, monotonicity, indicator, restriction, and pushforward identities
are all finite list calculations.
-/

namespace Purelib.Measure
namespace Content

section
open Purelib.Data.Rat
/-- Sum the retained content weights times the rational observable at their exact payloads. -/
def integral {α : Type} (content : Content α)
    (value : α → Fraction.Rational) : Fraction.Rational :=
  Distribution.expectationWeight content.atoms value

/-- Pointwise equal observables have equal integrals over the same retained content. -/
theorem integral_congr {α : Type} (content : Content α)
    (left right : α → Fraction.Rational)
    (pointwise : ∀ item, left item = right item) :
    content.integral left = content.integral right :=
  Distribution.expectationWeight_congr content.atoms left right pointwise

/-- Scaling content weights scales every observable's integral by the same factor. -/
theorem scale_integral {α : Type} (content : Content α)
    (factor : Fraction.Rational) (nonnegative : 0 ≤ factor)
    (value : α → Fraction.Rational) :
    (content.scale factor nonnegative).integral value =
      factor * content.integral value :=
  expectationWeight_scaleAtoms factor nonnegative content.atoms value

/-- An integral over appended contents is the sum of the two original integrals. -/
theorem append_integral {α : Type} (left right : Content α)
    (value : α → Fraction.Rational) :
    (left.append right).integral value =
      left.integral value + right.integral value :=
  expectationWeight_append left.atoms right.atoms value

/-- The content integral preserves pointwise addition of rational observables. -/
theorem integral_add {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) :
    content.integral (fun item => left item + right item) =
      content.integral left + content.integral right :=
  Distribution.expectationWeight_add content.atoms left right

/-- A rational factor on the observable factors out of the content integral. -/
theorem integral_scale {α : Type} (content : Content α)
    (factor : Fraction.Rational) (value : α → Fraction.Rational) :
    content.integral (fun item => factor * value item) =
      factor * content.integral value :=
  Distribution.expectationWeight_scale content.atoms factor value

/-- An observable nonnegative on retained content occurrences has nonnegative integral. -/
theorem integral_nonneg {α : Type} (content : Content α)
    (value : α → Fraction.Rational)
    (nonnegative : ∀ atom, atom ∈ content.atoms → 0 ≤ value atom.item) :
    0 ≤ content.integral value :=
  Distribution.expectationWeight_nonneg content.atoms value nonnegative

/-- Pointwise comparison on retained content occurrences bounds their integrals. -/
theorem integral_mono {α : Type} (content : Content α)
    (lower upper : α → Fraction.Rational)
    (pointwise : ∀ atom, atom ∈ content.atoms →
      lower atom.item ≤ upper atom.item) :
    content.integral lower ≤ content.integral upper :=
  Distribution.expectationWeight_mono content.atoms lower upper pointwise

end

/-- Integrating a Boolean event's indicator gives its exact content measurement.

The original weighted indicator certificate identifies the integral and
event scans on the content's retained occurrences. No normalization or
identification of observable functions is required. -/
theorem integral_indicator {α : Type} (content : Content α)
    (event : α → Bool) :
    content.integral (Distribution.indicator event) = content.measure event :=
  Distribution.expectationWeight_indicator content.atoms event

open Purelib.Data.Rat
/-- Integrating a rational constant gives total content times that constant.

Every retained occurrence contributes its exact weight times the supplied
constant. The recursive tail equality and scalar distributivity identify
that same weighted sum with the original content total. -/
theorem integral_constant {α : Type} (content : Content α)
    (constant : Fraction.Rational) :
    content.integral (fun _ => constant) = content.total * constant := by
  unfold integral total
  induction content.atoms with
  | nil => exact (Fraction.Field.zero_mul_direct constant).symm
  | cons atom remaining ih =>
      change atom.weight * constant + Distribution.expectationWeight remaining (fun _ => constant) =
        (atom.weight + totalWeight remaining) * constant
      calc
        atom.weight * constant + Distribution.expectationWeight remaining (fun _ => constant) =
            atom.weight * constant + totalWeight remaining * constant :=
          congrArg (fun tail => atom.weight * constant + tail) ih
        _ = (atom.weight + totalWeight remaining) * constant := by ring1

/-- An integral over restricted content equals the original integral multiplied pointwise by its condition indicator. -/
theorem restrict_integral {α : Type} (content : Content α)
    (condition : α → Bool) (value : α → Fraction.Rational) :
    (content.restrict condition).integral value =
      content.integral (fun item =>
        Distribution.indicator condition item * value item) :=
  expectationWeight_restrictAtoms condition value content.atoms

/-- An integral over mapped content equals the original integral of the pulled-back observable. -/
theorem map_integral {α β : Type} (content : Content α)
    (function : α → β) (value : β → Fraction.Rational) :
    (content.map function).integral value =
      content.integral (fun item => value (function item)) :=
  expectationWeight_mapAtoms function value content.atoms

/-- A product of separate observables integrates over product content as the product of its original integrals. -/
theorem product_integral_mul {α β : Type}
    (left : Content α) (right : Content β)
    (leftValue : α → Fraction.Rational) (rightValue : β → Fraction.Rational) :
    (left.product right).integral
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.integral leftValue * right.integral rightValue :=
  expectationWeight_productAtoms_mul leftValue rightValue
    left.atoms right.atoms

/-- Integration over exact product content equals the nested left-then-right content integrals. -/
theorem product_integral {α β : Type}
    (left : Content α) (right : Content β)
    (value : α × β → Fraction.Rational) :
    (left.product right).integral value =
      left.integral (fun leftItem =>
        right.integral (fun rightItem => value (leftItem, rightItem))) :=
  expectationWeight_productAtoms value left.atoms right.atoms
end Content

end Purelib.Measure

end
