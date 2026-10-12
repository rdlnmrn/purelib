module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Integral
public import Purelib.Measure.Weighted.Error
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Finite expectation stability

These estimates turn supplied pointwise rational error budgets into exact
finite expectation bounds.  A second form permits a larger error on one
displayed exceptional event and charges exactly its finite probability.
-/

namespace Purelib.Measure
namespace Distribution
end Distribution

namespace Content

open Purelib in
open Purelib.Data.Rat in
/-- Integration over the same finite content preserves pointwise subtraction. -/
theorem integral_sub {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) :
    content.integral (fun item => left item - right item) =
      content.integral left - content.integral right :=
  Measure.expectationWeight_sub content.atoms left right

open Purelib.Data.Rat
/-- A pointwise allowance on the exact content atoms bounds both signed differences of the two integrals by its
integral. -/
theorem integral_symmetricError {α : Type} (content : Content α)
    (allowance left right : α → Fraction.Rational)
    (bounded : SymmetricErrorOn content.atoms allowance left right) :
    content.integral right - content.integral left ≤
        content.integral allowance ∧
      content.integral left - content.integral right ≤
        content.integral allowance := by
  constructor
  · have averaged := content.integral_mono
      (fun item => right item - left item) allowance
      (fun atom member => (bounded atom member).1)
    rw [content.integral_sub] at averaged
    exact averaged
  · have averaged := content.integral_mono
      (fun item => left item - right item) allowance
      (fun atom member => (bounded atom member).2)
    rw [content.integral_sub] at averaged
    exact averaged

/-- A uniform pointwise error allowance bounds both signed integral differences by total content mass times that
allowance. -/
theorem integral_close_of_uniform {α : Type} (content : Content α)
    (epsilon : Fraction.Rational) (left right : α → Fraction.Rational)
    (bounded : SymmetricErrorOn content.atoms
      (fun _ => epsilon) left right) :
    content.integral right - content.integral left ≤
        content.total * epsilon ∧
      content.integral left - content.integral right ≤
        content.total * epsilon := by
  have averaged := content.integral_symmetricError
    (fun _ => epsilon) left right bounded
  rw [content.integral_constant] at averaged
  exact averaged

end Content

namespace Distribution
end Distribution

end Purelib.Measure

end
