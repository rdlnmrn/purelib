module
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
public section

/-! # Coordinate bounds from Gaussian squared magnitude

A strict squared-magnitude bound controls the imaginary coordinate between the
signed endpoints of the supplied positive rational radius. -/

namespace Purelib.Data.Gaussian.Norm.Components.Bounds

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A positive radius and a strict norm-square bound place the imaginary coordinate strictly between the signed radius
endpoints. -/
theorem imaginary_bounds_of_normSq_lt_sq
    {delta : Basic.Canonical} {radius : Fraction.Rational} (radiusPositive : 0 < radius)
    (distance : Basic.normSq delta < radius ^ 2) :
    -radius < delta.im /\ delta.im < radius := by
  have imaginarySquare : delta.im ^ 2 < radius ^ 2 :=
    (show delta.im ^ 2 <= delta.re ^ 2 + delta.im ^ 2 from
      le_add_of_nonneg_left
        (Fraction.Order.Arithmetic.sq_nonneg_direct delta.re)).trans_lt
      distance
  have upper := Bounds.Square.lt_of_sq_lt_sq_of_nonneg
    radiusPositive.le imaginarySquare
  have negativeUpper := Bounds.Square.lt_of_sq_lt_sq_of_nonneg
    radiusPositive.le (a := -delta.im) (by
      calc
        (-delta.im) ^ 2 = delta.im ^ 2 := by ring1
        _ < radius ^ 2 := imaginarySquare)
  exact
    ⟨by
      have negated := Fraction.Order.Arithmetic.neg_lt_neg_direct negativeUpper
      simpa only [neg_neg] using negated,
    upper⟩

end Purelib.Data.Gaussian.Norm.Components.Bounds

end
