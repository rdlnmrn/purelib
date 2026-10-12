module
import Purelib.Algebra.Field.Ratio
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Cast

open Purelib.Algebra

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10 rational examples

The two examples below retain the source's literal rational coordinates.  All
side matches and spread matches are explicit finite permutation witnesses.
-/

namespace Purelib.Data.Rat.Fraction.Field.Finite

/-- Distinct natural numbers have distinct canonical rational casts. -/
public theorem rational_natCast_ne {left right : Nat}
    (different : left ≠ right) : (left : Fraction.Rational) ≠ (right : Fraction.Rational) := by
  intro castsEqual
  exact different
    (Fraction.Cast.Compatibility.natCast_injective_direct castsEqual)

/-- Distinct natural numerators give distinct rational quotients over a common nonzero natural denominator. -/
public theorem rational_div_ne_div_same_denominator
    {left right denominator : Nat} (different : left ≠ right)
    (denominatorNonzero : denominator ≠ 0) :
    (left : Fraction.Rational) / denominator ≠ (right : Fraction.Rational) / denominator := by
  intro fractionsEqual
  have castDenominatorNonzero : (denominator : Fraction.Rational) ≠ 0 :=
    Fraction.Order.Cast.rational_natCast_nonzero denominatorNonzero
  have productsEqual := congrArg
    (fun value : Fraction.Rational => value * denominator) fractionsEqual
  rw [Field.ExplicitField.div_mul_cancel _ castDenominatorNonzero,
    Field.ExplicitField.div_mul_cancel _ castDenominatorNonzero] at productsEqual
  exact rational_natCast_ne different productsEqual

/-- Dividing a canonical rational by one leaves it unchanged. -/
public theorem rational_div_one (value : Fraction.Rational) : value / 1 =
  value := by
  have oneNonzero : (1 : Fraction.Rational) ≠ 0 :=
    fun oneZero => Fraction.Field.zero_ne_one oneZero.symm
  calc
    value / 1 = (value / 1) * 1 := by rw [mul_one]
    _ = value := Field.ExplicitField.div_mul_cancel value oneNonzero

/-- Products of natural-coordinate rational quotients agree when all denominators are nonzero and the cleared
cross-products agree.

The stated nonzero or positive denominator evidence justifies cancellation of the cleared denominator products. The
equality identifies the original canonical rational records. -/
public theorem rational_fraction_product_eq
    (a b c d e f g h : Nat)
    (bNonzero : b ≠ 0) (dNonzero : d ≠ 0)
    (fNonzero : f ≠ 0) (hNonzero : h ≠ 0)
    (crossProduct :
      ((a : Fraction.Rational) * c) * ((f : Fraction.Rational) * h) =
        ((e : Fraction.Rational) * g) * ((b : Fraction.Rational) * d)) :
    ((a : Fraction.Rational) / b) * (c / d) =
      ((e : Fraction.Rational) / f) * (g / h) := by
  calc
    ((a : Fraction.Rational) / b) * (c / d) =
        ((a : Fraction.Rational) * c) / ((b : Fraction.Rational) * d) :=
      Fraction.Field.div_mul_div_direct
        (a : Fraction.Rational) (b : Fraction.Rational) (c : Fraction.Rational) (d : Fraction.Rational)
    _ = ((e : Fraction.Rational) * g) / ((f : Fraction.Rational) * h) := by
      apply Field.Ratio.ratio_eq_of_cross_product
        (_root_.Purelib.Algebra.Field.ExplicitField.mul_ne_zero
          (Fraction.Order.Cast.rational_natCast_nonzero bNonzero)
          (Fraction.Order.Cast.rational_natCast_nonzero dNonzero))
        (_root_.Purelib.Algebra.Field.ExplicitField.mul_ne_zero
          (Fraction.Order.Cast.rational_natCast_nonzero fNonzero)
          (Fraction.Order.Cast.rational_natCast_nonzero hNonzero))
      exact crossProduct
    _ = ((e : Fraction.Rational) / f) * (g / h) :=
      (Fraction.Field.div_mul_div_direct
        (e : Fraction.Rational) (f : Fraction.Rational) (g : Fraction.Rational) (h : Fraction.Rational)).symm

end Purelib.Data.Rat.Fraction.Field.Finite

end
