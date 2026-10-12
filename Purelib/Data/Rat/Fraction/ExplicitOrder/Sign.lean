module
import Purelib.Algebra.Field.ExplicitOrder.Basic
public import Purelib.Algebra.Field.ExplicitOrder.Sign
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Algebra.Ring.Multiplication
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Algebra

open Purelib.Data.Rat

section
public section
namespace Purelib.Data.Rat.Fraction.ExplicitOrder.Sign
variable {F : Type*} [Purelib.Algebra.Field.ExplicitOrder.Sign.RayOrderedExplicitField F]
/-- Use the retained explicit ordered-field equality decision for the local field variable. -/
local instance : DecidableEq F := Field.ExplicitOrder.Basic.OrderedExplicitField.eq_decidable
namespace RationalRayModel

/-- Equip canonical rationals with the explicit sign-splitting ordered-field interface.

The stored witnesses use the concrete canonical comparison, direct product positivity and positive reciprocal theorem.
Nonzero inputs receive an explicit positive-or-negative split. -/
instance : Field.ExplicitOrder.Sign.RayOrderedExplicitField Fraction.Rational where
  toOrderedExplicitField :=
    { toExplicitField := inferInstance
      toLT := inferInstance
      eq_decidable := inferInstance
      zero_lt_one_direct :=
        Fraction.Cast.Order.natCast_pos_direct (n := 1) (by decide)
      add_pos_direct := by
        intro left right leftPositive rightPositive
        exact Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct
          leftPositive rightPositive.le
      mul_pos_direct := Fraction.Order.Arithmetic.mul_pos_direct
      mul_self_pos_direct := by
        intro value valueNonzero
        rcases lt_trichotomy value 0 with negative | zero | positive
        · have negatedPositive : 0 < -value := by
            have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct negative (-value)
            simpa only [Fraction.Field.zero_add, Fraction.neg_add_cancel, _root_.add_neg_cancel, -eq_self, -iff_self]
              using shifted
          have productPositive := Fraction.Order.Arithmetic.mul_pos_direct
            negatedPositive negatedPositive
          simpa only [Purelib.Algebra.Ring.Multiplication.neg_mul_neg, -eq_self, -iff_self] using productPositive
        · exact (valueNonzero zero).elim
        · exact Fraction.Order.Arithmetic.mul_pos_direct positive positive
      inv_pos_direct := Fraction.Order.Field.inv_pos_direct }
  positive_ne_zero_direct := by
    intro value positive
    exact ne_of_gt positive
  positive_neg_exclusive_direct := by
    intro value positive negativePositive
    have negative : value < 0 := by
      have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct negativePositive value
      simpa only [Fraction.Field.zero_add, Fraction.neg_add_cancel, _root_.add_neg_cancel, -eq_self, -iff_self] using
        shifted
    exact lt_asymm positive negative
  sign_split_direct := by
    intro value valueNonzero
    rcases lt_trichotomy value 0 with negative | zero | positive
    · apply Or.inr
      have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct negative (-value)
      simpa only [Fraction.Field.zero_add, Fraction.neg_add_cancel, _root_.add_neg_cancel, -eq_self, -iff_self] using
        shifted
    · exact (valueNonzero zero).elim
    · exact Or.inl positive
end RationalRayModel
end Purelib.Data.Rat.Fraction.ExplicitOrder.Sign

end
