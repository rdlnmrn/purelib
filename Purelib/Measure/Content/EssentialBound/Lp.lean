module
import Purelib.Measure.Content.Lp.L1
import Purelib.Measure.Content.Lp.Natural
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.EssentialBound.Basic
import Purelib.Measure.Content.Integral
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Finite essential bounds

An essential bound may fail only at displayed zero-weight atoms.  This is the
finite rational replacement for an essential supremum: the bound itself is
explicit data, so no supremum or completed value is selected.
-/

namespace Purelib.Measure
namespace Content

open Purelib.Data.Rat
/-- An essential magnitude ceiling bounds the magnitude integral by total mass times that ceiling. -/
theorem poweredL1_le_of_essentialBound {α : Type}
    (content : Content α) (value : α → Fraction.Rational)
    (ceiling : Fraction.Rational)
    (bounded : content.EssentiallyBoundedBy value ceiling) :
    content.poweredL1 value ≤ content.total * ceiling := by
  calc
    content.poweredL1 value ≤ content.integral (fun _ => ceiling) :=
      content.integral_mono_off_zero _ _ bounded
    _ = content.total * ceiling := content.integral_constant ceiling

/-- An essential magnitude ceiling bounds each natural-powered integral by total mass times that ceiling's power. -/
theorem poweredLp_le_of_essentialBound {α : Type}
    (content : Content α) (exponent : Nat)
    (value : α → Fraction.Rational) (ceiling : Fraction.Rational)
    (bounded : content.EssentiallyBoundedBy value ceiling) :
    content.poweredLp exponent value ≤
      content.total * ceiling ^ exponent := by
  calc
    content.poweredLp exponent value ≤
        content.integral (fun _ => ceiling ^ exponent) := by
      apply content.integral_mono_off_zero
      intro atom member
      rcases bounded atom member with zero | bound
      · exact Or.inl zero
      · exact Or.inr (Fraction.Order.Arithmetic.pow_le_pow_direct
          (Distance.rationalSeparation_nonneg _ _) bound exponent)
    _ = content.total * ceiling ^ exponent :=
      content.integral_constant (ceiling ^ exponent)

/-- An essential magnitude ceiling for the right factor bounds the product's magnitude integral by that ceiling times
the left magnitude integral. -/
theorem poweredL1_mul_le_of_right_essentialBound {α : Type}
    (content : Content α) (left right : α → Fraction.Rational)
    (ceiling : Fraction.Rational)
    (bounded : content.EssentiallyBoundedBy right ceiling) :
    content.poweredL1 (fun item => left item * right item) ≤
      ceiling * content.poweredL1 left := by
  unfold poweredL1
  calc
    content.integral (fun item =>
          Distance.rationalSeparation (left item * right item) 0) =
        content.integral (fun item =>
          Distance.rationalSeparation (left item) 0 *
            Distance.rationalSeparation (right item) 0) := by
      exact content.integral_congr _ _ (fun item =>
        Distance.rationalSeparation_mul_zero (left item) (right item))
    _ ≤ content.integral (fun item =>
          Distance.rationalSeparation (left item) 0 * ceiling) := by
      apply content.integral_mono_off_zero
      intro atom member
      rcases bounded atom member with zero | bound
      · exact Or.inl zero
      · exact Or.inr
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            bound (Distance.rationalSeparation_nonneg _ _))
    _ = ceiling * content.integral (fun item =>
          Distance.rationalSeparation (left item) 0) := by
      calc
        content.integral (fun item =>
            Distance.rationalSeparation (left item) 0 * ceiling) =
            content.integral (fun item =>
              ceiling * Distance.rationalSeparation (left item) 0) :=
          content.integral_congr _ _ (fun item => by ring1)
        _ = ceiling * content.integral (fun item =>
            Distance.rationalSeparation (left item) 0) := content.integral_scale _ _

end Content

namespace Distribution
end Distribution

end Purelib.Measure

end
