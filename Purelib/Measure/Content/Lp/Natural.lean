module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Integral
public import Purelib.Measure.Content.Lp.L1
public import Purelib.Measure.Content.Lp.L2
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

section
@[expose] public section

/-!
# Natural-powered finite Lp quantities

Natural powers of rational separation remain rational.  They provide exact
finite powered-Lp quantities and tail estimates without selecting roots or
constructing completed normed spaces.
-/

namespace Purelib.Measure
namespace Content

section
open Purelib.Data.Rat
/-- Integrate the natural power of an observable's rational magnitude over the retained finite content.

The exponent remains a natural parameter. In particular exponent zero returns total content mass, including at zero
observable values. -/
def poweredLp {α : Type} (content : Content α) (exponent : Nat)
    (value : α → Fraction.Rational) : Fraction.Rational :=
  content.integral fun item =>
    Distance.rationalSeparation (value item) 0 ^ exponent

/-- Integrate the natural power of the pointwise rational separation of two observables. -/
def poweredLpDistance {α : Type} (content : Content α)
    (exponent : Nat) (left right : α → Fraction.Rational) : Fraction.Rational :=
  content.integral fun item =>
    Distance.rationalSeparation (left item) (right item) ^ exponent

/-- Every natural-powered magnitude integral is nonnegative. -/
theorem poweredLp_nonnegative {α : Type} (content : Content α)
    (exponent : Nat) (value : α → Fraction.Rational) :
    0 ≤ content.poweredLp exponent value := by
  apply content.integral_nonneg
  intro atom member
  exact Fraction.Order.Arithmetic.pow_nonneg_direct
    (Distance.rationalSeparation_nonneg _ _) exponent

/-- Every natural-powered separation integral is nonnegative. -/
theorem poweredLpDistance_nonnegative {α : Type}
    (content : Content α) (exponent : Nat)
    (left right : α → Fraction.Rational) :
    0 ≤ content.poweredLpDistance exponent left right := by
  apply content.integral_nonneg
  intro atom member
  exact Fraction.Order.Arithmetic.pow_nonneg_direct
    (Distance.rationalSeparation_nonneg _ _) exponent

/-- Scaling both observables scales their powered distance by the same natural power of the factor's magnitude. -/
theorem poweredLpDistance_scale {α : Type}
    (content : Content α) (exponent : Nat)
    (factor : Fraction.Rational) (left right : α → Fraction.Rational) :
    content.poweredLpDistance exponent
        (fun item => factor * left item)
        (fun item => factor * right item) =
      Distance.rationalSeparation factor 0 ^ exponent *
        content.poweredLpDistance exponent left right := by
  unfold poweredLpDistance
  calc
    content.integral (fun item =>
        Distance.rationalSeparation (factor * left item) (factor * right item) ^
          exponent) =
        content.integral (fun item => Distance.rationalSeparation factor 0 ^ exponent *
          Distance.rationalSeparation (left item) (right item) ^ exponent) :=
      content.integral_congr _ _ (fun item => by
        rw [Distance.rationalSeparation_scale, Fraction.Field.mul_pow_direct])
    _ = Distance.rationalSeparation factor 0 ^ exponent *
          content.integral (fun item =>
            Distance.rationalSeparation (left item) (right item) ^ exponent) :=
      content.integral_scale _ _

/-- Scaling an observable scales its powered integral by the same natural power of the factor's magnitude. -/
theorem poweredLp_scale {α : Type} (content : Content α)
    (exponent : Nat) (factor : Fraction.Rational) (value : α → Fraction.Rational) :
    content.poweredLp exponent (fun item => factor * value item) =
      Distance.rationalSeparation factor 0 ^ exponent *
        content.poweredLp exponent value := by
  unfold poweredLp
  calc
    content.integral (fun item =>
        Distance.rationalSeparation (factor * value item) 0 ^ exponent) =
        content.integral (fun item => Distance.rationalSeparation factor 0 ^ exponent *
          Distance.rationalSeparation (value item) 0 ^ exponent) :=
      content.integral_congr _ _ (fun item => by
        rw [Distance.rationalSeparation_mul_zero, Fraction.Field.mul_pow_direct])
    _ = Distance.rationalSeparation factor 0 ^ exponent *
          content.integral (fun item =>
            Distance.rationalSeparation (value item) 0 ^ exponent) :=
      content.integral_scale _ _

/-- Exponent one gives the integral of magnitude. -/
theorem poweredLp_one {α : Type} (content : Content α)
    (value : α → Fraction.Rational) :
    content.poweredLp 1 value = content.poweredL1 value := by
  unfold poweredLp poweredL1
  exact content.integral_congr _ _ (fun item => by rw [pow_one])

/-- Exponent zero gives the total mass of the exact content. -/
theorem poweredLp_zero {α : Type} (content : Content α)
    (value : α → Fraction.Rational) :
    content.poweredLp 0 value = content.total := by
  unfold poweredLp
  calc
    content.integral (fun item => Distance.rationalSeparation (value item) 0 ^ 0) =
        content.integral (fun _ => (1 : Fraction.Rational)) :=
      content.integral_congr _ _ (fun item => pow_zero _)
    _ = content.total * 1 := content.integral_constant 1
    _ = content.total := mul_one _

/-- A constant observable's powered integral is total mass times that constant magnitude's power. -/
theorem poweredLp_constant {α : Type} (content : Content α)
    (exponent : Nat) (constant : Fraction.Rational) :
    content.poweredLp exponent (fun _ => constant) =
      content.total * Distance.rationalSeparation constant 0 ^ exponent := by
  unfold poweredLp
  exact content.integral_constant _

/-- Exponent two gives the observable's square integral. -/
theorem poweredLp_two {α : Type} (content : Content α)
    (value : α → Fraction.Rational) :
    content.poweredLp 2 value = content.poweredL2 value := by
  unfold poweredLp poweredL2
  exact content.integral_congr _ _ (fun item => by
    calc
      Distance.rationalSeparation (value item) 0 ^ 2 =
          (value item - 0) ^ 2 := Distance.NaturalLp.rationalSeparation_sq (value item) 0
      _ = value item ^ 2 := by ring1)

/-- Distance exponent one gives integrated rational separation. -/
theorem poweredLpDistance_one {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) :
    content.poweredLpDistance 1 left right =
      content.l1Distance left right := by
  unfold poweredLpDistance l1Distance
  exact content.integral_congr _ _ (fun item => by rw [pow_one])

/-- Distance exponent two gives squared integrated distance. -/
theorem poweredLpDistance_two {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) :
    content.poweredLpDistance 2 left right =
      content.poweredL2Distance left right := by
  unfold poweredLpDistance poweredL2Distance poweredL2
  exact content.integral_congr _ _ (fun item =>
    Distance.NaturalLp.rationalSeparation_sq (left item) (right item))

/-- The powered magnitude integral of a difference equals the powered separation integral of the original observables.
-/
theorem poweredLp_sub_eq_poweredLpDistance {α : Type}
    (content : Content α) (exponent : Nat)
    (left right : α → Fraction.Rational) :
    content.poweredLp exponent (fun item => left item - right item) =
      content.poweredLpDistance exponent left right := by
  unfold poweredLp poweredLpDistance
  exact content.integral_congr _ _ (fun item =>
    congrArg (fun magnitude => magnitude ^ exponent)
      (Distance.rationalSeparation_eq_sub_zero (left item) (right item)).symm)

/-- Every positive natural-powered distance of an observable from itself vanishes. -/
@[simp] theorem poweredLpDistance_refl {α : Type}
    (content : Content α) (exponent : Nat)
    (value : α → Fraction.Rational) :
    content.poweredLpDistance (exponent + 1) value value = 0 := by
  unfold poweredLpDistance
  calc
    content.integral (fun item =>
        Distance.rationalSeparation (value item) (value item) ^ (exponent + 1)) =
        content.integral (fun _ => (0 : Fraction.Rational)) :=
      content.integral_congr _ _ (fun item => by
        unfold Distance.rationalSeparation
        rewrite [sub_self, Fraction.Order.Basic.max_self]
        exact zero_pow (Nat.zero_lt_succ exponent).ne')
    _ = content.total * 0 := content.integral_constant 0
    _ = 0 := mul_zero _

/-- Exchanging the two observables preserves every natural-powered distance. -/
theorem poweredLpDistance_symm {α : Type}
    (content : Content α) (exponent : Nat)
    (left right : α → Fraction.Rational) :
    content.poweredLpDistance exponent left right =
      content.poweredLpDistance exponent right left := by
  unfold poweredLpDistance
  exact content.integral_congr _ _ (fun item => by
    rw [Distance.rationalSeparation_symm])

end

end Content

end Purelib.Measure

end
