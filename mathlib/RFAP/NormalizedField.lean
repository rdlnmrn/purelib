import mathlib.RFAP.NormalizedGaussian

/-!
# Explicit field compatibility for canonical normalized arithmetic

Normalized fractions and Gaussian rationals now are the canonical semantic
carriers themselves.  Their existing `CommRing` and `RFAP.ExplicitField`
instances therefore already govern the named normalized operations.  This
module retains the erasure-map theorems used by generic finite polynomial
programs without installing duplicate arithmetic instances for the same
carrier.
-/

namespace RFAP.NormalizedFraction

theorem value_injective : Function.Injective value := by
  intro left right equal
  exact equal

@[simp] theorem value_zero : value (0 : ReducedFraction) = 0 := rfl

@[simp] theorem value_one : value (1 : ReducedFraction) = 1 := rfl

@[simp] theorem value_add_instance (left right : ReducedFraction) :
    value (left + right) = value left + value right := rfl

@[simp] theorem value_neg_instance (source : ReducedFraction) :
    value (-source) = -value source := rfl

@[simp] theorem value_sub_instance (left right : ReducedFraction) :
    value (left - right) = value left - value right := rfl

@[simp] theorem value_mul_instance (left right : ReducedFraction) :
    value (left * right) = value left * value right := rfl

@[simp] theorem value_inv_instance (source : ReducedFraction) :
    value source⁻¹ = (value source)⁻¹ := rfl

@[simp] theorem value_div_instance (left right : ReducedFraction) :
    value (left / right) = value left / value right := rfl

end RFAP.NormalizedFraction

namespace RFAP.NormalizedGaussian

theorem value_injective : Function.Injective value := by
  intro left right equal
  exact equal

@[simp] theorem value_zero : value (0 : Gaussian) = 0 := rfl

@[simp] theorem value_one : value (1 : Gaussian) = 1 := rfl

@[simp] theorem value_add_instance (left right : Gaussian) :
    value (left + right) = value left + value right := rfl

@[simp] theorem value_neg_instance (source : Gaussian) :
    value (-source) = -value source := rfl

@[simp] theorem value_sub_instance (left right : Gaussian) :
    value (left - right) = value left - value right := rfl

@[simp] theorem value_mul_instance (left right : Gaussian) :
    value (left * right) = value left * value right := rfl

@[simp] theorem value_inv_instance (source : Gaussian) :
    value source⁻¹ = (value source)⁻¹ := rfl

@[simp] theorem value_div_instance (left right : Gaussian) :
    value (left / right) = value left / value right := rfl

end RFAP.NormalizedGaussian
