import Mathlib.Algebra.Ring.Defs

/-!
# An explicit field-law interface

Mathlib's `Field` has several compatible inheritance paths to its multiplicative
operations.  Asking typeclass synthesis to choose between those paths can make an
otherwise finite proof depend on `Classical.choice`.  `ExplicitField` records the
small set of field laws needed by the executable polynomial algorithms through one
unambiguous operation path.

This is not a finiteness or cardinality assumption on the carrier.  It is only a
bundled interface for explicitly supplied operations and proofs.
-/

namespace RFAP

/-- Commutative-ring operations together with explicitly chosen inverse and division
operations, and the cancellation laws used by the finite algorithms. -/
class ExplicitField (K : Type*) extends CommRing K, Inv K, Div K where
  div_eq_mul_inv : ∀ a b : K, a / b = a * b⁻¹
  mul_inv_cancel : ∀ a : K, a ≠ 0 → a * a⁻¹ = 1
  mul_ne_zero : ∀ {a b : K}, a ≠ 0 → b ≠ 0 → a * b ≠ 0
  inv_ne_zero : ∀ {a : K}, a ≠ 0 → a⁻¹ ≠ 0
  inv_neg : ∀ a : K, (-a)⁻¹ = -(a⁻¹)

namespace ExplicitField

variable {K : Type*} [ExplicitField K]

theorem div_ne_zero {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    a / b ≠ 0 := by
  rw [ExplicitField.div_eq_mul_inv]
  exact ExplicitField.mul_ne_zero ha (ExplicitField.inv_ne_zero hb)

theorem div_mul_cancel (a : K) {b : K} (hb : b ≠ 0) : a / b * b = a := by
  rw [ExplicitField.div_eq_mul_inv, mul_assoc,
    show b⁻¹ * b = b * b⁻¹ from mul_comm _ _,
    ExplicitField.mul_inv_cancel b hb, mul_one]

@[simp] theorem zero_div (b : K) : 0 / b = 0 := by
  rw [ExplicitField.div_eq_mul_inv, zero_mul]

theorem div_neg (a b : K) : a / -b = -(a / b) := by
  rw [ExplicitField.div_eq_mul_inv, ExplicitField.inv_neg,
    ExplicitField.div_eq_mul_inv, mul_neg]

end ExplicitField

end RFAP
