module

public import Mathlib.Algebra.Ring.Defs

namespace Purelib.Algebra.Ring.Multiplication

-- Read negation directly from the ring's retained additive group.
attribute [local instance high] SubNegMonoid.toNeg

variable {R : Type*} [Ring R]

/-- Negating the left ring factor negates the displayed product. -/
public theorem neg_mul (left right : R) : -left * right = -(left * right) := by
  apply Eq.symm
  apply SubtractionMonoid.neg_eq_of_add
  rw [← add_mul, add_comm left (-left), AddGroup.neg_add_cancel, zero_mul]

/-- Negating the right ring factor negates the displayed product. -/
public theorem mul_neg (left right : R) : left * -right = -(left * right) := by
  apply Eq.symm
  apply SubtractionMonoid.neg_eq_of_add
  rw [← mul_add, add_comm right (-right), AddGroup.neg_add_cancel, mul_zero]

/-- Negating both ring factors preserves their displayed product. -/
public theorem neg_mul_neg (left right : R) : -left * -right = left * right := by
  rw [neg_mul, mul_neg, neg_neg]

end Purelib.Algebra.Ring.Multiplication
