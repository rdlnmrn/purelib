module

public import Purelib.Algebra.Field.ExplicitOrder.Sign
import Purelib.Tactic.Ring

/-!
# Strict comparisons through retained differences

The positive cone of a ray-ordered field controls comparisons with zero.
Comparisons between arbitrary scalars additionally use an explicit law
for the same retained order and subtraction operations.
-/

public section

namespace Purelib.Algebra.Field.ExplicitOrder.Sign

variable {K : Type*} [RayOrderedExplicitField K]

/-- The retained strict comparison agrees with positivity of its explicit difference.

This property uses the original field and order dictionaries. It adds no
operation instance or replacement comparison procedure.
-/
@[expose] def OrderDifferenceLaw (K : Type*) [RayOrderedExplicitField K] : Prop :=
  ∀ left right : K, left < right ↔ 0 < right - left

namespace OrderDifferenceLaw

/-- A scalar is below zero exactly when its negative is positive. -/
theorem lt_zero_iff (law : OrderDifferenceLaw K) (value : K) :
    value < 0 ↔ 0 < -value := by
  have equivalent := law value 0
  rw [show (0 : K) - value = -value by ring1] at equivalent
  exact equivalent

/-- A scalar is below one exactly when its unit complement is positive. -/
theorem lt_one_iff (law : OrderDifferenceLaw K) (value : K) :
    value < 1 ↔ 0 < 1 - value := law value 1

/-- A scalar is above one exactly when its unit excess is positive. -/
theorem one_lt_iff (law : OrderDifferenceLaw K) (value : K) :
    1 < value ↔ 0 < value - 1 := law 1 value

end OrderDifferenceLaw

end Purelib.Algebra.Field.ExplicitOrder.Sign
