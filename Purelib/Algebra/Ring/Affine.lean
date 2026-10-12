module

public import Mathlib.Algebra.Ring.Defs
public import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring

/-! Scalar identities for affine reflection expressions in commutative rings and explicit fields. -/

section
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
namespace Purelib.Algebra.Ring.Affine
/-- Factor the common coefficient in the two spread recurrences. -/
public theorem two_sub_four_mul
  (value : K) :
    2 - 4 * value = 2 * (1 - 2 * value) := by
  ring1
end Purelib.Algebra.Ring.Affine
end

section

namespace Purelib.Algebra.Ring.Affine
/-- The scalar distributive identity transporting one reflected tail coefficient step through evaluation.

Distributivity and scalar cancellation identify the displayed terms in
the supplied commutative ring. -/
public theorem reflectedTailRingIdentity {R : Type} [CommRing R]
    (two parameter coefficient previous outer remaining : R) :
    two * parameter * coefficient - previous +
        outer * ((two * parameter - outer) * remaining - coefficient) =
      (two * parameter - outer) * (coefficient + outer * remaining) -
        previous := by
  ring1

/-- The scalar distributive identity transporting one reflected Horner step through evaluation.

The supplied commutative ring laws regroup the same scalar products and
remove the displayed double negation. -/
public theorem reflectedStepRingIdentity {R : Type} [CommRing R]
    (two parameter head coefficient outer remaining : R) :
    two * parameter * head - -coefficient +
        outer * ((two * parameter - outer) * remaining - head) =
      (head + outer * remaining) * (two * parameter - outer) +
        coefficient := by
  ring1
end Purelib.Algebra.Ring.Affine
end
