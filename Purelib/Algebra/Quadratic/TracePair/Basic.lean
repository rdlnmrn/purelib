module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation

public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib.Algebra.Field

section
public section

/-!
# A finite quadratic trace norm on integer coefficient lists

For a displayed trace parameter `t`, let `a` satisfy
`a² = t*a - 1`.  Every integer polynomial in `a` reduces to a pair
`A(t) + B(t)*a`; its conjugate norm is
`A² + t*A*B + B²`.  All coefficient programs below are primitive
recursions on finite `List Int` values.
-/

namespace Purelib.Algebra.Quadratic

set_option genInjectivity false in
/-- Two coefficients in the formal quadratic basis one and a generator.

The record retains scalar and generator coordinates; multiplication separately receives the trace parameter for the
relation alpha squared equals trace times alpha minus one. -/
structure TracePair (K : Type*) where
  /-- The coefficient of one in the quadratic basis. -/ scalar : K
  /-- The coefficient of the formal quadratic generator. -/ generator : K

constructive_injectivity TracePair

namespace TracePair

end TracePair
namespace TracePair

variable {K : Type*} [ExplicitField K]

section
/-- The quadratic coordinate pair (0, 0). -/
@[expose] def zero : TracePair K := ⟨0, 0⟩

/-- The quadratic coordinate pair (1, 0). -/
@[expose] def one : TracePair K := ⟨1, 0⟩

/-- Add quadratic pairs coordinate by coordinate. -/
@[expose] def add (left right : TracePair K) : TracePair K :=
  ⟨left.scalar + right.scalar, left.generator + right.generator⟩

/-- Multiply both coordinates of a quadratic pair by one field scalar. -/
@[expose] def scale (factor : K) (pair : TracePair K) :
  TracePair K :=
  ⟨factor * pair.scalar, factor * pair.generator⟩

/-- Negate both coordinates of a quadratic pair. -/
@[expose] def neg (pair : TracePair K) : TracePair K :=
  ⟨-pair.scalar, -pair.generator⟩

/-- Subtract quadratic pairs coordinate by coordinate. -/
@[expose] def sub (left right : TracePair K) : TracePair K :=
  ⟨left.scalar - right.scalar, left.generator - right.generator⟩

/-- Multiply quadratic pairs using the supplied trace relation.

Products of generator coordinates are reduced by alpha squared equals trace times alpha minus one. -/
@[expose] def mul (trace : K) (left right : TracePair K) :
  TracePair K :=
  ⟨left.scalar * right.scalar - left.generator * right.generator,
    left.scalar * right.generator + left.generator * right.scalar +
      trace * left.generator * right.generator⟩

end

/-- The formal quadratic generator, represented by the pair (0, 1). -/
@[expose] def alpha : TracePair K := ⟨0, 1⟩

omit [ExplicitField K] in
/-- Quadratic pairs are equal when both coordinates agree. -/
@[ext] theorem ext {left right : TracePair K}
    (scalar : left.scalar = right.scalar)
    (generator : left.generator = right.generator) : left = right := by
  cases left
  cases right
  simp_all [-eq_self, -iff_self]
  rfl

/-- The zero pair is a left zero for quadratic multiplication. -/
theorem mul_zero_left (trace : K) (pair : TracePair K) :
    TracePair.mul trace TracePair.zero pair = TracePair.zero := by
  apply TracePair.ext <;> simp [-eq_self, -iff_self, TracePair.mul, TracePair.zero] <;> rfl

/-- The unit pair is a left identity for quadratic multiplication. -/
theorem mul_one_left (trace : K) (pair : TracePair K) :
    TracePair.mul trace TracePair.one pair = pair := by
  apply TracePair.ext <;> simp only [-eq_self, -iff_self, TracePair.mul, TracePair.one] <;> ring0

/-- Quadratic multiplication distributes over addition in its left input.

All three pairs share the same trace parameter. -/
theorem mul_add_left (trace : K) (first second right :
  TracePair K) :
    TracePair.mul trace (TracePair.add first second) right =
      TracePair.add (TracePair.mul trace first right) (TracePair.mul trace second right) := by
  apply TracePair.ext <;> simp only [-eq_self, -iff_self, TracePair.mul, TracePair.add] <;> ring0

/-- A scalar factor in the left input can be extracted from quadratic multiplication.

The field scalar multiplies both output coordinates under the same trace parameter. -/
theorem mul_scale_left (trace factor : K) (left right :
  TracePair K) :
    TracePair.mul trace (TracePair.scale factor left) right =
      TracePair.scale factor (TracePair.mul trace left right) := by
  apply TracePair.ext <;> simp only [-eq_self, -iff_self, TracePair.mul, TracePair.scale] <;> ring0

/-- Multiplication by the quadratic generator shifts the coordinate pair.

The new scalar is the negative generator coordinate, and the new generator coordinate is the old scalar plus trace times
the old generator coordinate. -/
theorem alpha_mul (trace : K) (pair : TracePair K) :
    TracePair.mul trace TracePair.alpha pair =
      ⟨-pair.generator, pair.scalar + trace * pair.generator⟩ := by
  apply TracePair.ext <;> simp only [-eq_self, -iff_self, TracePair.mul, TracePair.alpha] <;> ring0
end TracePair

end Purelib.Algebra.Quadratic

end

end
