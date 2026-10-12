module
public import Purelib.Data.Nat.Order

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Quadratic.TracePair.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Algebra.Quadratic (TracePair)

section
@[expose] public section

/-!
# A finite quadratic trace norm on integer coefficient lists

For a displayed trace parameter `t`, let `a` satisfy
`a² = t*a - 1`.  Every integer polynomial in `a` reduces to a pair
`A(t) + B(t)*a`; its conjugate norm is
`A² + t*A*B + B²`.  All coefficient programs below are primitive
recursions on finite `List Int` values.
-/

namespace Purelib.Algebra.Quadratic.TracePair

section TracePair

variable {K : Type*} [ExplicitField K]

/-- Compute the conjugate norm of a quadratic pair.

For scalar A and generator coefficient B, the norm is A squared plus trace times A times B plus B squared. -/
def norm (trace : K) (pair : TracePair K) : K :=
  pair.scalar * pair.scalar +
    trace * pair.scalar * pair.generator +
    pair.generator * pair.generator

/-- The quadratic norm preserves multiplication at a fixed trace parameter.

The norm of the reduced product equals the product of the two scalar norms. -/
theorem norm_mul (trace : K) (left right : TracePair K) :
    TracePair.norm trace (TracePair.mul trace left right) =
      TracePair.norm trace left * TracePair.norm trace right := by
  simp only [TracePair.norm, TracePair.mul]
  ring0

/-- Compute the sum of a quadratic value and its conjugate.

The result is twice the scalar coordinate plus the trace parameter times the generator coordinate. -/
def traceValue (trace : K) (pair : TracePair K) : K :=
  2 * pair.scalar + trace * pair.generator

/-- The quadratic trace preserves coordinatewise subtraction. -/
theorem traceValue_sub (trace : K) (left right : TracePair K)
  :
    TracePair.traceValue trace (TracePair.sub left right) =
      TracePair.traceValue trace left - TracePair.traceValue trace right := by
  simp only [TracePair.traceValue, TracePair.sub]
  ring0

/-- The quadratic trace commutes with scalar multiplication. -/
theorem traceValue_scale (trace factor : K) (pair : TracePair
  K) :
    TracePair.traceValue trace (TracePair.scale factor pair) =
      factor * TracePair.traceValue trace pair := by
  simp only [TracePair.traceValue, TracePair.scale]
  ring0

/-- Subtracting the unit pair changes the norm by one minus the trace.

Both the norm and trace use the same quadratic trace parameter. -/
theorem norm_sub_one (trace : K) (pair : TracePair K) :
    TracePair.norm trace (TracePair.sub pair TracePair.one) =
      TracePair.norm trace pair + 1 - TracePair.traceValue trace pair := by
  simp only [TracePair.norm, TracePair.sub, TracePair.one, TracePair.traceValue]
  ring0
end TracePair

end Purelib.Algebra.Quadratic.TracePair

end
