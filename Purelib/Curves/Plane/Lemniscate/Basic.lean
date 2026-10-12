module
public import Purelib.Data.Nat.Order
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Geometry

@[expose] public section

namespace Purelib.Curves.Plane.Lemniscate

section Lemniscate

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The Bernoulli lemniscate with parameter `A=a²`: `(x²+y²)²=2A(x²-y²)`. -/
def evaluate (parameter : K) (point : Geometry.Plane.Point K)
  : K :=
  (point.x ^ 2 + point.y ^ 2) ^ 2 -
    2 * parameter * (point.x ^ 2 - point.y ^ 2)

/-- A point belongs to the Bernoulli lemniscate when its displayed quartic polynomial vanishes. -/
def Contains (parameter : K) (point : Geometry.Plane.Point K)
  : Prop :=
  evaluate parameter point = 0
end Lemniscate

end Purelib.Curves.Plane.Lemniscate

end
