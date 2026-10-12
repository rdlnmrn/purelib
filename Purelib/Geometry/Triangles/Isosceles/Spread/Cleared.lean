module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init

section
@[expose] public section

/-!
# Divine Proportions, Chapter 26: Platonic solids

All five face-spread computations are recorded by one denominator-cleared
isosceles-triangle certificate.  Exercise 26.1 is proved directly from three
displayed edge vectors.  Exercise 26.4 uses a uniformly scaled standard
icosahedron, so its coordinates are polynomial in a supplied witness
`root²=5` and contain no selected irrational or completed field.
-/

namespace Purelib.Geometry.Triangles.Isosceles.Spread.Cleared

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-! ## A common isosceles-spread certificate -/

/-- Suppose the base quadrance is `baseNumerator/baseDenominator` and each equal quadrance is
`radiusNumerator/radiusDenominator`. This is exactly the cross-multiplied assertion that the isosceles vertex spread is
`spreadNumerator/spreadDenominator`. -/
def ClearedIsoscelesSpread
    (baseNumerator baseDenominator radiusNumerator radiusDenominator
      spreadNumerator spreadDenominator : K) : Prop :=
  spreadDenominator * baseNumerator * radiusDenominator *
      (4 * radiusNumerator * baseDenominator -
        baseNumerator * radiusDenominator) =
    spreadNumerator * 4 * radiusNumerator ^ 2 * baseDenominator ^ 2

/-- The corresponding endpoint spread `1-base/(4 radius)`, again with all denominators cleared. -/
def ClearedIsoscelesEndpointSpread
    (baseNumerator baseDenominator radiusNumerator radiusDenominator
      spreadNumerator spreadDenominator : K) : Prop :=
  spreadDenominator *
      (4 * radiusNumerator * baseDenominator -
        baseNumerator * radiusDenominator) =
    spreadNumerator * 4 * radiusNumerator * baseDenominator
end
end Purelib.Geometry.Triangles.Isosceles.Spread.Cleared

end
