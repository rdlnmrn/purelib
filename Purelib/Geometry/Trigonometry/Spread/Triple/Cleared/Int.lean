module
public import Purelib.Algebra.Field.ExplicitField
import Init.Data.Int.Basic
import Mathlib.Algebra.Group.Defs

section
@[expose] public section

/-!
# Divine Proportions, Chapter 24: surveying

Every construction is expressed by its finite quadrance/spread equations.
Decimal readings are retained as exact integer coefficient pairs, with
integer interval certificates for the source's numerical approximations.
-/

namespace Purelib.Geometry.Trigonometry.Spread.Triple.Cleared.Int

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The common-denominator Triple-spread quadratic at `z=c/d`, when the two measured spreads are `a/d,b/d`. -/
def surveyingTripleRootNumerator
    (a b c denominator : Int) : Int :=
  (c * denominator - a * denominator - b * denominator + 2 * a * b) ^ 2 -
    4 * a * b * (denominator - a) * (denominator - b)
end
end Purelib.Geometry.Trigonometry.Spread.Triple.Cleared.Int

end
