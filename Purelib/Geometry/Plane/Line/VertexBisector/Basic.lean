module

import Purelib.Tactic.Ring
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Intersection
public import Purelib.Geometry.Plane.Line.Spread
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

section
@[expose] public section

/-!
# Divine Proportions, §6.9: vertex bisectors

An explicit witness `r² = ‖l₁‖‖l₂‖` produces the two normalized
bisectors `r l₁ ± ‖l₁‖ l₂`.  This formulation is equivalent to the
book's longer coefficient display, but is symmetric enough that all finite
field cancellations remain visible.
-/

namespace Purelib.Geometry.Plane.Line.VertexBisector.Basic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The book's definition of a bisector of the non-null, nonparallel vertex `first second`. The vertex is the explicitly
computed line intersection, and the non-null witness keeps both spread denominators executable. -/
def IsVertexBisector [DecidableEq K]
    (first second bisector : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second) : Prop :=
  ∃ bisectorNonNull : ¬ bisector.IsNull,
    bisector.Contains (Intersection.lineIntersection first second notParallel) ∧
      Spread.spread first bisector firstNonNull bisectorNonNull =
        Spread.spread second bisector secondNonNull bisectorNonNull
end Purelib.Geometry.Plane.Line.VertexBisector.Basic

end

section
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
namespace Purelib.Geometry.Plane.Line.VertexBisector.Basic
/-- The symmetric sum of a direction determinant times the other direction dot product.

Each term pairs one diagonal with the proposed axis, giving the common factor in the axis and equal-spread identities.
-/
@[expose] public def bisectorFactor (first second axis
  : Line K) : K :=
  (first.a * axis.b - axis.a * first.b) *
      (second.a * axis.a + second.b * axis.b) +
    (first.a * axis.a + first.b * axis.b) *
      (second.a * axis.b - axis.a * second.b)

/-- Factor the cleared difference of the two diagonal spreads with a proposed axis.

The factors are the diagonal direction determinant and the symmetric bisector expression; this polynomial identity
requires no divisions. -/
public theorem bisector_balance_factor
    (firstDiagonal secondDiagonal axis : Line K) :
    Purelib.Geometry.Plane.Line.Basic.lineNorm secondDiagonal *
          (firstDiagonal.a * axis.b - axis.a * firstDiagonal.b) ^ 2 -
        Purelib.Geometry.Plane.Line.Basic.lineNorm firstDiagonal *
          (secondDiagonal.a * axis.b - axis.a * secondDiagonal.b) ^ 2 =
      (firstDiagonal.a * secondDiagonal.b -
          secondDiagonal.a * firstDiagonal.b) *
        bisectorFactor firstDiagonal secondDiagonal axis :=
          by
  unfold Purelib.Geometry.Plane.Line.Basic.lineNorm bisectorFactor
  ring1
end Purelib.Geometry.Plane.Line.VertexBisector.Basic
end
