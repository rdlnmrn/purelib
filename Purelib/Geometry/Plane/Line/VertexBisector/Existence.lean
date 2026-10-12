module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Squares
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Spread.Squares
public import Purelib.Geometry.Plane.Line.VertexBisector.Basic
import Purelib.Geometry.Plane.Line.VertexBisector.Construction
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Spread

open Purelib.Geometry.Plane.Line.VertexBisector

section
@[expose] public section

/-!
# Divine Proportions, §6.9: vertex bisectors

An explicit witness `r² = ‖l₁‖‖l₂‖` produces the two normalized
bisectors `r l₁ ± ‖l₁‖ l₂`.  This formulation is equivalent to the
book's longer coefficient display, but is symmetric enough that all finite
field cancellations remain visible.
-/

namespace Purelib.Geometry.Plane.Line.VertexBisector.Existence

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Any bisector supplies the square witness required by the normalized construction. -/
theorem normProduct_isNonzeroSquare_of_isVertexBisector
  [DecidableEq K]
    (first second bisector : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (isBisector : VertexBisector.Basic.IsVertexBisector first second bisector
      firstNonNull secondNonNull notParallel) :
    Squares.IsNonzeroSquare (Line.Basic.lineNorm first * Line.Basic.lineNorm second) := by
  rcases isBisector with ⟨bisectorNonNull, _containsVertex, equalSpreads⟩
  exact Squares.normProduct_isNonzeroSquare_of_equal_spreads first second bisector
    firstNonNull secondNonNull bisectorNonNull notParallel equalSpreads

/-- Existence clause of Theorem 45: a bisector exists precisely when the spread of the two vertex lines is a nonzero
square. Nonparallelity makes the book's word “square” automatically nonzero. -/
theorem vertex_bisector_exists_iff_spread_isNonzeroSquare
  [DecidableEq K]
    (first second : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0) :
    (∃ bisector : Plane.Line K,
        VertexBisector.Basic.IsVertexBisector first second bisector
          firstNonNull secondNonNull notParallel) ↔
      Squares.IsNonzeroSquare
        (Spread.spread first second firstNonNull secondNonNull) := by
  constructor
  · rintro ⟨bisector, isBisector⟩
    apply (Squares.spread_isNonzeroSquare_iff_normProduct_isNonzeroSquare
      first second firstNonNull secondNonNull notParallel).2
    exact normProduct_isNonzeroSquare_of_isVertexBisector first second
      bisector
      firstNonNull secondNonNull notParallel isBisector
  · intro spreadSquare
    have normProductSquare :=
      (Squares.spread_isNonzeroSquare_iff_normProduct_isNonzeroSquare
        first second firstNonNull secondNonNull notParallel).1 spreadSquare
    rcases normProductSquare with ⟨root, _rootNonzero, normProductEquation⟩
    refine ⟨Construction.positiveVertexBisector first second root firstNonNull notParallel, ?_⟩
    exact Construction.positiveVertexBisector_isVertexBisector first second root firstNonNull
      secondNonNull notParallel twoNonzero normProductEquation.symm
end Purelib.Geometry.Plane.Line.VertexBisector.Existence

end
