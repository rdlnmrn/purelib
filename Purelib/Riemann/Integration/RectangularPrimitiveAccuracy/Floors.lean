module

public import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Nat.Order

/-! # A genuine later rectangular primitive request before model construction

An original numerical gluing request retains its scales. A separate finite
minimum index determines a NEW request whose edge and global bounds use
the actual maximum index. No model, primitive or observation is reindexed.
-/

public section

namespace Purelib.Riemann.Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy

open Purelib.Data.Nat

open Purelib
open Purelib.Approximation.Rational
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial Box)

variable {polynomial numerator : Polynomial} {ambient : Box}
    {clearance : RegionClearance polynomial ambient} {bounds : PrimitiveOverlapBounds clearance numerator}
    {columns : Nat} {target : Rational}

/-- Retain the original scales and construct a NEW accurate request at the maximum of its index and a required floor.

The original request stays an input. Its actual geometric radius is
recomputed at the new index, and owned antitonicity proves the same gluing
target. This construction precedes any model or primitive factory; it
does not transport an old refined cache to another nominal stage.
-/
def after (request : GridPrimitiveAccuracy bounds columns target) (floor : Nat) :
    GridPrimitiveAccuracy bounds columns target :=
  let index := Nat.max request.index floor
  let factor := 8 * Budget.Aggregate.countCoordinate columns ^ 2 + 2
  have factorEq : factor = 8 * (columns : Rational) ^ 2 + 2 := by
    dsimp only [factor]
    rewrite [Budget.Aggregate.countCoordinate_eq]
    rfl
  have factorNonnegative : (0 : Rational) ≤ factor :=
    (show (0 : Rational) ≤ 1 by decide +kernel).trans
      ((factor_one_le columns).trans_eq factorEq.symm)
  have scaleNonnegative : (0 : Rational) ≤ request.edgeScale :=
    (edgeScale_nonneg bounds).trans_eq request.edgeScale_eq.symm
  let edgeBound := Geometric.Basic.quarterRadius request.edgeScale index
  let globalBound := factor * edgeBound
  have monotone := Geometric.Basic.quarterRadius_antitone scaleNonnegative (Order.le_max_left request.index floor)
  have paid := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct monotone factorNonnegative
  have old : factor * Geometric.Basic.quarterRadius request.edgeScale request.index = request.globalBound :=
    (congrArg (fun value : Rational => value * Geometric.Basic.quarterRadius request.edgeScale request.index)
      factorEq).trans
        ((congrArg (fun value : Rational => (8 * (columns : Rational) ^ 2 + 2) * value)
          request.edgeBound_eq.symm).trans request.globalBound_eq.symm)
  { edgeScale := request.edgeScale
    edgeScale_eq := request.edgeScale_eq
    scale := request.scale
    scale_eq := request.scale_eq
    index := index
    edgeBound := edgeBound
    edgeBound_eq := rfl
    globalBound := globalBound
    globalBound_eq := congrArg (fun value : Rational => value * edgeBound) factorEq
    accurate := (paid.trans_eq old).trans_lt request.accurate }

/-- The new request records the exact maximum index selected before any model construction. -/
theorem after_index (request : GridPrimitiveAccuracy bounds columns target) (floor : Nat) :
    (after request floor).index = Nat.max request.index floor := by
  unfold after
  rfl

/-- The new actual index pays its original request's depth without replacing that request. -/
theorem index_le_after (request : GridPrimitiveAccuracy bounds columns target) (floor : Nat) :
    request.index ≤ (after request floor).index :=
  (Order.le_max_left request.index floor).trans_eq (after_index request floor).symm

/-- The independently required finite floor is paid by the same actual new request index. -/
theorem floor_le_after (request : GridPrimitiveAccuracy bounds columns target) (floor : Nat) :
    floor ≤ (after request floor).index :=
  (Order.le_max_right request.index floor).trans_eq (after_index request floor).symm

/-- The new request reuses the SAME cached original edge scale. -/
theorem after_edgeScale (request : GridPrimitiveAccuracy bounds columns target) (floor : Nat) :
    (after request floor).edgeScale = request.edgeScale := by
  unfold after
  rfl

/-- The new request reuses the SAME cached original global scale. -/
theorem after_scale (request : GridPrimitiveAccuracy bounds columns target) (floor : Nat) :
    (after request floor).scale = request.scale := by
  unfold after
  rfl

end Purelib.Riemann.Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy

end
