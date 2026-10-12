module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
public import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
public import Purelib.Topology.Surface.Sewing.SewnPathArea
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Nat.Init
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Mathlib.Algebra.Group.Defs
import Purelib.Tactic.Ring

public section

/-!
# Geometry-first requests for full sewn path areas

The request pays all occurrence counts before the local contact bank is
sampled. It consumes the existing inherited path allowance and a fixed
source-increment magnitude; it does not assume exact primitive offsets.
-/

section

open Purelib.Approximation.Rational.Budget

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.Rat

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.Patch

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnPathArea.PathSources

open Purelib.Topology.Surface.Sewing.SewnPathRequests

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces

namespace Purelib.Topology.Surface.Sewing.SewnPathAreaRequests

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces (PathSources)
open Purelib.Topology.Surface.Sewing.SewnPathRequests (PathRequest)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting (Shape shape)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceBank)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {patch : Patch.CutPatch faces indices boundary} {assembly : CutPatch.Assembly faces patch}

set_option genInjectivity false in
/-- A retained tolerance request for the area of a complete sewn path.

The request records its occurrence count, source-increment magnitude, quartic amplification and a subordinate path
request with positive error tolerance. -/
structure PathAreaRequest (assembly : CutPatch.Assembly faces patch) (count : Nat) (magnitude target :
  Fraction.Rational) where
  /-- The requested area-error target is strictly positive. -/ positive : 0 < target
  /-- The retained source-increment magnitude bound is nonnegative. -/ magnitude_nonnegative : 0 ≤ magnitude
  /-- Cached quartic occurrence-count amplification. -/ weight : Fraction.Rational
  /-- The cached weight is exactly 32 times the fourth power of the count times the shifted magnitude. -/ weight_eq :
    weight = 32 * (count : Fraction.Rational) ^ 4 * (magnitude + 1)
  /-- Cached path-error tolerance used by the area estimate. -/ error : Fraction.Rational
  /-- The tolerance is the minimum of one and the target divided by the shifted weight. -/ error_eq : error = min 1
    (target / (weight + 1))
  /-- A request on the same assembly and count whose target is the cached area-error tolerance. -/ path :
    SewnPathRequests.PathRequest assembly count error

constructive_injectivity PathAreaRequest

namespace PathAreaRequest

variable {count : Nat} {magnitude target : Fraction.Rational}

/-- The fourth power of a natural count cast to a rational is nonnegative. -/
private theorem fourth_nonnegative (count : Nat) : (0 : Fraction.Rational) ≤ (count : Fraction.Rational) ^ 4 :=
  (Fraction.Order.Arithmetic.sq_nonneg_direct ((count : Fraction.Rational) ^ 2)).trans_eq (by ring1)

/-- A nonnegative source magnitude makes the quartic path-area weight nonnegative. -/
private theorem weight_nonnegative_of (count : Nat) {magnitude : Fraction.Rational} (positive : 0 ≤ magnitude) :
    (0 : Fraction.Rational) ≤ 32 * (count : Fraction.Rational) ^ 4 * (magnitude + 1) :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (fourth_nonnegative count))
      (add_nonneg positive (by decide))

/-- Build a path-area request from an existing assembly profile and positive target.

The error tolerance is the minimum of one and the target divided by the shifted quartic weight; the subordinate path
request reuses the supplied profile. -/
@[expose] def ofProfile (profile : SewnPrimitiveAccounting.Shape) (profileEq : profile = SewnPrimitiveAccounting.shape
  assembly) (count : Nat)
    (magnitude target : Fraction.Rational) (nonnegative : 0 ≤ magnitude) (positive : 0 < target) :
    PathAreaRequest assembly count magnitude target :=
  let weight := 32 * (Aggregate.countCoordinate count) ^ 4 * (magnitude + 1)
  have weightEq : weight = 32 * (count : Fraction.Rational) ^ 4 * (magnitude + 1) := by
    dsimp only [weight]
    rw [Aggregate.countCoordinate_eq]
  have nonnegativeWeight : 0 ≤ weight := by rw [weightEq]; exact weight_nonnegative_of count nonnegative
  let error := min 1 (target / (weight + 1))
  have errorPositive : 0 < error := Fraction.Order.Basic.lt_min (by decide)
    (Fraction.Order.Field.div_pos_direct positive (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      nonnegativeWeight (by decide)))
  ⟨positive, nonnegative, weight, weightEq, error, rfl, PathRequest.ofProfile profile profileEq count error
    errorPositive⟩

/-- The retained path-area amplification weight is nonnegative. -/
theorem weight_nonnegative (request : PathAreaRequest assembly count magnitude target) : 0 ≤
  request.weight := by
  rw [request.weight_eq]
  exact weight_nonnegative_of count request.magnitude_nonnegative

/-- The subordinate path request certifies a positive area-error tolerance. -/
theorem error_positive (request : PathAreaRequest assembly count magnitude target) : 0 <
  request.error := request.path.target_positive

/-- An error below the retained tolerance pays the full quartic area bound.

The estimate retains both the source magnitude and error contribution, with all four occurrence-count factors. -/
theorem paid (request : PathAreaRequest assembly count magnitude target) {error :
  Fraction.Rational}
    (nonnegative : 0 ≤ error) (small : error < request.error) :
    32 * (count : Fraction.Rational) ^ 4 * error * (magnitude + error) < target := by
  have errorLeOne : error ≤ 1 := small.le.trans (by rw [request.error_eq]; exact Fraction.Order.Basic.min_le_left _ _)
  have factorNonnegative : (0 : Fraction.Rational) ≤ 32 * (count : Fraction.Rational) ^ 4 * error :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (fourth_nonnegative count))
        nonnegative
  have enlarged : 32 * (count : Fraction.Rational) ^ 4 * error * (magnitude + error) ≤
      32 * (count : Fraction.Rational) ^ 4 * error * (magnitude + 1) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add le_rfl errorLeOne) factorNonnegative
  have shifted : 0 < request.weight + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    request.weight_nonnegative (by decide)
  calc
    _ ≤ 32 * (count : Fraction.Rational) ^ 4 * error * (magnitude + 1) := enlarged
    _ = request.weight * error := by rw [request.weight_eq]; ring1
    _ ≤ (request.weight + 1) * error := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (le_add_of_nonneg_right (by decide)) nonnegative
    _ < (request.weight + 1) * request.error := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct shifted small
    _ ≤ (request.weight + 1) * (target / (request.weight + 1)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (by rw [request.error_eq]; exact Fraction.Order.Basic.min_le_right _ _) shifted.le
    _ = target := by
      rw [Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ shifted.ne'

/-- A retained area sample meets the target when its path bound meets the request.

The source increments must satisfy the requested magnitude bound and the actual path length must equal the retained
occurrence count. -/
theorem accurate (request : PathAreaRequest assembly count magnitude target)
    {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3} {values : PrimitiveSewing.PrimitiveValues
      patch.count}
    {bank : SewnPrimitiveFaces.FaceBank patch localValues values} {edges : List (Stokes.OrientedEdge patch.count)}
    {sources : SewnPrimitiveFaces.PathSources patch edges} {sample : PathSources.Sample sources bank}
    (area : Sample.AreaSample sample) (lengthEq : edges.length = count)
    (bounded : Gaussian.Norm.Sum.Basic.gaussianNormSqSum (sources.sources.map (fun source => source.increment
      localValues)) ≤ magnitude)
    (small : sample.bound < request.error) : Data.Gaussian.Norm.Basic.normSq (area.sewn.area - area.source.area) <
      target := by
  have bound := area.difference_bound bounded
  rw [lengthEq] at bound
  exact bound.trans_lt (request.paid (Sample.bound_nonnegative sample) small)

end PathAreaRequest
end Purelib.Topology.Surface.Sewing.SewnPathAreaRequests

end
