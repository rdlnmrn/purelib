module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
public import Purelib.Integration.Path.Dyadic.DyadicAreaRefinement
import Init.Data.Nat.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Rat.Fraction.Order

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Normalization

/-!
# A finite vertex mesh for the actual retained reciprocal arc area

Choose the displayed vertex depth before selecting the shared polynomial.
The original full path remains in the certificate. Its area differs from
this coarser path by a requested amount at every later subdivision depth.
The estimate uses the retained source slope and comparison scale and works
in both intrinsic degree cases.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data Sample)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    UniformReciprocalCover.Cell data edge}
  {regular : RegularBounds.Data cap} {comparison :
    Data regular cell}
  {index : Nat} {box : Geometry.Rational.Box} {capSample :
    Cap.Primitives.Sample cap differential index box}

set_option genInjectivity false in
/-- Fixed spatial movement and area ceilings for the original retained reciprocal cap arc. -/
structure SpatialBounds (comparison : Data regular cell) where
  /-- The cached cap-arc movement ceiling independent of later polynomial stages. -/ slope :
    Coordinate
  /-- The slope is twice the sum of the original source slope and comparison scale. -/ slope_eq : slope = 2 *
    (data.sourceSlope + comparison.scale)
  /-- The cached finite dyadic area refinement scale. -/ areaScale : Coordinate
  /-- The area scale is four times the square of the retained movement ceiling. -/ areaScale_eq : areaScale = 4 * slope
    ^ 2

constructive_injectivity SpatialBounds

namespace SpatialBounds

/-- Cache the original spatial ceilings and select the first finite dyadic depth paying the requested area target. -/
@[expose] def build (comparison : Data regular cell) :
  SpatialBounds comparison :=
  let slope := 2 * (data.sourceSlope + comparison.scale)
  ⟨slope, rfl, 4 * slope ^ 2, rfl⟩

/-- The original source slope and comparison scale give a nonnegative retained movement bound. -/
theorem slope_nonnegative (bounds : SpatialBounds comparison)
  : 0 ≤ bounds.slope := by
  rw [bounds.slope_eq]
  exact Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg data.sourceSlope_nonnegative comparison.scale_nonnegative)

/-- The retained original spatial area refinement scale is nonnegative. -/
theorem areaScale_nonnegative (bounds : SpatialBounds
  comparison) : 0 ≤ bounds.areaScale := by
  rw [bounds.areaScale_eq]
  exact Arithmetic.mul_nonneg_direct (by decide) (Arithmetic.sq_nonneg_direct _)

/-- Every original cap subarc satisfies the retained spatial movement ceiling times squared parameter width. -/
theorem increment_bound (bounds : SpatialBounds comparison)
    (source : UniformReciprocalPrimitives.SourcePrimitive data index) (sample : Sample comparison capSample)
    {first last : Coordinate} (firstInside : edge.left.parameter ≤ first ∧ first ≤
      edge.right.parameter)
    (lastInside : edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq (ArcArea.Sample.capValue sample last - ArcArea.Sample.capValue sample
      first) ≤ bounds.slope * (last - first) ^ 2 := by
  have errorLe : quarterRadius comparison.scale index ≤ comparison.scale := by
    simpa only [quarterRadius_eq_mul_pow, pow_zero,
      Fraction.Field.mul_one_direct, -eq_self, -iff_self] using
      quarterRadius_antitone comparison.scale_nonnegative (Nat.zero_le index)
  rw [bounds.slope_eq]
  exact (ArcArea.Sample.cap_increment_bound source sample firstInside lastInside).trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add le_rfl errorLe) (by decide))
      (Arithmetic.sq_nonneg_direct _))

end SpatialBounds

set_option genInjectivity false in
/-- A cached finite dyadic depth paying the original cap-arc area tolerance.

The retained bounds depend on the original source geometry and comparison scale, so the same request applies at every
polynomial stage. -/
structure SpatialRequest (comparison : Data regular cell) (target : Coordinate) (floor
  : Nat) where
  /-- The cached spatial bounds for this exact original cap comparison. -/ bounds :
    SpatialBounds comparison
  /-- The retained finite vertex depth paying the original area target. -/ depth : Nat
  /-- The depth is the first quarter-radius search result above the original floor. -/ depth_eq : depth =
    firstQuarterBelow bounds.areaScale floor target
  /-- The selected depth respects the original spatial floor. -/ floor_le : floor ≤ depth
  /-- The cached original area refinement discrepancy at the selected depth. -/ error : Coordinate
  /-- The cached discrepancy is the original area scale's quarter-radius. -/ error_eq : error =
    quarterRadius bounds.areaScale depth
  /-- The retained spatial discrepancy is strictly below the original target. -/ accurate : error < target

constructive_injectivity SpatialRequest

namespace SpatialRequest

/-- Cache the original spatial ceilings and select the first finite dyadic depth paying the requested area target. -/
@[expose] def build (comparison : Data regular cell) (target : Coordinate) (positive :
  0 < target) (floor : Nat) :
    SpatialRequest comparison target floor :=
  let bounds := SpatialBounds.build comparison
  let depth := firstQuarterBelow bounds.areaScale floor target
  ⟨bounds, depth, rfl, Search.firstQuarterBelow_ge _ _ _, quarterRadius bounds.areaScale depth, rfl,
    Search.firstQuarterBelow_accurate _ bounds.areaScale_nonnegative _ _ positive⟩

variable {target : Coordinate} {floor depth : Nat}
  {source : UniformReciprocalPrimitives.SourcePrimitive data index}

set_option genInjectivity false in
/-- A coarser cap path retaining the exact original fine path and total.

The new cached summary has the same endpoint increment, and its area differs by less than the paid width-weighted
tolerance. -/
structure CoarseArea (request : SpatialRequest comparison
  target floor)
    (original : ComparedCell comparison source capSample depth) where
  /-- The original fine path meets the retained requested vertex depth. -/ later : request.depth ≤ depth
  /-- The cached coarser increment path of the original cap polynomial. -/ path : List Gaussian
  /-- The path uses the original cap value at the retained requested depth and exact cell endpoints. -/ path_eq : path =
    dyadicIncrements (ArcArea.Sample.capValue original.sample) request.depth edge.left.parameter
    edge.right.parameter
  /-- The cached total and area of the original coarser cap path. -/ summary : IncrementArea.Summary path
  /-- The retained coarse total equals the original fine cap path total. -/ total_eq : summary.total =
    original.capSummary.total
  /-- The original fine and retained coarse areas differ by less than the target times fourth-power width. -/ area_error
    : Data.Gaussian.Norm.Basic.normSq (original.capSummary.area - summary.area) < target *
    (edge.right.parameter - edge.left.parameter) ^ 4

constructive_injectivity CoarseArea

/-- Only the new coarse path is evaluated. The supplied original source, cap polynomial, fine path, total and area are
consumed without rebuilding. -/
@[expose] def coarsen (request : SpatialRequest comparison
  target floor)
    (original : ComparedCell comparison source capSample depth)
    (later : request.depth ≤ depth) :
      CoarseArea request original := by
  let path := dyadicIncrements (ArcArea.Sample.capValue original.sample) request.depth
    edge.left.parameter edge.right.parameter
  let summary := IncrementArea.Summary.build path
  have totalEq : summary.total = original.capSummary.total := by
    rw [summary.total_eq]
    change Data.Gaussian.Norm.Sum.Basic.gaussianSum (dyadicIncrements _ _ _ _) = _
    rw [DyadicPrimitivePaths.dyadicIncrements_sum, (ArcArea.Sample.capValue_left original.sample),
      Data.Gaussian.Basic.sub_zero,
      (ArcArea.Sample.capValue_right original.sample), ComparedCell.cap_total original]
  have areaEq : summary.area = dyadicArea (ArcArea.Sample.capValue original.sample) request.depth
    edge.left.parameter edge.right.parameter := by
    rw [summary.area_eq]
    exact DyadicPrimitivePaths.pathArea_dyadicIncrements _ _ _ _ (ArcArea.Sample.capValue_left original.sample)
  refine ⟨later, path, rfl, summary, totalEq, ?_⟩
  rw [ComparedCell.cap_area original, areaEq]
  have estimate := DyadicAreaRefinement.dyadicArea_refinement_bound (ArcArea.Sample.capValue original.sample)
    request.bounds.slope_nonnegative
    (fun _ _ firstInside lastInside => request.bounds.increment_bound source original.sample firstInside lastInside)
    request.depth (depth - request.depth) ⟨le_rfl, cell.ordered.le⟩ ⟨cell.ordered.le, le_rfl⟩ cell.ordered.le
  rw [Data.Nat.Subtraction.add_sub_of_le later, ← request.bounds.areaScale_eq, ← request.error_eq] at estimate
  exact estimate.trans_lt (Arithmetic.mul_lt_mul_of_pos_right_direct request.accurate
    (Arithmetic.pow_pos_direct (Arithmetic.sub_pos_direct cell.ordered) 4))

end SpatialRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
