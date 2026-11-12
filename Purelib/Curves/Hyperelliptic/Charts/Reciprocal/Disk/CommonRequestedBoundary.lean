module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBlockComparison
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Rat.Fraction.Order

public section

/-! Requested open source-boundary comparison with an automatically chosen
original chart mesh. Outer radial and origin terms remain in the result. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus count otherCount : Nat} {curve : Basic.HyperellipticCurve genus}
  {differential other : Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : UniformReciprocalModels.Data patch count} {otherData :
    UniformReciprocalModels.Data otherPatch otherCount}
  {cover : UniformReciprocalCover.Cover data} {otherCover :
    UniformReciprocalCover.Cover otherData}
  (regular : RegularBounds.Data cap) (common :
    UniformReciprocalCommonCover.CommonCover cover otherCover)

/-- The original interval-count and source-slope scale for inserting common chart boundaries. -/
@[expose] def chartInsertionScale : Coordinate := 32 * ((2 * common.intervals.length - 1 : Nat) :
  Coordinate)^4 *
  (2 * (data.sourceSlope + otherData.sourceSlope + 4))

/-- The original chart insertion scale is nonnegative. -/
theorem chartInsertionScale_nonnegative : 0 ≤
  chartInsertionScale common := by
  have count : (0 : Coordinate) ≤ ((2 * common.intervals.length - 1 : Nat) :
    Coordinate) := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have powered := Arithmetic.pow_nonneg_direct count 4
  have magnitude : (0 : Coordinate) ≤ 2 * (data.sourceSlope + otherData.sourceSlope
    + 4) :=
    Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (add_nonneg data.sourceSlope_nonnegative
      otherData.sourceSlope_nonnegative) (by decide))
  have scaledCount := Arithmetic.mul_nonneg_direct (by
      decide +kernel : (0 : Coordinate) ≤ 32) powered
  unfold chartInsertionScale
  exact Arithmetic.mul_nonneg_direct scaledCount magnitude

/-- Twice the sum of the original block comparison and chart insertion scales. -/
@[expose] def joinedBlockScale : Coordinate := 2 *
  (CommonChartBlockComparison.blockComparisonScale (common := common) +
  chartInsertionScale common)

/-- The joined original block scale is nonnegative. -/
theorem joinedBlockScale_nonnegative : 0 ≤ joinedBlockScale
  common :=
  Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    (CommonChartBlockComparison.blockComparisonScale_nonnegative (common :=
    common))
    (chartInsertionScale_nonnegative common))

/-- The original block comparison scale is at most its joined scale. -/
theorem blockComparisonScale_le_joined :
  CommonChartBlockComparison.blockComparisonScale (common := common) ≤
  joinedBlockScale common := by
  have sum := add_nonneg
    (CommonChartBlockComparison.blockComparisonScale_nonnegative (common :=
    common)) (chartInsertionScale_nonnegative common)
  have doubled := Arithmetic.mul_le_mul_of_nonneg_right_direct (by
      decide : (1 : Coordinate) ≤ 2) sum
  rw [Fraction.Field.one_mul] at doubled
  exact (le_add_of_nonneg_right
    (chartInsertionScale_nonnegative common)).trans doubled

set_option genInjectivity false in
/-- A common boundary request retaining its original preparation, paid block allowance and one sufficient spatial depth.

The actual chart request uses that same preparation and depth, with separate source and geometric error certificates. -/
structure BoundaryRequest (requested : Coordinate) (floor : Nat) where
  /-- The original boundary preparation retained by this request. -/ preparation :
    CommonChartPreparation.ChartPreparation regular common
  /-- The cached original joined block comparison scale. -/ blockScale : Coordinate
  /-- The cached scale equals the original joined block scale. -/ blockScale_eq : blockScale =
    joinedBlockScale common
  /-- The retained block scale is nonnegative. -/ blockScale_nonnegative : 0 ≤ blockScale
  /-- The retained positive common local comparison allowance. -/ allowance :
    Coordinate
  /-- The allowance is the minimum of the original target fraction and weighted block allocation. -/ allowance_eq :
    allowance = min (requested / 32) (Rational.Budget.Weighted.allowance (requested / 2) blockScale)
  /-- The retained common allowance is positive. -/ positive : 0 < allowance
  /-- The cached sufficient spatial refinement depth. -/ depth : Nat
  /-- The depth is the original finite quarter-radius search result. -/ depth_eq : depth =
    Search.firstQuarterBelow
    (max preparation.scale (16 * (max data.sourceSlope otherData.sourceSlope)^2)) floor allowance
  /-- The retained depth is at least the original required minimum. -/ minimum_le : floor ≤ depth
  /-- The original geometric quarter-radius charge meets the local allowance. -/ accurate :
    Basic.quarterRadius preparation.scale depth < allowance
  /-- The original source-slope quarter-radius charge meets the local allowance. -/ source_accurate :
    Basic.quarterRadius (16 * (max data.sourceSlope otherData.sourceSlope)^2) depth < allowance
  /-- The actual common chart request at the retained depth. -/ request :
    CommonChartBank.ChartRequest regular common depth allowance floor
  /-- The actual chart request retains exactly the original preparation. -/ preparation_eq : request.preparation =
    preparation

constructive_injectivity BoundaryRequest

namespace BoundaryRequest

/-- Allocate the original common allowance and cache one sufficient spatial search result with its actual chart request.
-/
@[expose] def build (preparation : CommonChartPreparation.ChartPreparation regular
  common) (requested : Coordinate)
    (positive : 0 < requested) (floor : Nat) :
      BoundaryRequest regular common requested floor :=
  let blockScale := joinedBlockScale common
  have blockNonnegative := joinedBlockScale_nonnegative
    common
  let allowance := min (requested / 32) (Rational.Budget.Weighted.allowance (requested / 2) blockScale)
  have allowancePositive := Basic.lt_min (Field.div_pos_direct positive (by
      decide +kernel : (0 : Coordinate) < 32))
    (Rational.Budget.Weighted.allowance_positive (Field.div_pos_direct positive (by decide))
      blockNonnegative)
  let scale := max preparation.scale (16 * (max data.sourceSlope otherData.sourceSlope)^2)
  let depth := Search.firstQuarterBelow scale floor allowance
  have accurate := Search.firstQuarterBelow_accurate scale
    (preparation.nonnegative.trans (Basic.le_max_left _ _)) floor allowance allowancePositive
  have scaleBound {value : Coordinate} (bounded : value ≤ scale) :
    Basic.quarterRadius value depth < allowance := by
    refine (show Basic.quarterRadius value depth ≤ Basic.quarterRadius scale depth
      from ?_).trans_lt accurate
    rw [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow]
    exact Arithmetic.mul_le_mul_of_nonneg_right_direct bounded
      (Arithmetic.pow_nonneg_direct (by decide) depth)
  ⟨preparation, blockScale, rfl, blockNonnegative, allowance, rfl, allowancePositive, depth, rfl,
    Search.firstQuarterBelow_ge _ _ _,
    scaleBound (Basic.le_max_left _ _), scaleBound (Basic.le_max_right _ _),
    CommonChartBank.ChartRequest.build regular common preparation depth allowance
      allowancePositive floor, rfl⟩

variable {regular common} {requested : Coordinate} {floor index : Nat}
  (planned : BoundaryRequest regular common
    requested floor)
  (evaluated : planned.request.Evaluation index)

/-- The exact original arc preparation of the retained planned request. -/
@[expose] def ArcPreparation :=
  CommonChartArcComparison.ArcComparisonPreparation.build
  planned.request.preparation
/-- The actual arc comparison on the retained request's evaluation. -/
@[expose] def ArcComparison :=
  (ArcPreparation planned).Comparison
  (evaluated := evaluated)

set_option genInjectivity false in
/-- The retained fan, joined arcs and block comparison with a cached original source boundary area and its requested
accuracy. -/
structure Certificate where
  /-- The actual retained fan request. -/ fanRequest :
    CommonChartFanBank.FanBankRequest evaluated planned.allowance floor
  /-- The original fan acquisition at a sufficient stage. -/ fans : fanRequest.Bank
  /-- The actual joining of the retained acquired fans. -/ joined :
    CommonChartJoinedFans.FanBankRequest.Joined fanRequest fans
  /-- The original arc comparison on that joining. -/ comparison : planned.ArcComparison evaluated
  /-- The retained arc ceiling certificate. -/ ceiling :
    CommonChartCoordinateSteps.Evaluation.PreparedArcBound (evaluated := evaluated)
    comparison
  /-- The original geometric arc error certificate. -/ geometric :
    CommonChartGeometricError.GeometricArcBound (evaluated := evaluated) ceiling
  /-- The actual retained arc error meets its local allowance. -/ arc_accurate : geometric.bound < planned.allowance
  /-- The retained block comparison on the same original boundary. -/ blocks :
    CommonChartBlockComparison.BlockBank evaluated
  /-- The actual block error meets the whole-boundary target. -/ blocks_accurate : blocks.error < requested
  /-- The cached original source open-boundary area. -/ area : Gaussian.Basic.Canonical
  /-- The cached area is exactly the original source open boundary. -/ area_eq : area =
    CommonChartArcComparison.sourceOpenBoundary evaluated fanRequest.fan.depth
  /-- The cached original boundary area meets the requested comparison target. -/ accurate :
    Gaussian.Norm.Basic.normSq area < requested

constructive_injectivity Certificate

/-- The actual retained geometric arc comparison meets the allocated local allowance. -/
theorem arc_accurate (comparison : planned.ArcComparison evaluated)
    (ceiling : CommonChartCoordinateSteps.Evaluation.PreparedArcBound (evaluated :=
      evaluated) comparison) (geometric :
      CommonChartGeometricError.GeometricArcBound (evaluated := evaluated) ceiling)
      :
    geometric.bound < planned.allowance := by
  have scaleEq := geometric.preparation_scale evaluated rfl
  have preparationEq := congrArg (fun preparation :
    CommonChartPreparation.ChartPreparation regular common => preparation.scale)
    planned.preparation_eq
  exact (geometric.bound_eq.trans
    (congrArg (fun scale => Basic.quarterRadius scale planned.depth) (scaleEq.trans
      preparationEq))).trans_lt planned.accurate

/-- The complete fixed local comparison charge fits the supplied whole-boundary target. -/
theorem paid : 2 * (planned.allowance + 2 * (2 * (planned.allowance + planned.allowance) + planned.allowance)) ≤
  requested := by
  calc
    _ = 22 * planned.allowance := by ring1
    _ ≤ 32 * planned.allowance := Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel)
      planned.positive.le
    _ ≤ 32 * (requested / 32) := Arithmetic.mul_le_mul_of_nonneg_left_direct
      (planned.allowance_eq.trans_le (Basic.min_le_left _ _)) (by decide +kernel)
    _ = requested := by rw [Fraction.Field.mul_comm]; exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)

/-- The actual retained block comparison fits the supplied whole-boundary target. -/
theorem blocks_accurate (blocks : CommonChartBlockComparison.BlockBank evaluated) :
  blocks.error < requested := by
  have before := blocks.error_target evaluated
  have larger := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (blockComparisonScale_le_joined common)
    planned.positive.le
  rw [← planned.blockScale_eq] at larger
  have before := before.trans larger
  have positive : 0 < requested / 32 := planned.positive.trans_le (planned.allowance_eq.trans_le
    (Basic.min_le_left _ _))
  have requestedPositive : 0 < requested := by
    have product := Arithmetic.mul_pos_direct positive (by
        decide +kernel : (0 : Coordinate) < 32)
    exact product.trans_eq (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel))
  have halfPositive := Field.div_pos_direct requestedPositive (by
      decide : (0 : Coordinate) < 2)
  have halfEq : requested / 2 + requested / 2 = requested :=
    (by ring1 : requested / 2 + requested / 2 = (requested / 2) * 2).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by
      decide))
  have halfLess := (Fraction.Field.zero_add _ ▸ Arithmetic.add_lt_add_right_direct halfPositive
    _).trans_eq halfEq
  exact before.trans_lt (((Arithmetic.mul_le_mul_of_nonneg_left_direct
    (planned.allowance_eq.trans_le (Basic.min_le_right _ _)) planned.blockScale_nonnegative).trans
    (Rational.Budget.Weighted.mul_allowance_le halfPositive.le planned.blockScale_nonnegative)).trans_lt halfLess)

/-- Consume any certified shared sample bank at the selected chart request.
The geometric preparation was fixed before this bank's stage was chosen. -/
@[expose] def certify (fanRequest : CommonChartFanBank.FanBankRequest evaluated
  planned.allowance floor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) : planned.Certificate
      evaluated := by
  let fans := fanRequest.acquire branch
  let joined := CommonChartJoinedFans.FanBankRequest.Bank.join fans branch
  let comparison := (ArcPreparation
    planned).acquire (evaluated := evaluated) branch
  let ceiling := CommonChartCoordinateSteps.Evaluation.prepareArcBound evaluated
    comparison branch
  let geometric := CommonChartGeometricError.geometricArcBound evaluated ceiling
  let blocks := CommonChartBlockComparison.blockBank evaluated
  have arcAccurate := arc_accurate
    planned evaluated comparison ceiling geometric
  have bound :=
    CommonChartGeometricError.FanBankRequest.Joined.geometric_source_boundary_bound
    evaluated joined geometric
  have replaced : 2 * (planned.allowance + 2 * (2 * (planned.allowance + planned.allowance) + geometric.bound)) ≤
      2 * (planned.allowance + 2 * (2 * (planned.allowance + planned.allowance) + planned.allowance)) :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct le_rfl (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct le_rfl arcAccurate.le) (by decide))) (by decide)
  have accurate := bound.trans_le (replaced.trans
    (paid planned))
  exact ⟨fanRequest, fans, joined, comparison, ceiling, geometric, arcAccurate, blocks,
    blocks_accurate planned
    evaluated blocks,
    CommonChartArcComparison.sourceOpenBoundary evaluated fanRequest.fan.depth,
      rfl, accurate⟩

end BoundaryRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary
