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

variable {genus count otherCount : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {otherCover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover otherData}
  (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) (common :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonCover cover otherCover)

/-- The original interval-count and source-slope scale for inserting common chart boundaries. -/
@[expose] def chartInsertionScale : Coordinate := 32 * ((2 * common.intervals.length - 1 : Nat) :
  Normalization.InverseRootPolynomial.Coordinate)^4 *
  (2 * (data.sourceSlope + otherData.sourceSlope + 4))

/-- The original chart insertion scale is nonnegative. -/
theorem chartInsertionScale_nonnegative : 0 ≤
  Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.chartInsertionScale common := by
  have count : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ ((2 * common.intervals.length - 1 : Nat) :
    Normalization.InverseRootPolynomial.Coordinate) := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have powered := Fraction.Order.Arithmetic.pow_nonneg_direct count 4
  have magnitude : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2 * (data.sourceSlope + otherData.sourceSlope
    + 4) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (add_nonneg data.sourceSlope_nonnegative
      otherData.sourceSlope_nonnegative) (by decide))
  have scaledCount := Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 32) powered
  unfold Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.chartInsertionScale
  exact Fraction.Order.Arithmetic.mul_nonneg_direct scaledCount magnitude

/-- Twice the sum of the original block comparison and chart insertion scales. -/
@[expose] def joinedBlockScale : Coordinate := 2 *
  (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBlockComparison.blockComparisonScale (common := common) +
  Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.chartInsertionScale common)

/-- The joined original block scale is nonnegative. -/
theorem joinedBlockScale_nonnegative : 0 ≤ Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.joinedBlockScale
  common :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBlockComparison.blockComparisonScale_nonnegative (common :=
    common))
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.chartInsertionScale_nonnegative common))

/-- The original block comparison scale is at most its joined scale. -/
theorem blockComparisonScale_le_joined :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBlockComparison.blockComparisonScale (common := common) ≤
  Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.joinedBlockScale common := by
  have sum := add_nonneg
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBlockComparison.blockComparisonScale_nonnegative (common :=
    common)) (Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.chartInsertionScale_nonnegative common)
  have doubled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
      decide : (1 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2) sum
  rw [Fraction.Field.one_mul] at doubled
  exact (le_add_of_nonneg_right
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.chartInsertionScale_nonnegative common)).trans doubled

set_option genInjectivity false in
/-- A common boundary request retaining its original preparation, paid block allowance and one sufficient spatial depth.

The actual chart request uses that same preparation and depth, with separate source and geometric error certificates. -/
structure BoundaryRequest (requested : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original boundary preparation retained by this request. -/ preparation :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation.ChartPreparation regular common
  /-- The cached original joined block comparison scale. -/ blockScale : Normalization.InverseRootPolynomial.Coordinate
  /-- The cached scale equals the original joined block scale. -/ blockScale_eq : blockScale =
    Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.joinedBlockScale common
  /-- The retained block scale is nonnegative. -/ blockScale_nonnegative : 0 ≤ blockScale
  /-- The retained positive common local comparison allowance. -/ allowance :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The allowance is the minimum of the original target fraction and weighted block allocation. -/ allowance_eq :
    allowance = min (requested / 32) (Rational.Budget.Weighted.allowance (requested / 2) blockScale)
  /-- The retained common allowance is positive. -/ positive : 0 < allowance
  /-- The cached sufficient spatial refinement depth. -/ depth : Nat
  /-- The depth is the original finite quarter-radius search result. -/ depth_eq : depth =
    Rational.Geometric.Search.firstQuarterBelow
    (max preparation.scale (16 * (max data.sourceSlope otherData.sourceSlope)^2)) floor allowance
  /-- The retained depth is at least the original required minimum. -/ minimum_le : floor ≤ depth
  /-- The original geometric quarter-radius charge meets the local allowance. -/ accurate :
    Rational.Geometric.Basic.quarterRadius preparation.scale depth < allowance
  /-- The original source-slope quarter-radius charge meets the local allowance. -/ source_accurate :
    Rational.Geometric.Basic.quarterRadius (16 * (max data.sourceSlope otherData.sourceSlope)^2) depth < allowance
  /-- The actual common chart request at the retained depth. -/ request :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest regular common depth allowance floor
  /-- The actual chart request retains exactly the original preparation. -/ preparation_eq : request.preparation =
    preparation

constructive_injectivity BoundaryRequest

namespace BoundaryRequest

/-- Allocate the original common allowance and cache one sufficient spatial search result with its actual chart request.
-/
@[expose] def build (preparation : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation.ChartPreparation regular
  common) (requested : Normalization.InverseRootPolynomial.Coordinate)
    (positive : 0 < requested) (floor : Nat) :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.BoundaryRequest regular common requested floor :=
  let blockScale := Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.joinedBlockScale common
  have blockNonnegative := Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.joinedBlockScale_nonnegative
    common
  let allowance := min (requested / 32) (Rational.Budget.Weighted.allowance (requested / 2) blockScale)
  have allowancePositive := Fraction.Order.Basic.lt_min (Fraction.Order.Field.div_pos_direct positive (by
      decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) < 32))
    (Rational.Budget.Weighted.allowance_positive (Fraction.Order.Field.div_pos_direct positive (by decide))
      blockNonnegative)
  let scale := max preparation.scale (16 * (max data.sourceSlope otherData.sourceSlope)^2)
  let depth := Rational.Geometric.Search.firstQuarterBelow scale floor allowance
  have accurate := Rational.Geometric.Search.firstQuarterBelow_accurate scale
    (preparation.nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)) floor allowance allowancePositive
  have scaleBound {value : Normalization.InverseRootPolynomial.Coordinate} (bounded : value ≤ scale) :
    Rational.Geometric.Basic.quarterRadius value depth < allowance := by
    refine (show Rational.Geometric.Basic.quarterRadius value depth ≤ Rational.Geometric.Basic.quarterRadius scale depth
      from ?_).trans_lt accurate
    rw [Rational.Geometric.Basic.quarterRadius_eq_mul_pow, Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct bounded
      (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) depth)
  ⟨preparation, blockScale, rfl, blockNonnegative, allowance, rfl, allowancePositive, depth, rfl,
    Rational.Geometric.Search.firstQuarterBelow_ge _ _ _,
    scaleBound (Fraction.Order.Basic.le_max_left _ _), scaleBound (Fraction.Order.Basic.le_max_right _ _),
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest.build regular common preparation depth allowance
      allowancePositive floor, rfl⟩

variable {regular common} {requested : Normalization.InverseRootPolynomial.Coordinate} {floor index : Nat}
  (planned : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.BoundaryRequest regular common
    requested floor)
  (evaluated : planned.request.Evaluation index)

/-- The exact original arc preparation of the retained planned request. -/
@[expose] def ArcPreparation :=
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.ArcComparisonPreparation.build
  planned.request.preparation
/-- The actual arc comparison on the retained request's evaluation. -/
@[expose] def ArcComparison :=
  (Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.BoundaryRequest.ArcPreparation planned).Comparison
  (evaluated := evaluated)

set_option genInjectivity false in
/-- The retained fan, joined arcs and block comparison with a cached original source boundary area and its requested
accuracy. -/
structure Certificate where
  /-- The actual retained fan request. -/ fanRequest :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest evaluated planned.allowance floor
  /-- The original fan acquisition at a sufficient stage. -/ fans : fanRequest.Bank
  /-- The actual joining of the retained acquired fans. -/ joined :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.Joined fanRequest fans
  /-- The original arc comparison on that joining. -/ comparison : planned.ArcComparison evaluated
  /-- The retained arc ceiling certificate. -/ ceiling :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.PreparedArcBound (evaluated := evaluated)
    comparison
  /-- The original geometric arc error certificate. -/ geometric :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.GeometricArcBound (evaluated := evaluated) ceiling
  /-- The actual retained arc error meets its local allowance. -/ arc_accurate : geometric.bound < planned.allowance
  /-- The retained block comparison on the same original boundary. -/ blocks :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBlockComparison.BlockBank evaluated
  /-- The actual block error meets the whole-boundary target. -/ blocks_accurate : blocks.error < requested
  /-- The cached original source open-boundary area. -/ area : Gaussian.Basic.Canonical
  /-- The cached area is exactly the original source open boundary. -/ area_eq : area =
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.sourceOpenBoundary evaluated fanRequest.fan.depth
  /-- The cached original boundary area meets the requested comparison target. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq area < requested

constructive_injectivity Certificate

/-- The actual retained geometric arc comparison meets the allocated local allowance. -/
theorem arc_accurate (comparison : planned.ArcComparison evaluated)
    (ceiling : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.PreparedArcBound (evaluated :=
      evaluated) comparison) (geometric :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.GeometricArcBound (evaluated := evaluated) ceiling)
      :
    geometric.bound < planned.allowance := by
  have scaleEq := geometric.preparation_scale evaluated rfl
  have preparationEq := congrArg (fun preparation :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation.ChartPreparation regular common => preparation.scale)
    planned.preparation_eq
  exact (geometric.bound_eq.trans
    (congrArg (fun scale => Rational.Geometric.Basic.quarterRadius scale planned.depth) (scaleEq.trans
      preparationEq))).trans_lt planned.accurate

/-- The complete fixed local comparison charge fits the supplied whole-boundary target. -/
theorem paid : 2 * (planned.allowance + 2 * (2 * (planned.allowance + planned.allowance) + planned.allowance)) ≤
  requested := by
  calc
    _ = 22 * planned.allowance := by ring1
    _ ≤ 32 * planned.allowance := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel)
      planned.positive.le
    _ ≤ 32 * (requested / 32) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (planned.allowance_eq.trans_le (Fraction.Order.Basic.min_le_left _ _)) (by decide +kernel)
    _ = requested := by rw [Fraction.Field.mul_comm]; exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)

/-- The actual retained block comparison fits the supplied whole-boundary target. -/
theorem blocks_accurate (blocks : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBlockComparison.BlockBank evaluated) :
  blocks.error < requested := by
  have before := blocks.error_target evaluated
  have larger := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.blockComparisonScale_le_joined common)
    planned.positive.le
  rw [← planned.blockScale_eq] at larger
  have before := before.trans larger
  have positive : 0 < requested / 32 := planned.positive.trans_le (planned.allowance_eq.trans_le
    (Fraction.Order.Basic.min_le_left _ _))
  have requestedPositive : 0 < requested := by
    have product := Fraction.Order.Arithmetic.mul_pos_direct positive (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) < 32)
    exact product.trans_eq (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel))
  have halfPositive := Fraction.Order.Field.div_pos_direct requestedPositive (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 2)
  have halfEq : requested / 2 + requested / 2 = requested :=
    (by ring1 : requested / 2 + requested / 2 = (requested / 2) * 2).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by
      decide))
  have halfLess := (Fraction.Field.zero_add _ ▸ Fraction.Order.Arithmetic.add_lt_add_right_direct halfPositive
    _).trans_eq halfEq
  exact before.trans_lt (((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (planned.allowance_eq.trans_le (Fraction.Order.Basic.min_le_right _ _)) planned.blockScale_nonnegative).trans
    (Rational.Budget.Weighted.mul_allowance_le halfPositive.le planned.blockScale_nonnegative)).trans_lt halfLess)

/-- Consume any certified shared sample bank at the selected chart request.
The geometric preparation was fixed before this bank's stage was chosen. -/
@[expose] def certify (fanRequest : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest evaluated
  planned.allowance floor)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) : planned.Certificate
      evaluated := by
  let fans := fanRequest.acquire branch
  let joined := Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.Bank.join fans branch
  let comparison := (Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.BoundaryRequest.ArcPreparation
    planned).acquire (evaluated := evaluated) branch
  let ceiling := Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.prepareArcBound evaluated
    comparison branch
  let geometric := Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.geometricArcBound evaluated ceiling
  let blocks := Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBlockComparison.blockBank evaluated
  have arcAccurate := Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.BoundaryRequest.arc_accurate
    planned evaluated comparison ceiling geometric
  have bound :=
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.FanBankRequest.Joined.geometric_source_boundary_bound
    evaluated joined geometric
  have replaced : 2 * (planned.allowance + 2 * (2 * (planned.allowance + planned.allowance) + geometric.bound)) ≤
      2 * (planned.allowance + 2 * (2 * (planned.allowance + planned.allowance) + planned.allowance)) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct le_rfl arcAccurate.le) (by decide))) (by decide)
  have accurate := bound.trans_le (replaced.trans
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.BoundaryRequest.paid planned))
  exact ⟨fanRequest, fans, joined, comparison, ceiling, geometric, arcAccurate, blocks,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary.BoundaryRequest.blocks_accurate planned
    evaluated blocks,
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.sourceOpenBoundary evaluated fanRequest.fan.depth,
      rfl, accurate⟩

end BoundaryRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary
