module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PathArea
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Tactic.Ring

public section

/-!
# Requested cap area on a complete prepared side

The same retained samples supply cap endpoint readings, polynomial paths and
actual integration blocks. Concatenation pays internal areas and the polygon
of parent totals. The request controls both integral and full area errors.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration.Path
open Purelib.Integration.Polynomial.Gaussian.Path.Basic
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
open Purelib.Riemann.Normalization
open Purelib.Riemann.Paths

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (pathArea Summary)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectBlockRefinement)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover (Parent Bank Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank (Requests Samples)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives (areaSlope
  areaSlope_nonnegative)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives.Sample (areaPairs
  areaPairs_integral area_bounds)

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Differential genus} {count : Nat}

namespace Bank

/-- Take the finite maximum of the original cap coefficient and movement slopes in the retained parent bank. -/
@[expose] public def areaSlopeMaximum : {parents : List (PathCover.Parent curve differential)} → PathCover.Bank cap
  differential count parents → InverseRootPolynomial.Coordinate
  | _, .nil => 0
  | _, .cons data remaining => max (ReciprocalCapPreparedPrimitives.areaSlope data)
    (areaSlopeMaximum remaining)

/-- The maximum original parent area slope is nonnegative. -/
theorem areaSlopeMaximum_nonnegative {parents : List (PathCover.Parent curve differential)} (bank : PathCover.Bank cap
  differential count parents) :
    0 ≤ areaSlopeMaximum bank := by
  cases bank with
  | nil => exact le_rfl
  | cons data _ =>
    exact (ReciprocalCapPreparedPrimitives.areaSlope_nonnegative data).trans (Fraction.Order.Basic.le_max_left _ _)

variable {index : Nat} {box : Purelib.Geometry.Rational.Box} {capSample :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- Materialize each local pair list once before projecting the two paths. -/
@[expose] public def areaBlocks : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    Bank.Samples requests capSample → List (List InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)
  | _, .nil, _, _, _, _ => []
  | _, .cons _ _, _, _, _, samples =>
      let pairs := (ReciprocalCapPreparedPrimitives.Sample.areaPairs samples.1)
      (pairs.map Prod.fst, pairs.map Prod.snd) ::
        areaBlocks samples.2

/-- There is one retained pair of actual increment paths for every original parent. -/
theorem areaBlocks_length : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    (samples : Bank.Samples requests capSample) → (areaBlocks
      samples).length = parents.length
  | _, .nil, _, _, _, _ => rfl
  | _, .cons _ _, _, _, _, samples => congrArg Nat.succ
    (areaBlocks_length samples.2)

/-- The concatenated right paths are exactly the increments of the original retained integration blocks. -/
theorem areaBlocks_integral : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
      (samples : Bank.Samples requests capSample) →
    ((areaBlocks samples).map Prod.snd).flatten =
      PathArea.increments
      (PathModel.mk ((Samples.blocks samples).children.map CenteredEdge.model))
  | _, .nil, _, _, _, _ => rfl
  | _, .cons _ _, _, _, _, samples => by
      rewrite [areaBlocks, List.map_cons, List.flatten_cons,
        (ReciprocalCapPreparedPrimitives.Sample.areaPairs_integral samples.1),
        areaBlocks_integral samples.2,
        Samples.blocks, DirectBlockRefinement.children, Purelib.Data.List.Map.map_append, PathArea.increments]
      dsimp only [PathArea.increments]
      rewrite [Purelib.Data.List.Map.map_append]
      exact Eq.refl _

/-- Every retained parent path pair satisfies its full internal-area, total-error and norm bounds at the shared later
stage. -/
theorem areaBlocks_bounds : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    (samples : Bank.Samples requests capSample) → Requests.index requests ≤ index →
    (slope : InverseRootPolynomial.Coordinate) →
      areaSlopeMaximum bank ≤ slope → ∀ pair ∈
      areaBlocks samples,
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea pair.1 - IncrementArea.pathArea pair.2) ≤ 256 *
      target * (slope + 3 * target) ∧
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ 4 * target ∧
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1) ≤ 4 * (slope + 3 *
      target) ∧
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ 4 * (slope + 3 *
      target)
  | _, .nil, _, _, _, _, _, _, _, _, member => by cases member
  | _, .cons _ _, target, _, requests, samples, later, slope, upper, pair, member => by
      rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
      · have bounded := ReciprocalCapPreparedPrimitives.Sample.area_bounds samples.1
          ((Purelib.Data.Nat.Order.le_max_left _ _).trans later)
        have shifted := add_le_add ((Fraction.Order.Basic.le_max_left _ _).trans upper) (le_rfl (a := 3 * target))
        exact ⟨bounded.1.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct shifted
            (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) requests.1.positive.le)), bounded.2.1,
          bounded.2.2.1.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct shifted (by decide)),
          bounded.2.2.2.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct shifted (by decide))⟩
      · exact areaBlocks_bounds samples.2
          ((Purelib.Data.Nat.Order.le_max_right _ _).trans later) slope ((Fraction.Order.Basic.le_max_right _ _).trans
          upper) pair member

end Bank

set_option genInjectivity false in
/-- The cached count scale pays both the square and fourth power arising from the full concatenation formula. -/
structure SideAreaBudget (slope : InverseRootPolynomial.Coordinate) (count : Nat) (totalTarget areaTarget :
  InverseRootPolynomial.Coordinate) where
  /-- The cached finite parent-count cost for complete path concatenation. -/ scale : InverseRootPolynomial.Coordinate
  /-- The count scale is the sum of the square and fourth power of the original parent count. -/ scale_eq : scale =
    (count : InverseRootPolynomial.Coordinate) ^ 2 + (count : InverseRootPolynomial.Coordinate) ^ 4
  /-- The common positive local tolerance paying both original side targets. -/ tolerance :
    InverseRootPolynomial.Coordinate
  /-- The tolerance is capped by one and both original target-to-cost ratios. -/ tolerance_eq : tolerance = min 1 (min
    (totalTarget / (8 * (scale + 1))) (areaTarget / (1024 * (scale + 1) * (slope + 3))))
  /-- The retained local tolerance is strictly positive. -/ positive : 0 < tolerance
  /-- The common local tolerance pays the squared original parent count in the total discrepancy. -/ total_paid : 4 *
    (count : InverseRootPolynomial.Coordinate) ^ 2 * tolerance < totalTarget
  /-- The common local tolerance pays all internal-area and parent-total cross terms. -/ area_paid : 512 * scale *
    tolerance * (slope + 3 * tolerance) < areaTarget

constructive_injectivity SideAreaBudget

namespace SideAreaBudget

/-- Select one positive local tolerance paying the exact original parent-count costs and both complete-side targets. -/
@[expose] public def build (slope : InverseRootPolynomial.Coordinate) (nonnegative : 0 ≤ slope) (count : Nat)
  (totalTarget areaTarget : InverseRootPolynomial.Coordinate)
    (totalPositive : 0 < totalTarget) (areaPositive : 0 < areaTarget) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.SideAreaBudget slope count totalTarget areaTarget := by
  let scale := (count : InverseRootPolynomial.Coordinate) ^ 2 + (count : InverseRootPolynomial.Coordinate) ^ 4
  have scaleNonnegative : 0 ≤ scale := add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4)
  have shifted : 0 < scale + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct scaleNonnegative (by decide)
  have slopePositive : 0 < slope + 3 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct nonnegative (by
    decide)
  have totalDenominator : 0 < 8 * (scale + 1) := Fraction.Order.Arithmetic.mul_pos_direct (by decide) shifted
  have areaDenominator : 0 < 1024 * (scale + 1) * (slope + 3) :=
    Fraction.Order.Arithmetic.mul_pos_direct (Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel) shifted)
      slopePositive
  let tolerance := min 1 (min (totalTarget / (8 * (scale + 1))) (areaTarget / (1024 * (scale + 1) * (slope + 3))))
  have positive : 0 < tolerance := Fraction.Order.Basic.lt_min (by decide) (Fraction.Order.Basic.lt_min
    (Fraction.Order.Field.div_pos_direct totalPositive totalDenominator)
    (Fraction.Order.Field.div_pos_direct areaPositive areaDenominator))
  have small : tolerance ≤ 1 := Fraction.Order.Basic.min_le_left _ _
  have totalLe : tolerance ≤ totalTarget / (8 * (scale + 1)) := (Fraction.Order.Basic.min_le_right _ _).trans
    (Fraction.Order.Basic.min_le_left _ _)
  have areaLe : tolerance ≤ areaTarget / (1024 * (scale + 1) * (slope + 3)) := (Fraction.Order.Basic.min_le_right _
    _).trans (Fraction.Order.Basic.min_le_right _ _)
  refine ⟨scale, rfl, tolerance, rfl, positive, ?_, ?_⟩
  · have squareLe : (count : InverseRootPolynomial.Coordinate) ^ 2 ≤ scale + 1 :=
      (Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _ (Fraction.Order.Arithmetic.pow_nonneg_direct
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4)).trans
          (Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _ (by decide))
    calc
      _ ≤ 4 * (scale + 1) * tolerance := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareLe (by decide)) positive.le
      _ < (8 * (scale + 1)) * tolerance := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct (by
            decide : (4 : InverseRootPolynomial.Coordinate) < 8) shifted) positive
      _ ≤ (8 * (scale + 1)) * (totalTarget / (8 * (scale + 1))) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totalLe totalDenominator.le
      _ = totalTarget := by
        rw [Fraction.Field.mul_comm]
        exact Fraction.Field.div_mul_cancel_of_ne _ _ totalDenominator.ne'
  · have slopeLe : slope + 3 * tolerance ≤ slope + 3 := by
      simpa only [Fraction.Field.mul_one_direct] using
        add_le_add le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small (by
            decide : (0 : InverseRootPolynomial.Coordinate) ≤ 3))
    calc
      _ ≤ 512 * scale * tolerance * (slope + 3) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct slopeLe
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) scaleNonnegative) positive.le)
      _ ≤ 512 * (scale + 1) * tolerance * (slope + 3) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _ (by decide)) (by decide +kernel))
              positive.le) slopePositive.le
      _ = (512 * (scale + 1) * (slope + 3)) * tolerance := by ring1
      _ < (1024 * (scale + 1) * (slope + 3)) * tolerance :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
          (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
            (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct (by
                decide +kernel : (512 : InverseRootPolynomial.Coordinate) < 1024) shifted) slopePositive) positive
      _ ≤ (1024 * (scale + 1) * (slope + 3)) * (areaTarget / (1024 * (scale + 1) * (slope + 3))) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct areaLe areaDenominator.le
      _ = areaTarget := by
        rw [Fraction.Field.mul_comm]
        exact Fraction.Field.div_mul_cancel_of_ne _ _ areaDenominator.ne'

end SideAreaBudget

variable {first last : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}
  {path : Polynomial.Geometry.ClearPath
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve) collar.box first last}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval first)}

set_option genInjectivity false in
/-- A complete cap-side polynomial request retaining the original parent bank and common stage.

The cached maximum slope and exact parent count determine one tolerance paying both total and full-area discrepancies.
-/
structure PolynomialRequest (data : PathCover.Data cap path owner differential) (totalTarget areaTarget :
  InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The cached largest area slope among the original retained parents. -/ slope : InverseRootPolynomial.Coordinate
  /-- The cached slope equals the exact maximum on the original parent bank. -/ slope_eq : slope =
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaSlopeMaximum data.bank
  /-- The retained total and area budget for this original parent count and slope. -/ budget :
    SideAreaBudget slope data.parentCount totalTarget areaTarget
  /-- The original parent request bank using the retained common tolerance. -/ requests : Bank.Requests data.bank
    budget.tolerance floor
  /-- The common polynomial stage for these exact retained parent requests. -/ index : Nat
  /-- The cached stage is the maximum required by the original request bank. -/ index_eq : index = Requests.index
    requests

constructive_injectivity PolynomialRequest

namespace PolynomialRequest

/-- Retain the original cap parent bank, fixed slope budget and common requested polynomial stage. -/
@[expose] public def build (data : PathCover.Data cap path owner differential) (totalTarget areaTarget :
  InverseRootPolynomial.Coordinate)
    (totalPositive : 0 < totalTarget) (areaPositive : 0 < areaTarget) (floor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.PolynomialRequest data totalTarget areaTarget floor :=
  let slope := Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaSlopeMaximum data.bank
  let budget := Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.SideAreaBudget.build slope
    (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaSlopeMaximum_nonnegative data.bank) data.parentCount
    totalTarget areaTarget totalPositive areaPositive
  let requests := Requests.build data.bank budget.tolerance budget.positive floor data.cache.proper
  ⟨slope, rfl, budget, requests, Requests.index requests, rfl⟩

variable {data : Data cap path owner differential}
  {totalTarget areaTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The retained polynomial request stage respects the original caller floor. -/
theorem floor_le (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.PolynomialRequest data totalTarget
  areaTarget floor) : floor ≤ request.index := by
  rw [request.index_eq]
  exact Requests.floor_le request.requests

/-- The complete retained cap polynomial and integrator paths meet the original full-area target. -/
theorem area_accurate (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.PolynomialRequest data totalTarget
  areaTarget floor) {index : Nat} {box : Rational.Box}
    {capSample : Primitives.Sample cap differential index box} (samples : Bank.Samples request.requests capSample)
    (later : request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea
      ((Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaBlocks samples).map Prod.fst).flatten -
      IncrementArea.pathArea ((Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaBlocks samples).map
      Prod.snd).flatten) < areaTarget := by
  have slopeNonnegative : 0 ≤ request.slope := request.slope_eq ▸
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaSlopeMaximum_nonnegative data.bank
  have bounded := Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaBlocks_bounds samples (request.index_eq ▸
    later) request.slope request.slope_eq.ge
  have estimate := IncrementAreaComparison.blocks_area_difference_bound
    (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaBlocks samples)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) request.budget.positive.le)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg slopeNonnegative (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        request.budget.positive.le)))
    (fun pair member => (bounded pair member).1) (fun pair member => (bounded pair member).2.1)
    (fun pair member => (bounded pair member).2.2.1) (fun pair member => (bounded pair member).2.2.2)
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaBlocks_length, data.parents_length] at estimate
  apply estimate.trans_lt
  have equal : 2 * ((data.parentCount : InverseRootPolynomial.Coordinate) ^ 2 * (256 * request.budget.tolerance *
    (request.slope + 3 * request.budget.tolerance)) +
      16 * (data.parentCount : InverseRootPolynomial.Coordinate) ^ 4 * (4 * request.budget.tolerance) * (4 *
        (request.slope + 3 * request.budget.tolerance))) =
      512 * request.budget.scale * request.budget.tolerance * (request.slope + 3 * request.budget.tolerance) := by
    rw [request.budget.scale_eq]
    ring1
  rw [equal]
  exact request.budget.area_paid

/-- The complete retained cap polynomial and integrator totals meet the original integral target. -/
theorem total_accurate (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.PolynomialRequest data totalTarget
  areaTarget floor) {index : Nat} {box : Rational.Box}
    {capSample : Primitives.Sample cap differential index box} (samples : Bank.Samples request.requests capSample)
    (later : request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (((Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaBlocks samples).map Prod.fst).flatten) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (((Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaBlocks samples).map Prod.snd).flatten)) <
      totalTarget := by
  have bounded := Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaBlocks_bounds samples (request.index_eq ▸
    later) request.slope request.slope_eq.ge
  have estimate := PathRequests.row_error_le ((Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaBlocks
    samples).map (fun pair => (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2)))
    (4 * request.budget.tolerance) (by
      intro row member
      obtain ⟨pair, inPairs, equal⟩ := Map.mem_map.mp member
      rw [← equal]
      exact (bounded pair inPairs).2.1)
  repeat' rewrite [Purelib.Data.List.Map.map_map] at estimate
  dsimp only [Function.comp_def] at estimate
  rewrite [Purelib.Data.List.Map.length_map, Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaBlocks_length,
    data.parents_length] at estimate
  rw [IncrementArea.sum_flatten, IncrementArea.sum_flatten]
  repeat' rewrite [Purelib.Data.List.Map.map_map] <;> dsimp only [Function.comp_def]
  exact estimate.trans_lt ((by ring1 : (data.parentCount : InverseRootPolynomial.Coordinate) ^ 2 * (4 *
    request.budget.tolerance) =
    4 * (data.parentCount : InverseRootPolynomial.Coordinate) ^ 2 * request.budget.tolerance) ▸
      request.budget.total_paid)

set_option genInjectivity false in
/-- The two literal paths, their cached summaries and the complete actual refinement share the same sample bank. Open
total errors remain explicit. -/
structure PolynomialEvaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.PolynomialRequest data
  totalTarget areaTarget floor) {index : Nat} {box : Rational.Box}
    (capSample : Primitives.Sample cap differential index box) where
  /-- The retained parent evaluations on this exact shared cap polynomial. -/ samples : Bank.Samples request.requests
    capSample
  /-- The cached original paired cap polynomial and integration paths. -/ pairs : List (List
    InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)
  /-- The paired paths are exactly the original retained sample bank's area blocks. -/ pairs_eq : pairs =
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaBlocks samples
  /-- There is one paired block for each original cached parent. -/ count_eq : pairs.length = data.parentCount
  /-- The complete retained refinement on the original integration parent list. -/ blocks :
    PreparedDirectDyadicRefinements.DirectBlockRefinement data.cache.parents
  /-- The retained refinement is exactly the block bank extracted from these same samples. -/ blocks_eq : blocks =
    Samples.blocks samples
  /-- The cached finite total and area summary of the original cap polynomial path. -/ left : IncrementArea.Summary
    (pairs.map Prod.fst).flatten
  /-- The cached finite total and area summary of the original integration path. -/ right : IncrementArea.Summary
    (pairs.map Prod.snd).flatten
  /-- The cached right path is exactly the increment path of the retained original refinement. -/ right_path :
    (pairs.map Prod.snd).flatten = PathArea.increments (PathModel.mk (blocks.children.map CenteredEdge.model))
  /-- The cached right total equals the actual original integration sample. -/ right_total : right.total = (PathModel.mk
    (blocks.children.map CenteredEdge.model)).integralSample
  /-- The cached complete totals differ by less than the original integral target. -/ total_close :
    Data.Gaussian.Norm.Basic.normSq (left.total - right.total) < totalTarget
  /-- The cached complete areas differ by less than the original area target. -/ area_close :
    Data.Gaussian.Norm.Basic.normSq (left.area - right.area) < areaTarget

constructive_injectivity PolynomialEvaluation

/-- Evaluate the original request bank once and cache its exact integration blocks, paired paths and paid total and area
summaries. -/
@[expose] public def evaluatePolynomial (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.PolynomialRequest
  data totalTarget areaTarget floor) {index : Nat} {box : Rational.Box}
    (capSample : Primitives.Sample cap differential index box) (later : request.index ≤ index) :
      PolynomialEvaluation request capSample :=
  let samples := Samples.build request.requests capSample (request.index_eq ▸ later)
  let pairs := Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaBlocks samples
  let blocks := Samples.blocks samples
  let left := IncrementArea.Summary.build (pairs.map Prod.fst).flatten
  let right := IncrementArea.Summary.build (pairs.map Prod.snd).flatten
  have rightTotal : right.total = (PathModel.mk (blocks.children.map CenteredEdge.model)).integralSample := by
    rw [right.total_eq, Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaBlocks_integral,
      PathArea.increments_sum]
  ⟨samples, pairs, rfl, (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaBlocks_length samples).trans
    data.parents_length, blocks, rfl,
    left, right, Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank.areaBlocks_integral samples, rightTotal,
    (by rw [left.total_eq, right.total_eq]; exact request.total_accurate samples later),
    (by rw [left.area_eq, right.area_eq]; exact request.area_accurate samples later)⟩

end PolynomialRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
