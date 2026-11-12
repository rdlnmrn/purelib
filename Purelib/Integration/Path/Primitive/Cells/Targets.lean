module

public import Purelib.Integration.Path.Primitive.Cells
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Computed requests for original finite primitive paths

The original cell count determines a positive local allocation before any
later source model is constructed. The same allocation pays the finite
primitive-cell Cauchy estimate. A retained displacement cost determines a
strictly positive source target whose product pays that local allocation.
-/

public section

namespace Purelib.Integration.Path.Primitive.PrimitiveEdge.CellEndpoints

open Purelib
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Approximation.Rational.Geometric
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Data.Gaussian

set_option genInjectivity false in
/-- Cached source allocations for one original finite lifted path and actual geometric request.

The original cell count is retained once. Its exact rational square and a
positive increment determine the denominator of the local allocations.
The resulting payment controls the actual count-squared primitive error;
no caller-supplied shrinking integral budget is an input. -/
structure Targets {sheets : Nat} {start finish : LiftedPoint sheets}
    (original : LiftedPath sheets start finish) (stage : Nat) where
  /-- The actual original finite path's retained cell count. -/
  count : Nat
  /-- The count belongs to the original lifted path. -/
  count_eq : count = original.cellCount
  /-- The cached exact rational square of that original count. -/
  countSquare : Rational
  /-- Both count factors belong to the same original finite count. -/
  countSquare_eq : countSquare = (count : Rational) * (count : Rational)
  /-- The positive increment of the actual original count cost. -/
  cost : Rational
  /-- The increment retains the same original squared count. -/
  cost_eq : cost = countSquare + 1
  /-- The retained original geometric target budget. -/
  budget : Rational
  /-- The budget is the actual unit-scale quarter-radius request. -/
  budget_eq : budget = Basic.quarterRadius 1 stage
  /-- The cached positive denominator for both local allocations. -/
  denominator : Rational
  /-- The denominator pays the actual finite primitive Cauchy factors. -/
  denominator_eq : denominator = 16 * cost
  /-- The derivative-residual allocation for every original cell. -/
  localBound : Rational
  /-- The derivative allocation consumes the retained original budget and denominator. -/
  localBound_eq : localBound = budget / denominator
  /-- The endpoint-reading allocation for every original vertex occurrence. -/
  endpoint : Rational
  /-- The endpoint allocation reuses the same computed scalar allocation. -/
  endpoint_eq : endpoint = localBound

constructive_injectivity Targets

namespace Targets

variable {sheets : Nat} {start finish : LiftedPoint sheets}
  {original : LiftedPath sheets start finish} {stage : Nat}

/-- Compute source and endpoint allocations from the original actual cell count and geometric request. -/
@[expose] def build (original : LiftedPath sheets start finish) (stage : Nat) : Targets original stage :=
  let count := original.cellCount
  let countSquare := (count : Rational) * (count : Rational)
  let cost := countSquare + 1
  let budget := Basic.quarterRadius 1 stage
  let denominator := 16 * cost
  let localBound := budget / denominator
  ⟨count, rfl, countSquare, rfl, cost, rfl, budget, rfl, denominator, rfl, localBound, rfl, localBound, rfl⟩

/-- Reuse the same computed scalar allocations on another original path with the same retained cell count.

The new path receives its own count certificate. Every executable scalar
cache is retained from the original request; this operation asserts no
agreement between path endpoints, root owners or primitive readings. -/
@[expose] def onPath (targets : Targets original stage)
    {nextStart nextFinish : LiftedPoint sheets} (next : LiftedPath sheets nextStart nextFinish)
    (sameCount : next.cellCount = original.cellCount) : Targets next stage :=
  ⟨targets.count, targets.count_eq.trans sameCount.symm, targets.countSquare, targets.countSquare_eq,
    targets.cost, targets.cost_eq, targets.budget, targets.budget_eq, targets.denominator, targets.denominator_eq,
    targets.localBound, targets.localBound_eq, targets.endpoint, targets.endpoint_eq⟩

/-- Transporting an original computed request to an equal-count path gives that path's computed request. -/
theorem onPath_computed (targets : Targets original stage)
    {nextStart nextFinish : LiftedPoint sheets} (next : LiftedPath sheets nextStart nextFinish)
    (sameCount : next.cellCount = original.cellCount) (computed : targets = build original stage) :
    targets.onPath next sameCount = build next stage := by
  rewrite [computed]
  dsimp only [onPath, build]
  congr 1 <;> rewrite [← sameCount] <;> rfl

/-- The retained original count-square cost is nonnegative. -/
theorem countSquare_nonnegative (targets : Targets original stage) : 0 ≤ targets.countSquare := by
  rewrite [targets.countSquare_eq]
  exact Order.Arithmetic.mul_nonneg_direct (Cast.Order.natCast_le_direct (Nat.zero_le _))
    (Cast.Order.natCast_le_direct (Nat.zero_le _))

/-- The incremented original count cost is strictly positive. -/
theorem cost_positive (targets : Targets original stage) : 0 < targets.cost := by
  rewrite [targets.cost_eq]
  exact Order.Arithmetic.add_pos_of_nonneg_of_pos_direct targets.countSquare_nonnegative (by decide)

/-- The original geometric request is strictly positive. -/
theorem budget_positive (targets : Targets original stage) : 0 < targets.budget := by
  rewrite [targets.budget_eq]
  exact Basic.quarterRadius_pos (by decide) _

/-- The cached denominator of the original local allocation is strictly positive. -/
theorem denominator_positive (targets : Targets original stage) : 0 < targets.denominator := by
  rewrite [targets.denominator_eq]
  exact Order.Arithmetic.mul_pos_direct (by decide) targets.cost_positive

/-- The actual original derivative allocation is strictly positive. -/
theorem localBound_positive (targets : Targets original stage) : 0 < targets.localBound := by
  rewrite [targets.localBound_eq]
  exact Order.Field.div_pos_direct targets.budget_positive targets.denominator_positive

/-- The actual original endpoint allocation is strictly positive. -/
theorem endpoint_positive (targets : Targets original stage) : 0 < targets.endpoint := by
  rewrite [targets.endpoint_eq]
  exact targets.localBound_positive

/-- The retained local allocation is bounded by its original geometric request budget. -/
theorem localBound_le_budget (targets : Targets original stage) : targets.localBound ≤ targets.budget := by
  have costLower : (1 : Rational) ≤ targets.cost := by
    rewrite [targets.cost_eq]
    have combined := Order.Arithmetic.add_le_add_direct targets.countSquare_nonnegative
      (Order.Basic.le_refl (1 : Rational))
    rewrite [Field.zero_add] at combined
    exact combined
  have denominatorLower : (16 : Rational) ≤ targets.denominator := by
    rewrite [targets.denominator_eq]
    have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct costLower (by decide +kernel :
      (0 : Rational) ≤ 16)
    rewrite [Field.mul_one_direct] at scaled
    exact scaled
  have oneLower : (1 : Rational) ≤ targets.denominator :=
    (by decide +kernel : (1 : Rational) ≤ 16).trans denominatorLower
  have payment := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct oneLower targets.budget_positive.le
  rewrite [Field.mul_one_direct] at payment
  rewrite [targets.localBound_eq]
  exact (Order.Field.div_le_iff_pos targets.denominator_positive).mpr payment

/-- Every original local allocation obeys the literal unit-scale quarter-radius schedule. -/
theorem localBound_le_quarterRadius (targets : Targets original stage) :
    targets.localBound ≤ Basic.quarterRadius 1 stage := targets.localBound_le_budget.trans_eq targets.budget_eq

/-- A nonnegative fixed scalar times the original local allocation follows that same geometric schedule. -/
theorem mul_localBound_le_quarterRadius (targets : Targets original stage) (scale : Rational)
    (nonnegative : 0 ≤ scale) : scale * targets.localBound ≤ Basic.quarterRadius scale stage := by
  exact (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct targets.localBound_le_quarterRadius
    nonnegative).trans_eq (by
      rewrite [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow]
      ring1)

/-- Requests on the identical original finite path retain the same count-derived denominator at all stages. -/
theorem denominator_eq_of_path {firstStage lastStage : Nat}
    (first : Targets original firstStage) (last : Targets original lastStage) :
    first.denominator = last.denominator := by
  rewrite [first.denominator_eq, last.denominator_eq, first.cost_eq, last.cost_eq,
    first.countSquare_eq, last.countSquare_eq, first.count_eq, last.count_eq]
  rfl

/-- Local allocations on the identical original finite path decrease with the requested geometric stage. -/
theorem localBound_antitone {earlier later : Nat}
    (first : Targets original earlier) (last : Targets original later) (order : earlier ≤ later) :
    last.localBound ≤ first.localBound := by
  rewrite [last.localBound_eq, first.localBound_eq, last.budget_eq, first.budget_eq,
    ← first.denominator_eq_of_path last, Field.div_eq_mul_inv_direct, Field.div_eq_mul_inv_direct]
  exact Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Basic.quarterRadius_antitone (by decide +kernel : (0 : Rational) ≤ 1) order)
    (Order.Field.inv_pos_direct first.denominator_positive).le

/-- The computed allocations pay the actual original count-squared primitive error estimate. -/
theorem payment (targets : Targets original stage) :
    targets.countSquare * (4 * targets.localBound + 8 * targets.endpoint) ≤ targets.budget := by
  have countBound : targets.countSquare ≤ targets.cost := by
    rewrite [targets.cost_eq]
    exact le_add_of_nonneg_right (by decide)
  have localNonnegative := targets.localBound_positive.le
  have coefficient : 4 * targets.localBound + 8 * targets.endpoint ≤ 16 * targets.localBound := by
    rewrite [targets.endpoint_eq]
    calc
      _ = 12 * targets.localBound := by ring1
      _ ≤ 16 * targets.localBound :=
        Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide) localNonnegative
  have cancellation : targets.cost * (16 * targets.localBound) = targets.budget := by
    calc
      _ = targets.localBound * targets.denominator := by rw [targets.denominator_eq]; ring1
      _ = targets.budget := by
        rw [targets.localBound_eq]
        exact Field.div_mul_cancel_of_ne _ _ targets.denominator_positive.ne'
  exact (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct coefficient targets.countSquare_nonnegative).trans
    ((Order.Arithmetic.mul_le_mul_of_nonneg_right_direct countBound
      (Order.Arithmetic.mul_nonneg_direct (by decide) localNonnegative)).trans_eq cancellation)

/-- A retained displacement cost determines the original positive source-error request. -/
@[expose] def sourceTarget (targets : Targets original stage) (cost : Rational) : Rational :=
  min 1 (targets.localBound / (cost + 1))

/-- Every nonnegative original displacement cost has a positive computed source request. -/
theorem sourceTarget_positive (targets : Targets original stage) (cost : Rational) (nonnegative : 0 ≤ cost) :
    0 < targets.sourceTarget cost :=
  Order.Basic.lt_min (by decide)
    (Order.Field.div_pos_direct targets.localBound_positive
      (Order.Arithmetic.add_pos_of_nonneg_of_pos_direct nonnegative (by decide)))

/-- The same original displacement cost times its actual selected source target pays the local allocation. -/
theorem sourceTarget_payment (targets : Targets original stage) (cost : Rational) (nonnegative : 0 ≤ cost) :
    cost * targets.sourceTarget cost < targets.localBound :=
  Order.Field.mul_min_one_div_lt nonnegative targets.localBound_positive

/-- The actual original primitive-cell chain obeys the computed geometric whole-path request. -/
theorem integral_error_le (targets : Targets original stage)
    {endpoint : LiftedPoint sheets → Basic.Canonical} {cells : List CellModel}
    (chain : Cells endpoint targets.localBound targets.endpoint cells original) :
    Norm.Basic.normSq ((PathModel.mk cells).integralSample - (endpoint finish - endpoint start)) ≤
      Basic.quarterRadius 1 stage := by
  have bound := chain.integral_error_le
  have countEqual := LiftedPath.followedBy_length chain.follows
  rw [← targets.count_eq] at countEqual
  rw [countEqual] at bound
  have squareEqual : (targets.count : Rational) *
      ((targets.count : Rational) * (4 * targets.localBound + 8 * targets.endpoint)) =
        targets.countSquare * (4 * targets.localBound + 8 * targets.endpoint) := by
    rw [targets.countSquare_eq]
    ring1
  rw [squareEqual] at bound
  exact bound.trans (targets.payment.trans_eq targets.budget_eq)

end Targets

end Purelib.Integration.Path.Primitive.PrimitiveEdge.CellEndpoints

end
