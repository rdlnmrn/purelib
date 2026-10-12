module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Fin
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Approximation.Budget.WeightedRowBudgets
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational.Geometric

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Data.Rat

open Purelib.Riemann.Periods

public section

/-!
# One paid common-stage sample bank

Heterogeneous primitive comparisons may return different sample stages.
Finite movement thresholds are selected before those requests; afterward
one common stage and its component values are cached for every weighted row.
-/

namespace Purelib.Approximation.Budget.SynchronizedSamples

open Purelib.Data

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
local notation "Vector" => Data.Vector
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Riemann.Periods.WeightedPeriods (Coordinate)
open Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- Compute the maximum of a finite vector of natural stages, with zero for the empty vector.

The original structural spine supplies every stage once in order; each cons retains the same natural maximum operation.
-/
@[expose] def maximumStage : {count : Nat} → Vector Nat count → Nat
  | _, .nil => 0
  | _, .cons first rest => max first (maximumStage rest)

/-- Every retained finite stage is at most the vector's computed maximum.

Structural lookup keeps its original head or predecessor entry; the same
maximum recursion bounds that entry at each retained vector length. -/
theorem stage_le_maximum {count : Nat} (stages : Vector Nat count) (index : Fin count) :
    stages index ≤ maximumStage stages := by
  induction stages with
  | nil => exact (Nat.not_lt_zero _ index.isLt).elim
  | @cons count first rest inductionHypothesis =>
      refine Fin.cases_induction ?_ ?_ index
      · change first ≤ max first (maximumStage rest)
        rw [Nat.Order.max_eq_natMax]
        exact Nat.Order.le_max_left _ _
      · intro tailIndex
        change rest tailIndex ≤ max first (maximumStage rest)
        rw [Nat.Order.max_eq_natMax]
        exact (inductionHypothesis tailIndex).trans (Nat.Order.le_max_right _ _)

set_option genInjectivity false in
/-- Cached per-source movement stages for a positive common target and retained stage floors.

Every stage is certified as the original source's geometric search result at its own floor. -/
structure StageRequest {count : Nat} (sources : Vector Gaussian.Geometric.GeometricApproximation count)
    (target : WeightedPeriods.Coordinate) (floors : Vector Nat count) where
  /-- The common movement target is strictly positive. -/ positive : 0 < target
  /-- The cached geometric movement stage of each original source. -/ stages : Vector Nat count
  /-- Each retained stage equals the geometric search result for that source and its exact floor. -/ stages_eq : ∀
    index, stages index = Search.firstQuarterBelow (sources index).errorScale (floors index) target

constructive_injectivity StageRequest

namespace StageRequest

variable {count : Nat} {sources : Vector Purelib.Approximation.Gaussian.Geometric.GeometricApproximation count} {target
  : Purelib.Riemann.Periods.WeightedPeriods.Coordinate} {floors : Vector Nat count}

/-- Compute and retain each source's movement stage at the common positive target and its original floor. -/
@[expose] def build (sources : Vector Gaussian.Geometric.GeometricApproximation count) (target :
  WeightedPeriods.Coordinate) (positive : 0 < target)
    (floors : Vector Nat count) : Approximation.Budget.SynchronizedSamples.StageRequest sources target floors :=
  ⟨positive, Data.Vector.Basic.vectorOfFn fun index => Search.firstQuarterBelow (sources index).errorScale (floors
    index) target,
    Data.Vector.Basic.vectorOfFn_apply _⟩

/-- Every computed movement stage meets its corresponding retained floor. -/
theorem floor_le (request : Approximation.Budget.SynchronizedSamples.StageRequest sources target floors) (index : Fin
  count) : floors index ≤ request.stages index := by
  rw [request.stages_eq]
  exact Search.firstQuarterBelow_ge _ _ _

/-- Any two later samples beyond the retained request stage differ by squared norm less than the common target. -/
theorem movement (request : Approximation.Budget.SynchronizedSamples.StageRequest sources target floors) (index : Fin
  count) {earlier later : Nat}
    (requested : request.stages index ≤ earlier) (order : earlier ≤ later) :
    Data.Gaussian.Norm.Basic.normSq ((sources index).sample later - (sources index).sample earlier) < target :=
      by
  have paid := Search.firstQuarterBelow_accurate (sources index).errorScale
    (sources index).errorScale_nonneg (floors index) target request.positive
  rw [← request.stages_eq index] at paid
  exact ((sources index).later_close order).trans_lt
    ((quarterRadius_antitone (sources index).errorScale_nonneg requested).trans_lt paid)

end StageRequest

set_option genInjectivity false in
/-- Cached values of the original sources at one shared finite stage.

The retained stage is exactly the maximum of the supplied floor and all individual stages; every value is certified as
the original source's sample at that stage. -/
structure Samples {count : Nat} (sources : Vector Gaussian.Geometric.GeometricApproximation count)
    (stages : Vector Nat count) (floor : Nat) where
  /-- The retained common sampling stage. -/ stage : Nat
  /-- The common stage is exactly the maximum of the supplied floor and the individual stages. -/ stage_eq : stage = max
    floor (maximumStage stages)
  /-- The cached Gaussian rational values of all original sources at the common stage. -/ values : Vector
    Data.Gaussian.Basic.Canonical count
  /-- Each cached value equals its original source's sample at the retained common stage. -/ values_eq : ∀ index, values
    index = (sources index).sample stage

constructive_injectivity Samples

namespace Samples

variable {count : Nat} {sources : Vector Purelib.Approximation.Gaussian.Geometric.GeometricApproximation count} {stages
  : Vector Nat count} {floor : Nat}

/-- Compute the shared maximum stage and cache each original source's sample there. -/
@[expose] def build (sources : Vector Gaussian.Geometric.GeometricApproximation count) (stages : Vector Nat count)
  (floor : Nat) :
    Approximation.Budget.SynchronizedSamples.Samples sources stages floor :=
  let stage := max floor (Approximation.Budget.SynchronizedSamples.maximumStage stages)
  ⟨stage, rfl, Data.Vector.Basic.vectorOfFn fun index => (sources index).sample stage,
    Data.Vector.Basic.vectorOfFn_apply _⟩

/-- The cached common stage is at least each supplied individual stage. -/
theorem later (sample : Approximation.Budget.SynchronizedSamples.Samples sources stages floor) (index : Fin count) :
  stages index ≤ sample.stage := by
  rw [sample.stage_eq]
  exact (Approximation.Budget.SynchronizedSamples.stage_le_maximum stages index).trans (by
      rw [Nat.Order.max_eq_natMax]
      exact Nat.Order.le_max_right _ _)

/-- The cached common stage meets the supplied shared floor. -/
theorem floor_le (sample : Approximation.Budget.SynchronizedSamples.Samples sources stages floor) : floor ≤ sample.stage
  := by
  rw [sample.stage_eq]
  rw [Nat.Order.max_eq_natMax]
  exact Nat.Order.le_max_left _ _

/-- The cached common-stage value differs from its supplied individual-stage sample by less than the paid movement
target. -/
theorem movement (sample : Approximation.Budget.SynchronizedSamples.Samples sources stages floor) {target :
  WeightedPeriods.Coordinate} {floors : Vector Nat count}
    (request : Approximation.Budget.SynchronizedSamples.StageRequest sources target floors) (requested : ∀ index,
      request.stages index ≤ stages index) (index : Fin count) :
    Data.Gaussian.Norm.Basic.normSq (sample.values index - (sources index).sample (stages index)) < target :=
      by
  rw [sample.values_eq]
  exact request.movement index (requested index) (sample.later index)

/-- Transfer an actual earlier-stage comparison to the cached common-stage value. The synchronization cost is added
explicitly before row weighting. -/
theorem comparison (sample : Approximation.Budget.SynchronizedSamples.Samples sources stages floor) {target :
  WeightedPeriods.Coordinate} {floors : Vector Nat count}
    (request : Approximation.Budget.SynchronizedSamples.StageRequest sources target floors) (requested : ∀ index,
      request.stages index ≤ stages index)
    (values : Fin count → Data.Gaussian.Basic.Canonical) (bounds : Fin count → WeightedPeriods.Coordinate)
    (bounded : ∀ index, Data.Gaussian.Norm.Basic.normSq (values index - (sources index).sample (stages index))
      ≤ bounds index) (index : Fin count) :
    Data.Gaussian.Norm.Basic.normSq (values index - sample.values index) < 2 * (bounds index + target) := by
  have estimate := Data.Gaussian.Norm.Bounds.normSq_sub_le_two
    (values index - (sources index).sample (stages index)) (sample.values index - (sources index).sample (stages index))
  have equal : (values index - (sources index).sample (stages index)) -
      (sample.values index - (sources index).sample (stages index)) = values index - sample.values index := by ring1
  rw [equal] at estimate
  have translated : bounds index + Data.Gaussian.Norm.Basic.normSq (sample.values index - (sources
    index).sample (stages index)) < bounds index + target := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct (sample.movement request requested index) (bounds
      index)
    simpa only [add_comm] using shifted
  have summed := (add_le_add (bounded index)
    (le_refl (Data.Gaussian.Norm.Basic.normSq (sample.values index - (sources index).sample (stages
      index))))).trans_lt translated
  exact estimate.trans_lt (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
    summed)

end Samples
end Purelib.Approximation.Budget.SynchronizedSamples

end
