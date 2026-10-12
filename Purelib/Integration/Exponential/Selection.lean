module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Scale
import Purelib.Approximation.Rational.Geometric.Search
public import Purelib.Data.Nat.Schedule.PositiveStride
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Integration.Exponential.Geometry.Policy
public import Purelib.Integration.Partition.QuadraticWeight.Cache
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

open Purelib.Integration

/-!
# Retained finite exponential selection and observations

The original ordered geometry, positive-stride requests and polynomial depth
remain attached to their cached values and exact scalar readback certificates.
-/

public section
namespace Purelib.Integration.Exponential

open Purelib.Approximation.Rational
open Purelib.Data.Nat
open Purelib.Data.Rat
open Purelib.Integration.Exponential
open Purelib.Integration.Partition
open Purelib.Integration.Polynomial

set_option genInjectivity false in
/-- A retained partition geometry and depth whose amplified allowance is below the original stage target.

The selected depth is at least the original stage, and the cached geometry retains its exact partition and amplification
factor. -/
structure Selection (stage : Nat) where
  /-- The exact retained partition and cached quadratic amplification geometry. -/ geometry :
    QuadraticWeight.Cache.Geometry
  /-- The selected polynomial approximation depth. -/ depth : Nat
  /-- The selected depth is at least the original target stage. -/ stage_le_depth : stage ≤ depth
  /-- The retained geometry-amplified allowance is strictly below the original stage's quarter-radius target. -/
    allowance_small : geometry.factor * Geometric.Basic.quarterRadius 10 depth < Geometric.Basic.quarterRadius 10 stage

constructive_injectivity Selection

namespace Selection

/-- Search from the larger of the previous depth and scheduled index until the retained amplified allowance meets the
stage target.

The original schedule, geometry and target stage remain fixed, and the selected depth retains both its stage floor and
strict accuracy certificate. -/
@[expose] def select (schedule : Data.Nat.Schedule.PositiveStride) (geometry : QuadraticWeight.Cache.Geometry)
  (stage previousDepth : Nat) : Selection stage :=
  let start := max previousDepth (schedule.index stage)
  let depth := Geometric.Search.firstQuarterBelow (10 * geometry.factor) start (Geometric.Basic.quarterRadius 10 stage)
  { geometry := geometry
    depth := depth
    stage_le_depth := (schedule.index_ge stage).trans
      (((Order.max_eq_natMax previousDepth (schedule.index stage)).symm ▸
          Order.le_max_right previousDepth (schedule.index stage)).trans
        (Geometric.Search.firstQuarterBelow_ge (10 * geometry.factor) start (Geometric.Basic.quarterRadius 10 stage)))
    allowance_small := by
      rw [Geometric.Scale.amplified_quarter]
      exact Geometric.Search.firstQuarterBelow_accurate _
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) geometry.factor_nonnegative)
        start _ (Geometric.Basic.quarterRadius_pos (by decide) stage) }

end Selection

namespace Selection

/-- The selected depth is at least the exact supplied previous depth.

The original maximum retains the previous depth as a lower bound for the same target search. -/
theorem select_previous (schedule : Data.Nat.Schedule.PositiveStride) (geometry : QuadraticWeight.Cache.Geometry)
  (stage previousDepth : Nat) :
    previousDepth ≤ (Selection.select schedule geometry stage previousDepth).depth :=
  ((Order.max_eq_natMax previousDepth (schedule.index stage)).symm ▸
      Order.le_max_left previousDepth (schedule.index stage)).trans
    (Geometric.Search.firstQuarterBelow_ge _ _ _)

end Selection

namespace Selection

/-- The selected depth is at least the original schedule's requested stage index.

The original maximum retains the scheduled stage index as a lower bound for the same target search. -/
theorem select_requested (schedule : Data.Nat.Schedule.PositiveStride) (geometry : QuadraticWeight.Cache.Geometry)
  (stage previousDepth : Nat) :
    schedule.index stage ≤ (Selection.select schedule geometry stage previousDepth).depth :=
  ((Order.max_eq_natMax previousDepth (schedule.index stage)).symm ▸
      Order.le_max_right previousDepth (schedule.index stage)).trans
    (Geometric.Search.firstQuarterBelow_ge _ _ _)

end Selection

namespace Selection

/-- Build the retained geometry and depth sequence, carrying the previous selected depth into each next search.

Each stage retains its exact policy geometry and scheduled request. The previous cached depth becomes the next search
floor. -/
@[expose] def selection (policy : Exponential.Geometry.Policy) (schedule :
  Data.Nat.Schedule.PositiveStride) : (stage : Nat) → Selection stage
  | 0 => Selection.select schedule (QuadraticWeight.Cache.Geometry.canonical (Geometry.Policy.partitions policy 0)) 0 0
  | stage + 1 =>
      let previous := Purelib.Integration.Exponential.Selection.selection policy schedule stage
      Selection.select schedule (QuadraticWeight.Cache.Geometry.canonical (Geometry.Policy.partitions policy (stage +
        1))) (stage + 1) previous.depth

end Selection

namespace Selection

/-- Successive selected depths are nondecreasing.

The next selection keeps the previous stage depth as its search floor, preserving its original schedule and policy. -/
theorem selection_step (policy : Exponential.Geometry.Policy) (schedule :
  Data.Nat.Schedule.PositiveStride) (stage : Nat) :
    (Selection.selection policy schedule stage).depth ≤ (Selection.selection policy schedule (stage + 1)).depth :=
  Selection.select_previous schedule _ _ _

end Selection

namespace Selection

/-- Ordered original stages have ordered selected depths for the same policy and schedule.

The supplied stage order is decomposed into finitely many successor steps, each retaining the same policy and schedule.
-/
theorem selection_monotone (policy : Exponential.Geometry.Policy) (schedule :
  Data.Nat.Schedule.PositiveStride)
    {earlier later : Nat} (order : earlier ≤ later) :
    (Selection.selection policy schedule earlier).depth ≤ (Selection.selection policy schedule later).depth := by
  have decomposition : ∃ extra, later = earlier + extra :=
    ⟨later - earlier, (Subtraction.add_sub_of_le order).symm⟩
  obtain ⟨extra, rfl⟩ := decomposition
  clear order
  induction extra with
  | zero => exact Nat.le_refl _
  | succ extra inductionHypothesis =>
      exact inductionHypothesis.trans (Selection.selection_step policy schedule (earlier + extra))

end Selection

namespace Selection

/-- Every selected stage depth is at least its original scheduled index.

Each stage search starts at or above its original positive-stride schedule index. -/
theorem selection_requested (policy : Exponential.Geometry.Policy) (schedule :
  Data.Nat.Schedule.PositiveStride) (stage : Nat) :
    schedule.index stage ≤ (Selection.selection policy schedule stage).depth := by
  cases stage with
  | zero => exact Selection.select_requested schedule _ _ _
  | succ stage => exact Selection.select_requested schedule _ _ _

end Selection

end Purelib.Integration.Exponential
end
