module

import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Division
import Purelib.Tactic.QuotientFreeOmega

import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Natural schedules with positive stride

An offset and positive stride determine increasing source indices. Ceiling
division computes the first local stage whose source index meets a request;
the accompanying bounds certify that stage's reach and minimality.
-/

public section
namespace Purelib.Data.Nat.Schedule

open Purelib.Data.Nat

@[expose] public section
set_option genInjectivity false in
/-- A natural schedule with an offset and a strictly positive stride.

The stored extraStride represents stride minus one, so offset + (extraStride + 1) *
stage advances at every step without a separate positivity field. -/
structure PositiveStride where
  /-- The natural value at schedule index zero. -/ offset : Nat
  /-- The stride minus one, making the actual stride positive by construction. -/ extraStride : Nat
deriving DecidableEq

constructive_injectivity PositiveStride

end

namespace PositiveStride

/-- Compute the source index of a positive-stride schedule at a local stage.

The stored offset and extra stride determine the original natural affine expression at the supplied stage. -/
@[expose] def index (schedule : PositiveStride) (stage : Nat) : Nat :=
  schedule.offset + (schedule.extraStride + 1) * stage

/-- A positive-stride schedule preserves weak order of local stages.

Multiplication by the positive stride and addition of the fixed offset preserve the supplied natural stage order. -/
theorem monotone (schedule : PositiveStride) {earlier later : Nat} (order : earlier ≤ later) :
    schedule.index earlier ≤ schedule.index later :=
  Nat.add_le_add_left (Nat.mul_le_mul_left (schedule.extraStride + 1) order) schedule.offset

/-- A scheduled source index is at least its local stage.

The stride is at least one and the offset is nonnegative, so neither term can move the source index below its supplied
stage. -/
theorem index_ge (schedule : PositiveStride) (stage : Nat) : stage ≤ schedule.index stage := by
  unfold PositiveStride.index
  have stride : stage ≤ (schedule.extraStride + 1) * stage := by
    calc
      stage = 1 * stage := (Nat.one_mul stage).symm
      _ ≤ (schedule.extraStride + 1) * stage :=
        Nat.mul_le_mul_right stage (by omega)
  exact Nat.le_trans stride (Nat.le_add_left _ _)

/-- Compute the first schedule index whose value reaches a requested natural.

Ceiling division uses the positive stride. Truncated subtraction returns zero when
the initial offset already meets the request. -/
@[expose] def firstIndex (schedule : PositiveStride) (sourceIndex : Nat) : Nat :=
  (sourceIndex - schedule.offset + schedule.extraStride) / (schedule.extraStride + 1)

/-- The computed first local stage reaches the requested source index.

The same positive stride bounds the remainder in ceiling division. Its quotient therefore advances the source index far
enough for the supplied target. -/
theorem firstIndex_reaches (schedule : PositiveStride) (sourceIndex : Nat) :
    sourceIndex ≤ schedule.index (schedule.firstIndex sourceIndex) := by
  have division := Purelib.Data.Nat.Division.mod_add_div
    (sourceIndex - schedule.offset + schedule.extraStride) (schedule.extraStride + 1)
  have remainder := Nat.mod_lt
    (sourceIndex - schedule.offset + schedule.extraStride) (Nat.succ_pos schedule.extraStride)
  simp only [Nat.succ_eq_add_one] at remainder
  unfold PositiveStride.index PositiveStride.firstIndex
  omega

/-- The computed first index is at most an index exactly when its schedule value meets
the request.

This equivalence certifies minimality of the ceiling-division result using the
schedule's positive stride. -/
theorem firstIndex_le_iff (schedule : PositiveStride) (sourceIndex candidate : Nat) :
    schedule.firstIndex sourceIndex ≤ candidate ↔ sourceIndex ≤ schedule.index candidate := by
  constructor
  · intro order
    exact Nat.le_trans (schedule.firstIndex_reaches sourceIndex) (schedule.monotone order)
  · intro reaches
    unfold PositiveStride.firstIndex
    apply Purelib.Data.Nat.Division.div_le_of_lt_mul_succ
    rw [Nat.mul_succ]
    unfold PositiveStride.index at reaches
    omega

/-- Compute the least suitable schedule index at or beyond a retained cursor.

Take the maximum of the current cursor and the first index meeting the requested
natural value, preserving all earlier progress. -/
@[expose] def seek (schedule : PositiveStride) (current sourceIndex : Nat) : Nat :=
  max current (schedule.firstIndex sourceIndex)

/-- Seeking a source index never moves the current local cursor backwards.

The retained maximum contains the supplied current cursor as one of its original arguments. -/
theorem seek_ge (schedule : PositiveStride) (current sourceIndex : Nat) :
    current ≤ schedule.seek current sourceIndex := by
  rw [PositiveStride.seek, Order.max_eq_natMax]
  exact Order.le_max_left _ _

/-- The local stage returned by seek reaches the requested source index.

The maximum contains the least suitable index. Monotonicity of the same retained schedule transports its target-reaching
certificate. -/
theorem seek_reaches (schedule : PositiveStride) (current sourceIndex : Nat) :
    sourceIndex ≤ schedule.index (schedule.seek current sourceIndex) := by
  apply Nat.le_trans (schedule.firstIndex_reaches sourceIndex)
  apply schedule.monotone
  rw [PositiveStride.seek, Order.max_eq_natMax]
  exact Order.le_max_right _ _

/-- Characterize the least local stage that preserves the cursor and reaches the target.

A candidate is at least seek current sourceIndex exactly when it is at least current
and its scheduled source index reaches sourceIndex. -/
theorem seek_le_iff (schedule : PositiveStride) (current sourceIndex candidate : Nat) :
    schedule.seek current sourceIndex ≤ candidate ↔
      current ≤ candidate ∧ sourceIndex ≤ schedule.index candidate := by
  rw [PositiveStride.seek, Order.max_eq_natMax]
  constructor
  · intro retained
    exact ⟨Nat.le_trans (Order.le_max_left _ _) retained,
      (schedule.firstIndex_le_iff sourceIndex candidate).mp
        (Nat.le_trans (Order.le_max_right _ _) retained)⟩
  · intro retained
    exact Order.max_le retained.1
      ((schedule.firstIndex_le_iff sourceIndex candidate).mpr retained.2)

/-- The schedule with zero offset and unit stride.

Both stored parameters are zero, retaining exactly the source index equal to its supplied local stage. -/
@[expose] def identity : PositiveStride := ⟨0, 0⟩

/-- The identity schedule returns its supplied local stage unchanged.

The zero offset and unit stride reduce the original affine index expression to that same stage. -/
@[simp] theorem identity_index (stage : Nat) : PositiveStride.identity.index stage = stage := by
  change 0 + 1 * stage = stage
  rw [Nat.zero_add, Nat.one_mul]

end PositiveStride
end Purelib.Data.Nat.Schedule
end
