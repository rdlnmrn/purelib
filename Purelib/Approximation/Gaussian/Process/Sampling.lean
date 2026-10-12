module
public import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Nat.Subtraction

/-!
# Finite sampling trajectories

Each retained sampled state is obtained by a positive geometric
refinement of the preceding state. Witness readbacks and possibility bounds
concern that exact trajectory and the process's retained observations.
-/

namespace Purelib.Approximation.Gaussian.Process.Sampling

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Data.Nat

/-- The scale-one quarter-power squared-error request at the displayed finite index.

The original unit-scale quarter radius supplies the squared-error request
for each displayed natural stage of the sampling trajectory. -/
@[expose] public def refinementTarget (index : Nat) : Fraction.Rational :=
  Geometric.Basic.quarterRadius 1 index

/-- Every finite sampling request is strictly positive.

Every stage uses the positive unit-scale quarter radius. The bound
justifies that same retained request in the process refinement constructor. -/
public theorem refinementTarget_pos (index : Nat) : 0 < refinementTarget index :=
  Geometric.Basic.quarterRadius_pos (by decide) index

/-- Every finite sampling request is at most one.

The nonnegative unit scale bounds all successive quarter radii.
The retained request at the displayed index therefore does not exceed one. -/
public theorem refinementTarget_le_one (index : Nat) : refinementTarget index ≤ 1 :=
  Geometric.Basic.quarterRadius_le_scale (by decide) index

/-- A nested path of finite process states. State zero is itself a genuine refinement, so every displayed state has the
same geometric accuracy form.

Stage zero refines the supplied start, and each successor refines exactly
the preceding selected state with its own positive quarter-radius request. -/
@[expose] public def stateAt (process : Process) (start : process.State) : Nat → process.State
  | 0 => process.refine start (refinementTarget 0) (refinementTarget_pos 0)
  | index + 1 =>
      process.refine (Purelib.Approximation.Gaussian.Process.Sampling.stateAt process start index)
        (refinementTarget (index + 1)) (refinementTarget_pos (index + 1))

/-- The first sampled state refines the original start at the index-zero request.

The original zero branch performs the index-zero refinement of the
supplied starting state with that request and its retained positivity evidence. -/
@[simp] public theorem stateAt_zero (process : Process) (start : process.State) :
    stateAt process start 0 =
      process.refine start (refinementTarget 0) (refinementTarget_pos 0) := rfl

/-- The next sampled state refines the preceding state at its own geometric request.

The original successor branch retains the preceding sampled state and
refines it using the next index-specific request and its positivity certificate. -/
@[simp] public theorem stateAt_succ (process : Process) (start : process.State)
    (index : Nat) :
    stateAt process start (index + 1) =
      process.refine (stateAt process start index)
        (refinementTarget (index + 1)) (refinementTarget_pos (index + 1)) := rfl

/-- Each sampled state's ball has squared radius below its indexed geometric request.

The process accuracy field bounds the radius of the exact state returned
by each original refinement, including the first refinement at stage zero. -/
public theorem stateAt_accurate (process : Process) (start : process.State)
    (index : Nat) :
    (process.ball (stateAt process start index)).radiusSq <
      refinementTarget index := by
  cases index with
  | zero => exact process.accurate start _ _
  | succ index => exact process.accurate (stateAt process start index) _ _

/-- Possibility at an index extended by a finite number of steps persists at the original index.

Each displayed successor applies the process persistence field to the
same preceding state. Induction retains every finite intervening refinement. -/
public theorem stateAt_possible_persists_add (process : Process)
    (start : process.State) (earlier : Nat) :
    ∀ (extra : Nat) {value : Basic.Canonical},
      process.Possible (stateAt process start (earlier + extra)) value →
        process.Possible (stateAt process start earlier) value
  | 0, _, possible => by
      simpa only [Nat.add_zero] using possible
  | extra + 1, value, possible => by
      have atPrevious :
          process.Possible (stateAt process start (earlier + extra)) value := by
        apply process.refine_persists
          (stateAt process start (earlier + extra))
          (refinementTarget (earlier + extra + 1))
          (refinementTarget_pos (earlier + extra + 1))
        simpa only [stateAt_succ,
          show earlier + (extra + 1) = earlier + extra + 1 by ring1] using possible
      exact stateAt_possible_persists_add process start earlier extra atPrevious

/-- Every reading possible at a later sampled state remains possible at an earlier sampled state.

The retained stage order gives the explicit natural difference between
indices. Persistence over that many original refinements gives the earlier possibility. -/
public theorem stateAt_possible_persists (process : Process) (start : process.State)
    {earlier later : Nat} (order : earlier ≤ later) {value : Basic.Canonical}
    (possible : process.Possible (stateAt process start later) value) :
    process.Possible (stateAt process start earlier) value := by
  have atExtended :
      process.Possible (stateAt process start (earlier + (later - earlier))) value := by
    rw [Subtraction.add_sub_of_le order]
    exact possible
  exact stateAt_possible_persists_add process start earlier (later - earlier) atExtended

/-- Read the process's retained rational witness at the indexed sampled state.

The process witness belongs to the exact state selected at this index.
The readback returns its original retained value without constructing another candidate. -/
@[expose] public def witnessAt (process : Process) (start : process.State) (index : Nat) :
    Basic.Canonical :=
  (process.witness (stateAt process start index)).val

/-- The sampled witness is possible at the same sampled state.

The possibility certificate is the property field of the original witness
returned at that same retained sampled state. -/
public theorem witnessAt_possible (process : Process) (start : process.State)
    (index : Nat) :
    process.Possible (stateAt process start index)
      (witnessAt process start index) :=
  (process.witness (stateAt process start index)).property

/-- A later sampled witness is possible at every earlier sampled state.

The original later witness is possible at its own retained sampled state.
Stage persistence transports that same possibility to the earlier selected state. -/
public theorem witnessAt_later_possible (process : Process) (start : process.State)
    {earlier later : Nat} (order : earlier ≤ later) :
    process.Possible (stateAt process start earlier)
      (witnessAt process start later) :=
  stateAt_possible_persists process start order
    (witnessAt_possible process start later)

/-- Every reading possible at a sampled state was possible at the original starting state.

Possibility first persists to the index-zero sampled state. Its original
refinement certificate then relates that state to the supplied starting state. -/
public theorem stateAt_possible_at_start (process : Process) (start : process.State)
    (index : Nat) {value : Basic.Canonical}
    (possible : process.Possible (stateAt process start index) value) :
    process.Possible start value := by
  have atZero : process.Possible (stateAt process start 0) value :=
    stateAt_possible_persists process start (Nat.zero_le index) possible
  exact process.refine_persists start (refinementTarget 0)
    (refinementTarget_pos 0) atZero

/-- Every sampled rational witness was possible at the original starting state.

The original witness is possible at its selected sampled state.
Persistence through the original trajectory relates it to the supplied start. -/
public theorem witnessAt_possible_start (process : Process) (start : process.State)
    (index : Nat) :
    process.Possible start (witnessAt process start index) :=
  stateAt_possible_at_start process start index
    (witnessAt_possible process start index)

/-- Two later finite witnesses are close because both are explicit candidates inside the earlier finite ball.

Both original witnesses are possible in the earlier state's retained ball.
The same ball radius and geometric request bound their displayed squared separation. -/
public theorem witnessAt_later_close (process : Process) (start : process.State)
    {earlier later : Nat} (order : earlier ≤ later) :
    Data.Gaussian.Norm.Basic.normSq (witnessAt process start later - witnessAt process start earlier) ≤
      Geometric.Basic.quarterRadius 4 earlier := by
  let state := stateAt process start earlier
  let center := (process.ball state).center
  let radius := (process.ball state).radiusSq
  have laterInside := process.possible_inside
    (witnessAt_later_possible process start order)
  have earlierInside := process.possible_inside
    (witnessAt_possible process start earlier)
  have centerEarlierInside :
      Data.Gaussian.Norm.Basic.normSq (center - witnessAt process start earlier) ≤ radius := by
    rw [Purelib.Data.Gaussian.Field.sub_eq_neg_sub, Norm.Basic.normSq_neg]
    exact earlierInside
  have radiusLeTarget : radius ≤ refinementTarget earlier :=
    (stateAt_accurate process start earlier).le
  calc
    Data.Gaussian.Norm.Basic.normSq (witnessAt process start later - witnessAt process start earlier) =
        Data.Gaussian.Norm.Basic.normSq ((witnessAt process start later - center) +
          (center - witnessAt process start earlier)) := by
      rw [Data.Gaussian.Field.later_sub_earlier]
    _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (witnessAt process start later - center) +
        Data.Gaussian.Norm.Basic.normSq (center - witnessAt process start earlier)) :=
      Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * (radius + radius) :=
      Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add laterInside centerEarlierInside) (by decide)
    _ = 4 * radius := by ring1
    _ ≤ 4 * refinementTarget earlier :=
      Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusLeTarget
        (by decide)
    _ = Geometric.Basic.quarterRadius 4 earlier := by
      rw [refinementTarget,
        Geometric.Basic.quarterRadius_eq_mul_pow,
        Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1

/-- Every sampled witness has squared norm at most twice one plus the process centre bound.

The witness lies inside the original selected ball. Its retained radius
is at most one, and the same centre satisfies the process centre-bound certificate. -/
public theorem witnessAt_bounded (process : Process) (start : process.State)
    (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (witnessAt process start index) ≤
      2 * (1 + process.centerBound) := by
  let state := stateAt process start index
  let center := (process.ball state).center
  let radius := (process.ball state).radiusSq
  have inside := process.possible_inside (witnessAt_possible process start index)
  have centerBound := process.center_bounded state
  have radiusLeOne : radius ≤ 1 :=
    (stateAt_accurate process start index).le.trans
      (refinementTarget_le_one index)
  have identity : witnessAt process start index =
      (witnessAt process start index - center) + center := by
    apply Basic.ext <;>
      simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im] <;> ring1
  rw [identity]
  calc
    Data.Gaussian.Norm.Basic.normSq ((witnessAt process start index - center) + center) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq (witnessAt process start index - center) + Data.Gaussian.Norm.Basic.normSq
          center) :=
      Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * (radius + process.centerBound) :=
      Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add inside centerBound) (by decide)
    _ ≤ 2 * (1 + process.centerBound) :=
      Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (calc
          radius + process.centerBound = process.centerBound + radius := by ring1
          _ ≤ process.centerBound + 1 :=
            add_le_add_right radiusLeOne process.centerBound
          _ = 1 + process.centerBound := by ring1)
        (by decide)

/-- The scale-four quarter-radius allowance is four times the indexed sampling request.

The unit and scale-four requests use the same quarter power at the given
index. The original multiplication laws identify their displayed scaling. -/
private theorem quarterRadius_four_eq_four_refinementTarget (index : Nat) :
    Geometric.Basic.quarterRadius 4 index =
      4 * refinementTarget index := by
  rw [refinementTarget,
    Geometric.Basic.quarterRadius_eq_mul_pow,
    Geometric.Basic.quarterRadius_eq_mul_pow]
  ring1

end Purelib.Approximation.Gaussian.Process.Sampling
