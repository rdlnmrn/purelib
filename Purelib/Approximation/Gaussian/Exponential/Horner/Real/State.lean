module
public import Purelib.Approximation.Gaussian.Exponential.Horner.Real
import Purelib.Approximation.Bound.Process
import Purelib.Data.Nat.Order

/-!
# Original finite exponential samples in retained point states

On a rational unit point the public source is its original Gaussian Horner
process projected to the real coordinate. Every later finite Horner sample
is admitted by that same retained coordinate state.
-/

public section

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Real

open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- A rational unit query uses its original projected Gaussian process. -/
theorem source_eq_unit (point : Fraction.Rational) (unit : 0 ≤ point ∧ point ≤ 1) :
    source point = unitProcess point unit := by
  unfold source
  exact dif_pos unit

/-- Recover the exact retained Gaussian-coordinate state at a rational unit query. -/
@[expose] def originalState (point : Fraction.Rational) (unit : 0 ≤ point ∧ point ≤ 1)
    (state : (source point).State) : (unitProcess point unit).State := source_eq_unit point unit ▸ state

/-- The original process bound is exactly the bound of its retained Gaussian-coordinate state. -/
theorem originalState_bound (point : Fraction.Rational) (unit : 0 ≤ point ∧ point ≤ 1)
    (state : (source point).State) :
    (source point).bound state = (unitProcess point unit).bound (originalState point unit state) :=
  BoundProcess.bound_transport (source point) (unitProcess point unit) (source_eq_unit point unit) state

/-- Pair an actual real exponential point state with the imaginary coordinate of its original Gaussian process. -/
@[expose] def pairedState (point : Fraction.Rational) (unit : 0 ≤ point ∧ point ≤ 1)
    (state : (source point).State) : Process.Coordinate.Paired (approximation point unit).toProcess (0 : Nat) :=
  Process.Coordinate.Paired.fromReal (originalState point unit state)

/-- Pairing preserves the exact real interval of the original exponential point state. -/
theorem pairedState_real_bound (point : Fraction.Rational) (unit : 0 ≤ point ∧ point ≤ 1)
    (state : (source point).State) :
    (pairedState point unit state).real.interval = (source point).bound state :=
  (originalState_bound point unit state).symm

/-- Both paired coordinates admit the same actual later finite exponential sample. -/
theorem pairedState_sample_inside (point : Fraction.Rational) (unit : 0 ≤ point ∧ point ≤ 1)
    (state : (source point).State) (depth : Nat)
    (later : (show Nat from (pairedState point unit state).current) ≤ depth) :
    (pairedState point unit state).real.interval.Contains ((approximation point unit).sample depth).re ∧
      (pairedState point unit state).imaginary.interval.Contains ((approximation point unit).sample depth).im :=
  (pairedState point unit state).admits ((approximation point unit).sample depth) ⟨depth, later, rfl⟩

/-- The same later exponential sample obeys the paired coordinate half-width squared-norm bound. -/
theorem pairedState_sample_normSq_le (point : Fraction.Rational) (unit : 0 ≤ point ∧ point ≤ 1)
    (state : (source point).State) (depth : Nat)
    (later : (show Nat from (pairedState point unit state).current) ≤ depth) :
    Norm.Basic.normSq ((approximation point unit).sample depth - (pairedState point unit state).midpoint) ≤
      ((pairedState point unit state).real.interval.width * (1 / 2)) ^ 2 +
        ((pairedState point unit state).imaginary.interval.width * (1 / 2)) ^ 2 :=
  (pairedState point unit state).normSq_sub_midpoint_le ((approximation point unit).sample depth) ⟨depth, later, rfl⟩

/-- Independent saved exponential point states have a common later sample and an explicit squared-norm comparison. -/
theorem pairedState_midpoints_normSq_le (point : Fraction.Rational) (unit : 0 ≤ point ∧ point ≤ 1)
    (left right : (source point).State) :
    Norm.Basic.normSq ((pairedState point unit left).midpoint - (pairedState point unit right).midpoint) ≤
      ((pairedState point unit left).real.interval.width + (pairedState point unit right).real.interval.width) ^ 2 +
        ((pairedState point unit left).imaginary.interval.width +
          (pairedState point unit right).imaginary.interval.width) ^ 2 := by
  let first := pairedState point unit left
  let second := pairedState point unit right
  let depth := max (show Nat from first.current) (show Nat from second.current)
  let value := (approximation point unit).sample depth
  have firstPossible : (approximation point unit).toProcess.Possible first.current value :=
    ⟨depth, Purelib.Data.Nat.Order.le_max_left _ _, rfl⟩
  have secondPossible : (approximation point unit).toProcess.Possible second.current value :=
    ⟨depth, Purelib.Data.Nat.Order.le_max_right _ _, rfl⟩
  exact Process.Coordinate.Paired.midpoints_normSq_le first second value firstPossible secondPossible

/-- Every later displayed Horner sample belongs to the same original point-state interval. -/
theorem sample_inside (point : Fraction.Rational) (unit : 0 ≤ point ∧ point ≤ 1)
    (state : (source point).State) (depth : Nat)
    (later : (show Nat from (originalState point unit state).current) ≤ depth) :
    ((source point).bound state).Contains (finiteSource depth point) := by
  rw [originalState_bound]
  exact (originalState point unit state).admits ((approximation point unit).sample depth) ⟨depth, later, rfl⟩

end Purelib.Approximation.Gaussian.Exponential.Horner.Real

end
