module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Add
public import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Request.Addition
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

public section

/-!
# Constructive chart preparation for progressive CCL arithmetic

The local arithmetic controller needs two chart-side facts which are stronger
than mere convergence of a squared-error radius:

* a possible-value lower norm must be turned into apartness of the whole
  displayed rational ball before affine inversion; and
* a strict possible-value lower norm above one must be turned into a centre
  norm at least one before the redundant loop decision.

This module begins that bridge.  All witnesses are rational candidates in one
explicit finite state.  No completed value is selected.
-/

namespace Purelib.Approximation.Gaussian.Process.Translation

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Enclosure
open Purelib.Approximation.Gaussian.Request.Basic
open Purelib.Data.Rat

/-- Translate a stateful enclosure process by subtracting a fixed Gaussian rational.

The original state type is retained, possible readings keep their source witnesses, and refinement pays the additive
quarter-target budget. -/
@[expose] public def translate (process : Process) (shift : Data.Gaussian.Basic.Canonical) :
  Process where
  State := process.State
  ball state := (process.ball state).sub (Ball.point shift)
  Possible state value := ∃ sourceValue : Data.Gaussian.Basic.Canonical,
    process.Possible state sourceValue ∧ value = sourceValue - shift
  witness state := by
    rcases process.witness state with ⟨sourceValue, possible⟩
    exact ⟨sourceValue - shift, sourceValue, possible, rfl⟩
  possible_inside := by
    rintro state value ⟨sourceValue, possible, rfl⟩
    exact Enclosure.Ball.contains_sub
      (process.possible_inside possible) (Ball.contains_point shift)
  refine state target positive :=
    process.refine state (Name.additiveInputTarget
      target) (Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive)
  refine_persists := by
    rintro state target positive value ⟨sourceValue, possible, equal⟩
    exact ⟨sourceValue, process.refine_persists state _ _ possible, equal⟩
  accurate := by
    intro state target positive
    apply Name.add_radius_lt
    · exact process.accurate state _ _
    · exact Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive
  centerBound := 2 * (process.centerBound + Data.Gaussian.Norm.Basic.normSq shift)
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg process.centerBound_nonneg (Data.Gaussian.Norm.Basic.normSq_nonneg shift))
  center_bounded := by
    intro state
    change Data.Gaussian.Norm.Basic.normSq ((process.ball state).center - shift) ≤
      2 * (process.centerBound + Data.Gaussian.Norm.Basic.normSq shift)
    exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (process.center_bounded state) le_rfl) (by decide))
end Purelib.Approximation.Gaussian.Process.Translation

end
