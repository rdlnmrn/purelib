module
public import Purelib.Approximation.Gaussian.Process.Coordinate
public import Purelib.Approximation.Gaussian.Exponential.Horner.Sequence
public import Purelib.Approximation.Gaussian.Sequence.Process
public import Purelib.Approximation.Rational.Uniform.Numerical
public import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Gaussian.RationalEmbedding.Bounds
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-!
# Finite real-coordinate exponential observations

Every rational unit input retains the original Gaussian exponential Horner
process and projects its real-coordinate bounds. Its uniform variation law
compares two actual finite states using one common finite sample depth.
-/

public section

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Real

open Purelib.Data.Gaussian
open Purelib.Data.Nat
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Approximation.Rational

/-- A rational unit input embeds into the original Gaussian unit disk. -/
theorem unit_input (point : Fraction.Rational) (unit : 0 ≤ point ∧ point ≤ 1) :
    Norm.Basic.normSq (RationalEmbedding.realPoint point) ≤ 1 := by
  rw [Norm.Basic.normSq_eq_canonical]
  exact RationalEmbedding.Bounds.unit_parameter unit.1 unit.2

/-- The original Gaussian exponential approximation at a rational unit point. -/
@[expose] def approximation (point : Fraction.Rational) (unit : 0 ≤ point ∧ point ≤ 1) :
    Gaussian.Sequence.ApproximationData :=
  Sequence.approximation (RationalEmbedding.realPoint point) (unit_input point unit)

/-- The actual real-coordinate process of the original Gaussian finite exponential approximation. -/
@[expose] def unitProcess (point : Fraction.Rational) (unit : 0 ≤ point ∧ point ≤ 1) : BoundProcess :=
  Process.Coordinate.real (approximation point unit).toProcess (0 : Nat)

/-- Exponential point observations on the rational unit interval, with an exact zero process elsewhere. -/
@[expose] def source (point : Fraction.Rational) : BoundProcess :=
  if unit : 0 ≤ point ∧ point ≤ 1 then unitProcess point unit else BoundProcess.exact 0

/-- The original exponential point process has executable finite-state equality. -/
instance (point : Fraction.Rational) : DecidableEq (source point).State := by
  unfold source
  by_cases unit : 0 ≤ point ∧ point ≤ 1
  · rw [dif_pos unit]
    change DecidableEq (Process.Coordinate.State (approximation point unit).toProcess (0 : Nat) Basic.Canonical.re)
    infer_instance
  · rw [dif_neg unit]
    change DecidableEq Unit
    infer_instance

/-- The original finite exponential samples have four-Lipschitz real coordinates on the rational unit interval. -/
theorem sample_variation (first second : Fraction.Rational)
    (firstUnit : 0 ≤ first ∧ first ≤ 1) (secondUnit : 0 ≤ second ∧ second ≤ 1)
    (ordered : first ≤ second) (depth : Nat) :
    let firstReading := (Sample.sample (RationalEmbedding.realPoint first) depth).re
    let secondReading := (Sample.sample (RationalEmbedding.realPoint second) depth).re
    firstReading - secondReading ≤ 4 * (second - first) ∧
      secondReading - firstReading ≤ 4 * (second - first) := by
  let firstValue := Sample.sample (RationalEmbedding.realPoint first) depth
  let secondValue := Sample.sample (RationalEmbedding.realPoint second) depth
  have squared := (Norm.Coordinates.re_sub_sq_le_basic_normSq firstValue secondValue).trans
    (Sample.sample_input_close _ _ (unit_input first firstUnit) (unit_input second secondUnit) depth)
  rw [RationalEmbedding.realPoint_sub, RationalEmbedding.normSq_realPoint] at squared
  have squareBound : (firstValue.re - secondValue.re) ^ 2 ≤ (4 * (second - first)) ^ 2 := by
    calc
      (firstValue.re - secondValue.re) ^ 2 ≤ 16 * (first - second) ^ 2 := squared
      _ = (4 * (second - first)) ^ 2 := by ring1
  have nonnegative : 0 ≤ 4 * (second - first) :=
    Arithmetic.mul_nonneg_direct (by decide)
      (Arithmetic.sub_nonneg_direct ordered)
  have forward := Arithmetic.le_of_sq_le_sq_direct nonnegative squareBound
  have reverseSquare : (secondValue.re - firstValue.re) ^ 2 ≤ (4 * (second - first)) ^ 2 := by
    have identity : (secondValue.re - firstValue.re) ^ 2 = (firstValue.re - secondValue.re) ^ 2 := by ring1
    rw [identity]
    exact squareBound
  exact ⟨forward, Arithmetic.le_of_sq_le_sq_direct nonnegative reverseSquare⟩

/-- Read the real coordinate of one original finite exponential Horner sample. -/
@[expose] def finiteSource (depth : Nat) (point : Fraction.Rational) : Fraction.Rational :=
  (Sample.sample (RationalEmbedding.realPoint point) depth).re

/-- The original fixed-depth Horner readings have an effective rational unit-interval modulus. -/
@[expose] def finiteModulus (depth : Nat) : Uniform.Modulus (finiteSource depth) where
  radius := fun variation => variation / 4
  radius_pos := fun _ positive => Bounds.Quarter.quarter_pos positive
  variation := by
    intro variation _ first second lower ordered upper small
    have firstUnit : 0 ≤ first ∧ first ≤ 1 := ⟨lower, ordered.trans upper⟩
    have secondUnit : 0 ≤ second ∧ second ≤ 1 := ⟨lower.trans ordered, upper⟩
    have samples := sample_variation first second firstUnit secondUnit ordered depth
    have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct small.le
      (by decide : (0 : Fraction.Rational) ≤ 4)
    have budget : 4 * (second - first) ≤ variation := by
      calc
        _ ≤ 4 * (variation / 4) := paid
        _ = (variation / 4) * 4 := by ring1
        _ = variation := Fraction.Field.div_mul_cancel_of_ne variation 4 (by decide)
    have firstDifference := samples.1.trans budget
    have secondDifference := samples.2.trans budget
    have firstAdded := Arithmetic.sub_le_iff_le_add_direct.mp firstDifference
    have secondAdded := Arithmetic.sub_le_iff_le_add_direct.mp secondDifference
    change finiteSource depth first ≤ variation + finiteSource depth second at firstAdded
    change finiteSource depth second ≤ variation + finiteSource depth first at secondAdded
    have firstCommute : variation + finiteSource depth second = finiteSource depth second + variation := by ring1
    have secondCommute : variation + finiteSource depth first = finiteSource depth first + variation := by ring1
    rw [firstCommute] at firstAdded
    rw [secondCommute] at secondAdded
    exact ⟨Arithmetic.sub_le_iff_le_add_direct.mpr firstAdded, secondAdded⟩

/-- The original exponential point processes have effective uniform rational variation.

At the maximum of the two retained process indices, each original interval
admits its own finite Horner sample. Their same-depth sensitivity pays the
requested variation without selecting an exact or completed exponential. -/
@[expose] def modulus : Uniform.Numerical source where
  radius := fun variation => variation / 4
  radius_pos := fun _ positive => Bounds.Quarter.quarter_pos positive
  variation := by
    intro variation positive first second lower ordered upper small firstState secondState
    have firstUnit : 0 ≤ first ∧ first ≤ 1 := ⟨lower, ordered.trans upper⟩
    have secondUnit : 0 ≤ second ∧ second ≤ 1 := ⟨lower.trans ordered, upper⟩
    have firstEq : source first = unitProcess first firstUnit := by
      rw [source, dif_pos firstUnit]
    have secondEq : source second = unitProcess second secondUnit := by
      rw [source, dif_pos secondUnit]
    generalize firstOwnerEq : source first = firstOwner at firstState ⊢
    generalize secondOwnerEq : source second = secondOwner at secondState ⊢
    have firstOwnerIdentity : firstOwner = unitProcess first firstUnit := firstOwnerEq.symm.trans firstEq
    have secondOwnerIdentity : secondOwner = unitProcess second secondUnit := secondOwnerEq.symm.trans secondEq
    clear firstOwnerEq secondOwnerEq
    subst firstOwner
    subst secondOwner
    let depth : Nat := Nat.max (show Nat from firstState.current) (show Nat from secondState.current)
    let firstReading := (Sample.sample (RationalEmbedding.realPoint first) depth).re
    let secondReading := (Sample.sample (RationalEmbedding.realPoint second) depth).re
    have firstInside : firstState.interval.Contains firstReading :=
      firstState.admits ((approximation first firstUnit).sample depth)
        ⟨depth, Order.le_max_left _ _, rfl⟩
    have secondInside : secondState.interval.Contains secondReading :=
      secondState.admits ((approximation second secondUnit).sample depth)
        ⟨depth, Order.le_max_right _ _, rfl⟩
    have samples := sample_variation first second firstUnit secondUnit ordered depth
    have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct small.le
      (by decide : (0 : Fraction.Rational) ≤ 4)
    have budget : 4 * (second - first) ≤ variation := by
      calc
        4 * (second - first) ≤ 4 * (variation / 4) := paid
        _ = (variation / 4) * 4 := by ring1
        _ = variation := Fraction.Field.div_mul_cancel_of_ne variation 4 (by decide)
    have forward := samples.1.trans budget
    have reverse := samples.2.trans budget
    have firstLe := Arithmetic.sub_le_iff_le_add_direct.mp forward
    have secondLe := Arithmetic.sub_le_iff_le_add_direct.mp reverse
    have firstCommute : variation + secondReading = secondReading + variation := by ring1
    have secondCommute : variation + firstReading = firstReading + variation := by ring1
    rw [firstCommute] at firstLe
    rw [secondCommute] at secondLe
    have translated := Arithmetic.sub_le_sub_right_direct firstInside.1 variation
    have firstMinus : firstReading - variation ≤ secondReading := by
      exact Arithmetic.sub_le_iff_le_add_direct.mpr firstLe
    have upperBound := Arithmetic.add_le_add_right_direct firstInside.2 variation
    exact ⟨translated.trans (firstMinus.trans secondInside.2), secondInside.1.trans (secondLe.trans upperBound)⟩

end Purelib.Approximation.Gaussian.Exponential.Horner.Real

end
