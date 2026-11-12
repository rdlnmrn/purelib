module
import Purelib.Integration.Cell.Source.Continuous.Affine
import Purelib.Integration.Cell.Source.Continuous.Affine.Reverse
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! Rational affine endpoint transport, including reversed and zero intervals. -/

namespace TestPurelib.Integration.Cell.Source.Affine

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Integration
open Purelib.Integration.Partition
open Purelib.Integration.SourceFrontier.Continuous

/-- The original exact rational constant source. -/
private def source (_ : Fraction.Rational) : Fraction.Rational := 5

/-- A constant source value obeys every positive variation request. -/
private theorem constant_variation (value variation : Fraction.Rational) (positive : 0 < variation) :
    value - variation ≤ value ∧ value ≤ value + variation := by
  have negative := Arithmetic.neg_le_neg_direct positive.le
  rw [neg_zero] at negative
  have lower := Arithmetic.add_le_add_right_direct negative value
  have upper := Arithmetic.add_le_add_right_direct positive.le value
  have lowerEq : -variation + value = value - variation := by ring1
  have upperEq : variation + value = value + variation := by ring1
  rw [lowerEq, Fraction.Field.zero_add] at lower
  rw [Fraction.Field.zero_add, upperEq] at upper
  exact ⟨lower, upper⟩

/-- The actual affine pullback of the constant source has an effective modulus. -/
private def modulus (interval : Partition.Interval) : Rational.Uniform.Modulus (Affine.pullback source interval) where
  radius := fun _ => 1
  radius_pos := fun _ _ => by decide
  variation := by
    intro variation positive _ _ _ _ _ _
    exact constant_variation 5 variation positive

/-- A positively oriented rational endpoint pair outside the unit interval. -/
private def forward : Partition.Interval := ⟨2, 4⟩

/-- The same original endpoints in the reverse orientation. -/
private def backward : Partition.Interval := ⟨4, 2⟩

/-- A zero-length rational endpoint pair. -/
private def stationary : Partition.Interval := ⟨2, 2⟩

/-- A unit-length interval and its reverse for the nonconstant source. -/
private def forwardUnit : Partition.Interval := ⟨2, 3⟩
private def backwardUnit : Partition.Interval := ⟨3, 2⟩

/-- The original exact rational identity source. -/
private def identity (point : Fraction.Rational) : Fraction.Rational := point

/-- The forward affine identity pullback is the original shifted parameter. -/
private theorem forward_value (point : Fraction.Rational) :
    Affine.pullback identity forwardUnit point = 2 + point := by
  change (2 : Fraction.Rational) + (3 - 2) * point = 2 + point
  have difference : (3 : Fraction.Rational) - 2 = 1 := by decide
  rw [difference]
  ring1

/-- The forward nonconstant pullback has the exact unit-slope modulus. -/
private def forwardIdentityModulus : Rational.Uniform.Modulus (Affine.pullback identity forwardUnit) where
  radius := fun variation => variation
  radius_pos := fun _ positive => positive
  variation := by
    intro variation positive first second _ ordered _ small
    rw [forward_value first, forward_value second]
    have lower := (constant_variation first variation positive).1.trans ordered
    have upper := Arithmetic.sub_le_iff_le_add_direct.mp small.le
    have commute : variation + first = first + variation := by ring1
    rw [commute] at upper
    have shiftedLower := Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl 2) lower
    have shiftedUpper := Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl 2) upper
    have lowerEq : (2 : Fraction.Rational) + (first - variation) = (2 + first) - variation := by ring1
    have upperEq : (2 : Fraction.Rational) + (first + variation) = (2 + first) + variation := by ring1
    rw [lowerEq] at shiftedLower
    rw [upperEq] at shiftedUpper
    exact ⟨shiftedLower, shiftedUpper⟩

/-- The reversed pullback reuses the forward source's original effective modulus. -/
private def backwardIdentityModulus : Rational.Uniform.Modulus (Affine.pullback identity backwardUnit) :=
  Affine.reversedModulus identity forwardUnit forwardIdentityModulus

/-- The actual positively oriented finite integration process. -/
private def forwardProcess : BoundProcess := Affine.boundProcess source forward (modulus forward)

/-- The actual negatively oriented finite integration process. -/
private def backwardProcess : BoundProcess := Affine.boundProcess source backward (modulus backward)

/-- The actual forward process for the original nonconstant identity source. -/
private def forwardIdentityProcess : BoundProcess := Affine.boundProcess identity forwardUnit forwardIdentityModulus

/-- The actual reverse process for the original nonconstant identity source. -/
private def backwardIdentityProcess : BoundProcess := Affine.boundProcess identity backwardUnit backwardIdentityModulus

/-- The actual zero-length finite integration process. -/
private def stationaryProcess : BoundProcess := Affine.boundProcess source stationary (modulus stationary)

/-- A positive rational request for the transported processes. -/
private def request : AccuracyRequest := ⟨16, Fraction.Cast.Order.natCast_pos_direct (by decide : 0 < 16)⟩

/-- The actual saved positive-orientation state after its finite request. -/
private def forwardState : forwardProcess.State :=
  forwardProcess.request forwardProcess.initial request.tolerance request.positive

/-- The actual saved negative-orientation state after its finite request. -/
private def backwardState : backwardProcess.State :=
  backwardProcess.request backwardProcess.initial request.tolerance request.positive

/-- The actual finite forward request for the nonconstant source. -/
private def forwardIdentityState : forwardIdentityProcess.State :=
  forwardIdentityProcess.request forwardIdentityProcess.initial request.tolerance request.positive

/-- The actual finite reverse request for the nonconstant source. -/
private def backwardIdentityState : backwardIdentityProcess.State :=
  backwardIdentityProcess.request backwardIdentityProcess.initial request.tolerance request.positive

/-- Two independently built nonconstant source frontiers with distinct requests. -/
private def forwardResult := SourceFrontier.Continuous.build forwardIdentityModulus ⟨8, by decide⟩
private def backwardResult := SourceFrontier.Continuous.build backwardIdentityModulus ⟨4, by decide⟩

/-- The original nonuniform partition used to check reflected cut and cell order. -/
private def nonuniform := Partition.Unit.Normalized.ofRequest [1 / 4, 1 / 2]

example : Affine.pullback (fun point => point) forward 0 = 2 ∧
    Affine.pullback (fun point => point) forward 1 = 4 := by decide +kernel

example : backwardIdentityModulus.radius (1 / 2) = forwardIdentityModulus.radius (1 / 2) := rfl

example : Affine.pullback identity backwardUnit (1 / 4) =
    Affine.pullback identity forwardUnit (1 - 1 / 4) := Affine.pullback_reversed identity forwardUnit (1 / 4)

example : (Partition.Unit.Reverse.partition nonuniform).cuts = [1 / 2, 3 / 4] := by decide +kernel

example : (Partition.Unit.Reverse.partition nonuniform).intervals =
    [⟨0, 1 / 2⟩, ⟨1 / 2, 3 / 4⟩, ⟨3 / 4, 1⟩] := by decide +kernel

example : integralBound (SourceFrontier.Reverse.frontier forwardResult.frontier).cells =
    integralBound forwardResult.frontier.cells := SourceFrontier.Reverse.integralBound_eq forwardResult.frontier

example : Fraction.abs (forwardUnit.signedLength * forwardResult.answer +
      (-forwardUnit.signedLength) * backwardResult.answer) ≤
    Fraction.abs forwardUnit.signedLength * ((integralBound forwardResult.frontier.cells).width +
      (integralBound backwardResult.frontier.cells).width) :=
  Affine.oriented_answers_sum_le identity forwardUnit forwardResult.frontier backwardResult.frontier
    forwardResult.answer backwardResult.answer forwardResult.answer_contains backwardResult.answer_contains

example : Fraction.abs ((forwardIdentityProcess.bound forwardIdentityState).midpoint +
      (backwardIdentityProcess.bound backwardIdentityState).midpoint) ≤
    (forwardIdentityProcess.bound forwardIdentityState).width +
      (backwardIdentityProcess.bound backwardIdentityState).width :=
  Affine.saved_midpoints_sum_le identity forwardUnit (by decide) forwardIdentityModulus backwardIdentityModulus
    forwardIdentityState backwardIdentityState

example : (forwardProcess.bound forwardState).Contains 10 ∧ (forwardProcess.bound forwardState).midpoint = 10 :=
  by decide +kernel

example : (backwardProcess.bound backwardState).Contains (-10) ∧
    (backwardProcess.bound backwardState).midpoint = -10 := by decide +kernel

example : (forwardIdentityProcess.bound forwardIdentityState).Contains (5 / 2) ∧
    (backwardIdentityProcess.bound backwardIdentityState).Contains (-5 / 2) := by decide +kernel

example : (stationaryProcess.bound stationaryProcess.initial).width = 0 ∧
    (stationaryProcess.bound stationaryProcess.initial).Contains 0 := by decide +kernel

example : (forwardProcess.bound forwardState).width < request.tolerance :=
  forwardProcess.accurate forwardProcess.initial request.tolerance request.positive

end TestPurelib.Integration.Cell.Source.Affine
