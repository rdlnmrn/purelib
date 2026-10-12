module
import Purelib.Data.Rat.Fraction
import Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Contraction.Basic
public import Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Return
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Floor
public import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Region.Gaussian.UnitSquare

import Purelib.Data.GaussianInt.Norm.Basic
public import Purelib.Data.GaussianInt.Constants
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.GaussianInt.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Executable constructive coordinate-floor CCF encoder

The encoder groups at most three ordinary coordinate-floor clauses into one
well-founded recursive call.  Its measure is the natural squared norm of the
displayed uncancelled Gaussian denominator.
-/

namespace Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Transition

open Purelib in
open Purelib.Data in
/-- Take the coordinatewise Gaussian-integer floor of the retained fraction readback. -/
def digit (fraction : GaussianInt.Fraction) :
  Data.GaussianInt :=
  GaussianInt.Floor.floor fraction.value

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.CoordinateFloor in
open Purelib.Data.Gaussian in
/-- Subtract the embedded selected floor digit from the fraction readback. -/
def residual (fraction : GaussianInt.Fraction) :
  Basic.Canonical :=
  fraction.value - GaussianInt.toGaussian (digit fraction)

open Purelib in
open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.CoordinateFloor in
/-- Compute the displayed integer numerator minus the selected digit times the retained denominator. -/
def remainder (fraction : GaussianInt.Fraction)
  : Data.GaussianInt :=
  fraction.numerator - digit fraction * fraction.denominator

section
open Purelib.Data
open Purelib.Data.ComplexContinuedFraction.CoordinateFloor
open Purelib.Geometry.Region in
/-- The coordinate-floor fraction residual lies in the half-open unit square. -/
theorem residual_sq (fraction :
  GaussianInt.Fraction) :
    Gaussian.UnitSquare.Sq (residual fraction) := by
  simpa only [residual, digit, GaussianInt.Floor.fract] using
    GaussianInt.Floor.fract_sq fraction.value

section
open Purelib.Data.Gaussian
/-- The embedded integer remainder equals the Gaussian residual times the embedded retained denominator. -/
theorem remainder_toGaussian (fraction :
  GaussianInt.Fraction) :
    GaussianInt.toGaussian (remainder fraction) =
      residual fraction * GaussianInt.toGaussian fraction.denominator := by
  rw [remainder, GaussianInt.toGaussian_sub, GaussianInt.toGaussian_mul]
  simp only [residual, digit]
  rw [← fraction.value_mul_denominator]
  apply Basic.ext <;>
    simp only [Basic.sub_re,
      Basic.sub_im,
      Basic.mul_re,
      Basic.mul_im] <;>
    ring1

/-- A nonzero displayed integer remainder gives a nonzero Gaussian residual. -/
theorem residual_ne_zero {fraction :
  GaussianInt.Fraction}
    (remainderNonzero : remainder fraction ≠ 0) :
    residual fraction ≠ 0 := by
  intro residualZero
  have identity := remainder_toGaussian fraction
  rw [residualZero, Basic.zero_mul] at identity
  exact remainderNonzero
    (GaussianInt.toGaussian_eq_zero.mp identity)

end

/-- Construct the next displayed fraction with gamma-scaled old denominator and the retained nonzero remainder.

The supplied remainder-nonzero witness belongs to the exact new denominator. The original numerator and denominator
representation are not normalized or replaced. -/
def next (fraction : GaussianInt.Fraction)
  (remainderNonzero : remainder fraction ≠ 0) :
    GaussianInt.Fraction :=
  ⟨GaussianInt.gammaInt * fraction.denominator, remainder fraction, remainderNonzero⟩

/-- The next numerator is integer gamma times the retained preceding denominator. -/
@[simp] theorem next_num (fraction :
  GaussianInt.Fraction)
    (remainderNonzero : remainder fraction ≠ 0) :
    (next fraction remainderNonzero).numerator = GaussianInt.gammaInt * fraction.denominator := rfl

/-- The next denominator is the original coordinate-floor integer remainder. -/
@[simp] theorem next_den (fraction :
  GaussianInt.Fraction)
    (remainderNonzero : remainder fraction ≠ 0) :
    (next fraction remainderNonzero).denominator = remainder fraction := rfl

open Purelib.Data.Gaussian in
/-- The next displayed fraction reads back as gamma times the reciprocal of the original residual. -/
theorem next_value (fraction :
  GaussianInt.Fraction)
    (remainderNonzero : remainder fraction ≠ 0) :
    (next fraction remainderNonzero).value =
      Basic.Canonical.gamma * (residual fraction)⁻¹ := by
  have remainderGaussianNonzero : GaussianInt.toGaussian (remainder fraction) ≠ 0 := by
    intro gaussianZero
    exact remainderNonzero
      (GaussianInt.toGaussian_eq_zero.mp gaussianZero)
  apply Field.mul_right_cancel_of_ne
    remainderGaussianNonzero
  calc
    (next fraction remainderNonzero).value * GaussianInt.toGaussian (remainder fraction) =
        GaussianInt.toGaussian (GaussianInt.gammaInt * fraction.denominator) :=
      (next fraction remainderNonzero).value_mul_denominator
    _ = Basic.Canonical.gamma * GaussianInt.toGaussian fraction.denominator := by
      rw [GaussianInt.toGaussian_mul, GaussianInt.toGaussian_gammaInt]
    _ = (Basic.Canonical.gamma * (residual fraction)⁻¹) *
          GaussianInt.toGaussian (remainder fraction) := by
      rw [remainder_toGaussian,
        Basic.mul_assoc,
        ← Basic.mul_assoc
          (residual fraction)⁻¹,
        Field.inv_eq,
        Field.inv_mul _
          (residual_ne_zero remainderNonzero),
        Basic.one_mul]

/-- The next fraction residual is the coordinate-floor return of the original residual. -/
theorem residual_next (fraction :
  GaussianInt.Fraction)
    (remainderNonzero : remainder fraction ≠ 0) :
    residual (next fraction remainderNonzero) =
      Return.step (residual fraction) := by
  rw [residual, digit, next_value]
  rfl

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- The next denominator norm equals the original denominator norm scaled by residual squared norm. -/
theorem next_den_norm (fraction :
  GaussianInt.Fraction)
    (remainderNonzero : remainder fraction ≠ 0) :
    (GaussianInt.normNat (next fraction remainderNonzero).denominator : Fraction.Rational) =
      Data.Gaussian.Norm.Basic.normSq (residual fraction) * (GaussianInt.normNat fraction.denominator :
        Fraction.Rational) := by
  rw [next_den, ← GaussianInt.normSq_toGaussian, remainder_toGaussian, Norm.Basic.normSq_mul,
    GaussianInt.normSq_toGaussian]

/-- Three nonterminal coordinate-floor transitions strictly reduce the retained natural denominator norm.

Each nonzero-remainder witness selects the exact next displayed fraction. The three-step Gaussian contraction is
transported through the original remainder and denominator norm identities. -/
theorem three_den_descent (fraction :
  GaussianInt.Fraction)
    (firstNonzero : remainder fraction ≠ 0)
    (secondNonzero : remainder (next fraction firstNonzero) ≠ 0)
    (thirdNonzero :
      remainder (next (next fraction firstNonzero) secondNonzero) ≠ 0) :
    GaussianInt.normNat
        (next (next (next fraction firstNonzero) secondNonzero)
          thirdNonzero).denominator <
      GaussianInt.normNat fraction.denominator := by
  let first := next fraction firstNonzero
  let second := next first secondNonzero
  let third := next second thirdNonzero
  let u := residual fraction
  have uNonzero : u ≠ 0 := residual_ne_zero firstNonzero
  have firstResidual :
      residual first = Return.step u := by
    dsimp only [first, u]
    exact residual_next fraction firstNonzero
  have secondResidualNonzero :
      Return.step u ≠ 0 := by
    rw [← firstResidual]
    exact residual_ne_zero secondNonzero
  have secondResidual :
      residual second = Return.step
        (Return.step u) := by
    rw [residual_next first secondNonzero, firstResidual]
  have contraction :=
    Contraction.Basic.three_step_contraction
      u uNonzero (residual_sq fraction) secondResidualNonzero
  have firstNorm := next_den_norm fraction firstNonzero
  have secondNorm := next_den_norm first secondNonzero
  have thirdNorm := next_den_norm second thirdNonzero
  have normIdentity : (GaussianInt.normNat third.denominator : Fraction.Rational) =
      Data.Gaussian.Norm.Basic.normSq (u * Return.step u *
        Return.step
          (Return.step u)) *
        (GaussianInt.normNat fraction.denominator : Fraction.Rational) := by
    calc
      (GaussianInt.normNat third.denominator : Fraction.Rational) =
          Data.Gaussian.Norm.Basic.normSq (residual second) * (GaussianInt.normNat second.denominator :
            Fraction.Rational) :=
        thirdNorm
      _ = Data.Gaussian.Norm.Basic.normSq (residual second) *
          (Data.Gaussian.Norm.Basic.normSq (residual first) * (GaussianInt.normNat first.denominator :
            Fraction.Rational)) := by
        rw [secondNorm]
      _ = Data.Gaussian.Norm.Basic.normSq (residual second) *
          (Data.Gaussian.Norm.Basic.normSq (residual first) *
            (Data.Gaussian.Norm.Basic.normSq u * (GaussianInt.normNat fraction.denominator : Fraction.Rational))) := by
        rw [firstNorm]
      _ = Data.Gaussian.Norm.Basic.normSq (u * residual first * residual second) *
          (GaussianInt.normNat fraction.denominator : Fraction.Rational) := by
        rw [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
        ring1
      _ = Data.Gaussian.Norm.Basic.normSq (u * Return.step u *
          Return.step
            (Return.step u)) *
          (GaussianInt.normNat fraction.denominator : Fraction.Rational) := by
        rw [firstResidual, secondResidual]
  have denominatorPositive :
      (0 : Fraction.Rational) < (GaussianInt.normNat fraction.denominator : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct
      (GaussianInt.normNat_pos fraction.denominatorNonzero)
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
    contraction denominatorPositive
  have castDescent : (GaussianInt.normNat third.denominator : Fraction.Rational) <
      (GaussianInt.normNat fraction.denominator : Fraction.Rational) := by
    rw [normIdentity]
    simpa only [Fraction.Field.one_mul] using scaled
  exact (Fraction.Cast.Order.natCast_lt_iff_direct).1 castDescent
end

end Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Transition

end
