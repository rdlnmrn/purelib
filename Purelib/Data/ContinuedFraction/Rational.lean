module
import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Ring.IntCast
public import Purelib.Data.ContinuedFraction.Matrix
public import Purelib.Data.Int.Division
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Rational.Equivalence

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic

/-!
# Constructive one-dimensional baseline algorithms

Executable versions of the real continued-fraction and continued-logarithm
algorithms used for comparison in the CCL manuscript.  Both encoders recurse
on the displayed natural measure and decode in explicit constructive rational
coordinates.
-/

@[expose] public section

namespace Purelib.Data.ContinuedFraction.Rational

open Purelib.Data.Int in
/-- Compute rational Euclidean continued-fraction digits within the supplied finite fuel.

At each step retain the exact integer quotient and natural remainder; stop with a singleton when the remainder vanishes.
Zero fuel returns an empty list, while a denominator at most the fuel guarantees the reconstruction theorem. -/
def cfEncodeFuel : (fuel : Nat) → (numerator : Int) →
    (denominator : Nat) → 0 < denominator → List Int
  | 0, _, _, _ => []
  | fuel + 1, numerator, denominator, positive =>
      let quotient := numerator / (denominator : Int)
      let remainder := numerator % (denominator : Int)
      if remainderZero : remainder = 0 then
        [quotient]
      else
        quotient :: cfEncodeFuel fuel (denominator : Int)
          (Division.remNat numerator denominator)
          (Division.remNat_pos numerator positive remainderZero)

open Purelib.Data.ContinuedFraction in
/-- Encode a displayed rational using its positive natural denominator as sufficient Euclidean fuel. -/
def cfEncode (numerator : Int) (denominator : Nat)
    (positive : 0 < denominator) : List Int :=
  cfEncodeFuel denominator numerator denominator positive

section
open Purelib.Data.ContinuedFraction
open Purelib.Data.Rat
open Purelib.Geometry.Projective
/-- Decode a finite integer digit list by continued-fraction matrix action on the point at infinity. -/
def cfDecode : List Int → Line.Proj Fraction.Rational
  | [] => Line.Proj.omega
  | quotient :: digits =>
      Line.Matrix.act (Matrix.cf (quotient : Fraction.Rational) 1)
        (cfDecode digits)

/-- A singleton integer digit decodes as that integer over one. -/
@[simp] theorem cfDecode_singleton (quotient : Int) :
    cfDecode [quotient] =
      ⟨(quotient : Fraction.Rational), 1⟩ := by
  ext <;>
    simp only [cfDecode, Line.Matrix.act, Matrix.cf, Line.Proj.omega,
      mul_one, mul_zero, add_zero, -eq_self, -iff_self] <;> rfl

end

open Purelib.Algebra in
open Purelib.Data.ContinuedFraction in
open Purelib.Data.Int in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Fuel at least the positive denominator makes decoding the computed digits projectively equivalent to the original
displayed rational pair. -/
private theorem cfEncodeFuel_reconstruct : ∀ (fuel : Nat)
    (numerator : Int) (denominator : Nat) (positive : 0 < denominator),
    denominator ≤ fuel →
      (cfDecode (cfEncodeFuel fuel numerator denominator positive)).Equivalent
        ⟨(numerator : Fraction.Rational), (denominator : Fraction.Rational)⟩
  | 0, numerator, 0, positive, bounded =>
      (Nat.not_lt_zero 0 positive).elim
  | 0, numerator, denominator + 1, positive, bounded =>
      (Nat.not_succ_le_zero denominator bounded).elim
  | fuel + 1, numerator, denominator, positive, bounded => by
      rw [cfEncodeFuel]
      split
      · rename_i remainderZero
        rw [cfDecode_singleton]
        dsimp only [Line.Proj.Equivalent]
        have remainderVanishes : Division.remNat numerator denominator = 0 := by
          rw [Division.remNat, remainderZero]
          rfl
        have divisionIdentity : numerator / (denominator : Int) *
            (denominator : Int) = numerator := by
          have retained := Division.ediv_add_remNat numerator positive
          rw [remainderVanishes, Int.natCast_zero, Int.add_zero] at retained
          exact (Arithmetic.mul_comm _ _).trans retained
        have castIdentity := congrArg (fun value : Int =>
          (value : Fraction.Rational)) divisionIdentity
        simpa only [Ring.IntCast.intCast_mul, Int.cast_natCast, mul_one]
          using castIdentity
      · rename_i remainderNonzero
        let remainder := Division.remNat numerator denominator
        have remainderPositive : 0 < remainder :=
          Division.remNat_pos numerator positive remainderNonzero
        have remainderLess : remainder < denominator :=
          Division.remNat_lt numerator positive
        have remainderBound : remainder ≤ fuel :=
          Nat.lt_succ_iff.mp (remainderLess.trans_le bounded)
        have tail := cfEncodeFuel_reconstruct fuel
          (denominator : Int) remainder remainderPositive remainderBound
        have acted := Line.Matrix.act_respects_equivalent
          (Matrix.cf
            ((numerator / (denominator : Int) : Int) : Fraction.Rational) 1)
          tail
        have divisionIdentity := Division.ediv_add_remNat numerator positive
        have displayedIdentity :
            ((numerator / (denominator : Int) : Int) : Fraction.Rational) *
                (denominator : Fraction.Rational) + (remainder : Fraction.Rational) =
              (numerator : Fraction.Rational) := by
          have castIdentity := congrArg (fun value : Int =>
            (value : Fraction.Rational)) divisionIdentity
          simpa only [Ring.IntCast.add, Ring.IntCast.intCast_mul, Int.cast_natCast, mul_comm]
            using castIdentity
        have step :
            (Line.Matrix.act
              (Matrix.cf
                ((numerator / (denominator : Int) : Int) : Fraction.Rational) 1)
              (⟨(denominator : Fraction.Rational),
                (remainder : Fraction.Rational)⟩ : Line.Proj Fraction.Rational)).Equivalent
              ⟨(numerator : Fraction.Rational),
                (denominator : Fraction.Rational)⟩ := by
          dsimp only [Line.Proj.Equivalent, Line.Matrix.act, Matrix.cf]
          simp only [one_mul, zero_mul, add_zero]
          rw [displayedIdentity]
        exact Rational.Equivalence.equivalent_trans_of_mid_q acted step
          (by
            simpa only [Line.Matrix.act, Matrix.cf, one_mul, zero_mul,
              add_zero, Int.cast_natCast] using
              (ne_of_gt (Fraction.Cast.Order.natCast_pos_direct
                positive)))

open Purelib.Data.ContinuedFraction in
open Purelib.Data.Rat in
/-- The finite Euclidean continued-fraction encoding reconstructs the original displayed rational pair. -/
theorem cfEncode_reconstruct (numerator : Int) (denominator : Nat)
    (positive : 0 < denominator) :
    (cfDecode (cfEncode numerator denominator positive)).Equivalent
      ⟨(numerator : Fraction.Rational), (denominator : Fraction.Rational)⟩ := by
  unfold cfEncode
  exact cfEncodeFuel_reconstruct denominator numerator denominator positive
    (Nat.le_refl denominator)
end Purelib.Data.ContinuedFraction.Rational

end
