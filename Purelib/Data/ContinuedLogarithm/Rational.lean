module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.ContinuedFraction.Matrix
public import Purelib.Data.Nat.BinaryNormalization
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Rational.Equivalence

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
public import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Algebra.NatCast
import Purelib.Data.Nat.Multiplication

/-!
# Continued logarithms of positive rational ratios

Finite continued-logarithm words retain the binary normalization exponents of
displayed natural numerator-denominator pairs. Decoding composes their exact
scaling and reciprocal projective matrices.
-/

public section

namespace Purelib.Data.ContinuedLogarithm.Rational

open Purelib.Data
open Purelib.Data.Nat
open Purelib.Data.Rat
open Purelib.Data.ContinuedFraction
open Purelib.Geometry.Projective
open Purelib.Algebra

/-- Compute a positive rational continued-logarithm word within the supplied finite fuel.

Retain the power-of-two normalization exponent. Terminal exact powers produce only true bits; other steps append false
and recur on normalized numerator over the positive residual difference. A numerator at most the fuel guarantees
reconstruction. -/
@[expose] def clEncodeFuel : (fuel : Nat) → (numerator denominator : Nat) →
    0 < denominator → denominator ≤ numerator → List Bool
  | 0, _, _, _, _ => []
  | fuel + 1, numerator, denominator, positive, ordered =>
      if equal : numerator = denominator then
        []
      else
        let scale := BinaryNormalization.clScale numerator denominator positive ordered
        let normalized := 2 ^ scale.exponent * denominator
        if terminal : normalized = numerator then
          List.replicate scale.exponent true
        else
          List.replicate scale.exponent true ++ false ::
            Purelib.Data.ContinuedLogarithm.Rational.clEncodeFuel fuel normalized (numerator - normalized)
              (by
                have normalizedLt : normalized < numerator :=
                  lt_of_le_of_ne scale.lower terminal
                omega0)
              (by
                have upper : numerator < 2 * normalized := by
                  calc
                    numerator <
                        2 ^ (scale.exponent + 1) * denominator :=
                      scale.upper
                    _ = 2 * normalized := by
                      dsimp only [normalized]
                      rw [Nat.pow_succ, Nat.mul_comm (2 ^ scale.exponent) 2,
                        Multiplication.mul_assoc]
                exact BinaryNormalization.difference_le_of_lt_two_mul upper)

/-- Encode a positive ordered natural ratio with its numerator as finite fuel.

The displayed lower bound permits continued-logarithm normalization, and the
input numerator bounds the residual recursion. -/
@[expose] def clEncode (numerator denominator : Nat) (positive : 0 < denominator)
    (ordered : denominator ≤ numerator) : List Bool :=
  ContinuedLogarithm.Rational.clEncodeFuel numerator numerator denominator positive ordered

/-- Decode a finite continued-logarithm word by exact projective matrix actions.

The empty word represents one. A true head doubles the tail value and a false head applies the continued-fraction
substitution with both coefficients one. -/
@[expose] def clDecode : List Bool → Line.Proj Fraction.Rational
  | [] => ⟨1, 1⟩
  | true :: bits =>
      Line.Matrix.act (Line.Matrix.scale (2 : Fraction.Rational)) (Purelib.Data.ContinuedLogarithm.Rational.clDecode
        bits)
  | false :: bits =>
      Line.Matrix.act (Matrix.cf (1 : Fraction.Rational) 1) (Purelib.Data.ContinuedLogarithm.Rational.clDecode bits)

/-- The empty continued-logarithm word decodes to the pair one over one. -/
@[simp] theorem clDecode_nil : ContinuedLogarithm.Rational.clDecode [] = ⟨1, 1⟩ := rfl

/-- Repeated true bits decode to the corresponding power of two over one.

Each retained true bit doubles the displayed numerator while preserving the
denominator one, with the same projective matrix action. -/
theorem clDecode_replicate_true (exponent : Nat) :
    ContinuedLogarithm.Rational.clDecode (List.replicate exponent true) =
      ⟨(2 : Fraction.Rational) ^ exponent, 1⟩ := by
  induction exponent with
  | zero => rfl
  | succ exponent inductionHypothesis =>
      rw [List.replicate_succ, ContinuedLogarithm.Rational.clDecode,
        inductionHypothesis]
      apply Line.Proj.ext
      · dsimp only [Line.Matrix.act, Line.Matrix.scale]
        rw [pow_succ, mul_one, add_zero]
        exact mul_comm _ _
      · dsimp only [Line.Matrix.act, Line.Matrix.scale]
        rw [mul_one, zero_mul, zero_add]

/-- Prepending repeated true bits scales the decoded tail by their binary power.

The ordered prefix acts on the retained projective tail by the scale
matrix, preserving the denominator coordinate. -/
theorem clDecode_replicate_true_append (exponent : Nat) (bits : List Bool) :
    ContinuedLogarithm.Rational.clDecode (List.replicate exponent true ++ bits) =
      Line.Matrix.act (Line.Matrix.scale ((2 : Fraction.Rational) ^ exponent))
        (ContinuedLogarithm.Rational.clDecode bits) := by
  induction exponent with
  | zero =>
      apply Line.Proj.ext <;>
        dsimp only [List.replicate, List.nil_append, pow_zero,
          Line.Matrix.act, Line.Matrix.scale] <;>
        ring1
  | succ exponent inductionHypothesis =>
      simp only [List.replicate_succ, List.cons_append, ContinuedLogarithm.Rational.clDecode,
        inductionHypothesis]
      apply Line.Proj.ext
      · simp only [Line.Matrix.act, Line.Matrix.scale, pow_succ,
          add_zero, zero_mul]
        ring1
      · simp only [Line.Matrix.act, Line.Matrix.scale, add_zero, zero_mul]
        ring1

/-- Sufficient numerator fuel reconstructs the displayed positive ordered ratio.

The finite residual recursion retains positive denominators and reduces its
original numerator bound. Decoding composes the same scaling and reciprocal
matrices to recover the input projective pair. -/
private theorem clEncodeFuel_reconstruct : ∀ (fuel numerator denominator : Nat)
    (positive : 0 < denominator) (ordered : denominator ≤ numerator),
    numerator ≤ fuel →
      (ContinuedLogarithm.Rational.clDecode
        (ContinuedLogarithm.Rational.clEncodeFuel fuel numerator denominator positive ordered)).Equivalent
        ⟨(numerator : Fraction.Rational), (denominator : Fraction.Rational)⟩
  | 0, 0, denominator, positive, ordered, bounded => by
      have denominatorZero : denominator = 0 :=
        Nat.eq_zero_of_le_zero ordered
      subst denominator
      exact (Nat.not_lt_zero 0 positive).elim
  | 0, numerator + 1, denominator, positive, ordered, bounded =>
      (Nat.not_succ_le_zero numerator bounded).elim
  | fuel + 1, numerator, denominator, positive, ordered, bounded => by
      rw [ContinuedLogarithm.Rational.clEncodeFuel]
      split
      · rename_i equal
        subst numerator
        dsimp only [ContinuedLogarithm.Rational.clDecode, Line.Proj.Equivalent]
        ring1
      · rename_i notEqual
        let scale := BinaryNormalization.clScale numerator denominator positive ordered
        let normalized := 2 ^ scale.exponent * denominator
        change
          (ContinuedLogarithm.Rational.clDecode
            (if terminal : normalized = numerator then
              List.replicate scale.exponent true
            else
              List.replicate scale.exponent true ++ false ::
                ContinuedLogarithm.Rational.clEncodeFuel fuel normalized
                  (numerator - normalized) _ _)).Equivalent
            ⟨(numerator : Fraction.Rational), (denominator : Fraction.Rational)⟩
        split
        · rename_i terminal
          rw [ContinuedLogarithm.Rational.clDecode_replicate_true]
          dsimp only [Line.Proj.Equivalent]
          have castTerminal := congrArg (fun value : Nat =>
            (value : Fraction.Rational)) terminal
          dsimp only [normalized] at castTerminal
          rw [NatCast.mul, NatCast.pow] at castTerminal
          simpa only [Nat.cast_ofNat, mul_one] using castTerminal
        · rename_i nonterminal
          have normalizedLe : normalized ≤ numerator := scale.lower
          have normalizedLt : normalized < numerator :=
            lt_of_le_of_ne normalizedLe nonterminal
          have newPositive : 0 < numerator - normalized := by
            omega0
          have upper : numerator < 2 * normalized := by
            calc
              numerator < 2 ^ (scale.exponent + 1) * denominator :=
                scale.upper
              _ = 2 * normalized := by
                dsimp only [normalized]
                rw [Nat.pow_succ, Nat.mul_comm (2 ^ scale.exponent) 2,
                  Multiplication.mul_assoc]
          have newOrdered : numerator - normalized ≤ normalized :=
            BinaryNormalization.difference_le_of_lt_two_mul upper
          have normalizedBound : normalized ≤ fuel :=
            Nat.lt_succ_iff.mp (normalizedLt.trans_le bounded)
          have tail := Purelib.Data.ContinuedLogarithm.Rational.clEncodeFuel_reconstruct fuel normalized
            (numerator - normalized) newPositive newOrdered normalizedBound
          have afterFalse := Line.Matrix.act_respects_equivalent
            (Matrix.cf (1 : Fraction.Rational) 1) tail
          have afterScale := Line.Matrix.act_respects_equivalent
            (Line.Matrix.scale ((2 : Fraction.Rational) ^ scale.exponent))
            afterFalse
          rw [ContinuedLogarithm.Rational.clDecode_replicate_true_append]
          have step :
              (Line.Matrix.act
                (Line.Matrix.scale ((2 : Fraction.Rational) ^ scale.exponent))
                (Line.Matrix.act (Matrix.cf (1 : Fraction.Rational) 1)
                  (⟨(normalized : Fraction.Rational),
                    ((numerator - normalized : Nat) : Fraction.Rational)⟩ :
                    Line.Proj Fraction.Rational))).Equivalent
                ⟨(numerator : Fraction.Rational),
                  (denominator : Fraction.Rational)⟩ := by
            dsimp only [Line.Proj.Equivalent, Line.Matrix.act,
              Line.Matrix.scale, Matrix.cf]
            rw [NatCast.sub normalizedLe]
            dsimp only [normalized]
            rw [NatCast.mul, NatCast.pow]
            ring1
          apply Purelib.Geometry.Projective.Rational.Equivalence.equivalent_trans_of_mid_q afterScale step
          simpa only [Line.Matrix.act, Line.Matrix.scale, Matrix.cf,
            one_mul, zero_mul, add_zero, zero_add] using
            (ne_of_gt (Fraction.Cast.Order.natCast_pos_direct
              (Nat.mul_pos (Nat.two_pow_pos scale.exponent) positive)))

/-- The finite continued-logarithm word reconstructs the displayed positive ratio.

Decoding the encoder output is projectively equivalent to the same natural
numerator and positive denominator, with no quotient-carrier substitution. -/
theorem clEncode_reconstruct (numerator denominator : Nat)
    (positive : 0 < denominator) (ordered : denominator ≤ numerator) :
    (ContinuedLogarithm.Rational.clDecode (ContinuedLogarithm.Rational.clEncode numerator denominator positive
      ordered)).Equivalent
      ⟨(numerator : Fraction.Rational), (denominator : Fraction.Rational)⟩ := by
  unfold ContinuedLogarithm.Rational.clEncode
  exact ContinuedLogarithm.Rational.clEncodeFuel_reconstruct numerator numerator denominator positive
    ordered (Nat.le_refl numerator)

end Purelib.Data.ContinuedLogarithm.Rational

end
