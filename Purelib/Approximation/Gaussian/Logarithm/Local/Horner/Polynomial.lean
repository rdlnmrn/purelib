module
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Basic
public import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
import Purelib.Approximation.Rat.Logarithm.Horner.Basic
import Purelib.Approximation.Rat.Logarithm.Horner.Coefficient
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.RationalEmbedding
public import Purelib.Data.Gaussian.Scale
public import Purelib.Data.Nat.Odd
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

section
public section

/-! Approximation Gaussian Logarithm Local Horner Polynomial and its finite structural certificates. -/

namespace Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Polynomial

open Purelib
open Purelib.Algebra.FiniteSum
open Purelib.Approximation.Gaussian.Logarithm.Local
open Purelib.Approximation.Gaussian.Logarithm.Local.Horner
open Purelib.Approximation.Rat.Logarithm.Horner
open Purelib.Approximation.Rat.Logarithm.Horner.Basic
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.RationalEmbedding
open Purelib.Data.Nat
open Purelib.Data.Rat

/-- The final monomial contributed by a finite complex-log Horner tail. -/
@[expose] public def logHornerTerm (w : Purelib.Data.Gaussian.Basic.Canonical) : Nat → Nat →
  Purelib.Data.Gaussian.Basic.Canonical
  | _, 0 => 1
  | index, degree + 1 =>
      Purelib.Data.Gaussian.RationalEmbedding.ComplexLog.scalar
          (Purelib.Approximation.Rat.Logarithm.Horner.Basic.ComplexLog.coefficient index) *
        w * Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm w (index + 1) degree

/-- The degree-zero logarithm Horner term is one. -/
@[simp] theorem logHornerTerm_zero (w : Data.Gaussian.Basic.Canonical) (index : Nat) :
    Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm w index 0 = 1 := rfl

/-- The next logarithm Horner term multiplies the recursive tail by its argument and odd-index coefficient. -/
@[simp] theorem logHornerTerm_succ (w : Data.Gaussian.Basic.Canonical) (index degree : Nat) :
    Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm w index (degree + 1) =
      ComplexLog.scalar
          (ComplexLog.coefficient index) *
        w * Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm w (index + 1) degree := rfl

/-- A logarithm Horner term at a positive index is the corresponding argument power scaled by the ratio of its endpoint
odd indices. -/
theorem logHornerTerm_eq_scaled_power (w : Data.Gaussian.Basic.Canonical) :
    ∀ (degree index : Nat), 1 ≤ index →
      Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm w index degree =
        Scale.scale
          ((Odd.priorOdd index : Fraction.Rational) /
            (Odd.priorOdd (index + degree) : Fraction.Rational))
          (w ^ degree)
  | 0, index, positive => by
      rw [Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm_zero, pow_zero]
      have same : Odd.priorOdd (index + 0) = Odd.priorOdd index := by
        rw [Nat.add_zero]
      rw [same]
      have denominatorNonzero : (Odd.priorOdd index : Fraction.Rational) ≠ 0 :=
        (Fraction.Cast.Order.natCast_pos_direct
          (Odd.priorOdd_pos positive)).ne'
      have quotientOne :
          (Odd.priorOdd index : Fraction.Rational) / (Odd.priorOdd index : Fraction.Rational) = 1 :=
        (Fraction.Field.div_eq_div_of_cross
          (Odd.priorOdd index : Fraction.Rational) (Odd.priorOdd index : Fraction.Rational) 1 1
          denominatorNonzero (by decide) (by
            rw [Fraction.Field.one_mul,
              Fraction.Field.mul_one_direct])).trans (by decide)
      rw [quotientOne]
      apply Data.Gaussian.Basic.ext <;>
        simp only [Scale.scale_re,
          Scale.scale_im, Basic.one_re, Basic.one_im] <;> ring1
  | degree + 1, index, positive => by
      rw [Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm_succ,
        Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm_eq_scaled_power w degree (index +
          1) (by omega),
        Scale.scalar_mul_eq_scale, Scale.scale_mul_scale, pow_succ]
      have coefficientIdentity := Coefficient.logCoefficient_telescope positive degree
      rw [coefficientIdentity]
      apply Data.Gaussian.Basic.ext <;>
        simp only [Scale.scale_re,
          Scale.scale_im, Basic.mul_re, Basic.mul_im] <;> ring1

/-- Increasing the finite local-log Horner depth appends exactly one bounded odd monomial. -/
theorem complexLog_horner_succ_eq_add_term (w : Data.Gaussian.Basic.Canonical) :
    ∀ (degree index : Nat),
      Horner.Basic.horner w index (degree + 1) =
        Horner.Basic.horner w index degree +
          Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm w index (degree + 1)
  | 0, index => by
      rw [Horner.Basic.horner_succ,
        Horner.Basic.horner_zero,
        Horner.Basic.horner_zero,
        Horner.Basic.step_eq,
        Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm_succ,
          Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm_zero]
  | degree + 1, index => by
      calc
        Horner.Basic.horner w index (degree + 1 + 1) =
            Horner.Basic.step w index
              (Horner.Basic.horner w (index + 1)
                (degree + 1)) := rfl
        _ = Horner.Basic.step w index
              (Horner.Basic.horner w (index + 1) degree +
                Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm w (index + 1) (degree + 1)) := by
          rw [Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.complexLog_horner_succ_eq_add_term w
            degree (index + 1)]
        _ = Horner.Basic.step w index
              (Horner.Basic.horner w (index + 1) degree) +
            Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm w index (degree + 1 + 1) := by
          have termStep :
              ComplexLog.scalar
                    (ComplexLog.coefficient index) *
                  w * Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm w (index + 1) (degree + 1)
                    =
                Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm w index (degree + 1 + 1) := rfl
          rw [Horner.Basic.step_eq,
            Horner.Basic.step_eq, ← termStep]
          apply Data.Gaussian.Basic.ext <;>
            simp only [Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im,
              ComplexLog.scalar, Basic.one_re, Basic.one_im] <;> ring1
        _ = Horner.Basic.horner w index (degree + 1) +
            Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm w index (degree + 1 + 1) := rfl

/-- The finite logarithm Horner value is the sum of its retained monomial terms through the requested depth. -/
theorem complexLog_horner_eq_sum (w : Data.Gaussian.Basic.Canonical) :
    ∀ (depth index : Nat),
      Horner.Basic.horner w index depth =
        Prefix.sum (Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm w index) (depth + 1)
  | 0, index => by
      rw [Horner.Basic.horner_zero, Prefix.sum_succ,
        Prefix.sum_zero, Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm_zero,
        Data.Gaussian.Basic.zero_add]
  | depth + 1, index => by
      calc
        Horner.Basic.horner w index (depth + 1) =
            Horner.Basic.horner w index depth +
              Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm w index (depth + 1) :=
          Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.complexLog_horner_succ_eq_add_term w depth index
        _ = Prefix.sum (Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm w index) (depth + 1) +
              Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm w index (depth + 1) := by
          rw [Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.complexLog_horner_eq_sum w depth index]
        _ = Prefix.sum (Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm w index) (depth + 1 + 1)
          := rfl

/-- One displayed odd logarithm monomial `2 z^(2j+1)/(2j+1)`. -/
@[expose] public def localLogTerm (z : Data.Gaussian.Basic.Canonical) (degree : Nat) : Data.Gaussian.Basic.Canonical :=
  Scale.scale
    (2 / (2 * (degree : Fraction.Rational) + 1)) (z ^ (2 * degree + 1))

/-- Multiplying the inner logarithm Horner term by the outer sample factor gives the matching odd local-logarithm
monomial. -/
theorem outputFactor_mul_logHornerTerm (z : Data.Gaussian.Basic.Canonical) (degree : Nat) :
    Sample.outputFactor z *
        Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm (Sample.squaredArgument z)
          1 degree =
      Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.localLogTerm z degree := by
  rw [Sample.outputFactor_eq,
    Sample.squaredArgument_eq,
    Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.logHornerTerm_eq_scaled_power _ degree 1 (by decide),
    Scale.scalar_mul_eq_scale, Scale.scale_mul_scale]
  have priorOne : Odd.priorOdd 1 = 1 := by decide
  have priorDegree : Odd.priorOdd (1 + degree) = 2 * degree + 1 := by
    unfold Odd.priorOdd
    omega
  rw [priorOne, priorDegree]
  have denominatorCast :
      ((2 * degree + 1 : Nat) : Fraction.Rational) =
        2 * (degree : Fraction.Rational) + 1 := by
    rw [Purelib.Algebra.NatCast.add, Purelib.Algebra.NatCast.mul, Nat.cast_one]
    rfl
  rw [denominatorCast]
  rw [show ((1 : Nat) : Fraction.Rational) = 1 by rfl]
  change Scale.scale
      ((2 : Fraction.Rational) * (1 / (2 * (degree : Fraction.Rational) + 1)))
      (z * (z * z) ^ degree) = Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.localLogTerm z degree
  have coefficientIdentity :
      (2 : Fraction.Rational) * (1 / (2 * (degree : Fraction.Rational) + 1)) =
        2 / (2 * (degree : Fraction.Rational) + 1) := by
    rw [Algebra.Field.ExplicitField.div_eq_mul_inv,
      Algebra.Field.ExplicitField.div_eq_mul_inv,
      Fraction.Field.one_mul]
  rw [coefficientIdentity, Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.localLogTerm]
  congr 1
  calc
    z * (z * z) ^ degree = z * (z ^ 2) ^ degree := by rw [pow_two]
    _ = z * z ^ (2 * degree) := by rw [← pow_mul]
    _ = z ^ (2 * degree) * z :=
      Data.Gaussian.Basic.mul_comm _ _
    _ = z ^ (2 * degree + 1) := (pow_succ z (2 * degree)).symm

/-- Exact bounded-polynomial identification of every complex-log sample. -/
theorem complexLog_sample_eq_sum (z : Data.Gaussian.Basic.Canonical) (depth : Nat) :
    Sample.sample z depth =
      Prefix.sum (Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.localLogTerm z) (depth + 1) := by
  rw [Sample.sample_eq,
    Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.complexLog_horner_eq_sum,
    Prefix.mul_sum_left]
  exact Prefix.sum_congr
    (fun degree => Approximation.Gaussian.Logarithm.Local.Horner.Polynomial.outputFactor_mul_logHornerTerm z degree)
      (depth + 1)
end Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Polynomial

end
