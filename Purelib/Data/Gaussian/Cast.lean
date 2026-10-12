module
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.Ring

/-! Exact scalar embeddings into the original Gaussian rational carrier. -/

public section

namespace Purelib.Data.Gaussian.Cast

open Purelib.Data
open Purelib.Data.Gaussian.Basic
open Purelib.Data.Rat.Fraction

/-- Embed the supplied rational coordinate on the real Gaussian axis. -/
@[expose] def CurveCanonical.ofCoordinate (value : Rational) : Canonical := ⟨value, 0⟩
/-- Embed the supplied rational coordinate on the imaginary Gaussian axis. -/
@[expose] def BoundaryCanonical.imaginaryCoordinate (value : Rational) : Canonical := ⟨0, value⟩

/-- The real coordinate of a natural Gaussian cast is its rational natural cast. -/
@[simp] theorem natCast_re (value : Nat) :
    ((value : Canonical).re) = (value : Rational) := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ, Gaussian.Basic.add_re, inductionHypothesis, Gaussian.Basic.one_re, Nat.cast_succ]

/-- The imaginary coordinate of every natural Gaussian cast is zero. -/
@[simp] theorem natCast_im (value : Nat) : ((value : Canonical).im) = 0 := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ, Gaussian.Basic.add_im, inductionHypothesis, Gaussian.Basic.one_im]
      exact _root_.zero_add 0

/-- Embed the supplied rational coordinate on the real Gaussian axis. -/
@[expose] def Path.ofCoordinate (t : Rational) : Canonical := ⟨t, 0⟩

/-- Real-axis inclusion retains the original rational coordinate. -/
@[simp] theorem ofCoordinate_re (t : Rational) : (Path.ofCoordinate t).re = t := rfl
/-- Real-axis inclusion has zero imaginary coordinate. -/
@[simp] theorem ofCoordinate_im (t : Rational) : (Path.ofCoordinate t).im = 0 := rfl

/-- Embed the supplied integer as an exact real Gaussian rational. -/
@[expose] def integralGaussian (value : Int) : Canonical := ⟨(value : Rational), 0⟩

/-- Embed the supplied rational coordinate on the real Gaussian axis. -/
@[expose] def LegendrePeriodJets.realGaussian (value : Rational) : Canonical := ⟨value, 0⟩

/-- Embed the supplied rational coordinate on the real Gaussian axis. -/
@[expose] def CoordinateTaylor.ofCoordinate (value : Rational) : Canonical := ⟨value, 0⟩

/-- Real-axis inclusion sends rational zero to Gaussian zero. -/
@[simp] theorem ofCoordinate_zero : CoordinateTaylor.ofCoordinate 0 = 0 := rfl

/-- Real-axis inclusion preserves rational addition. -/
@[simp] theorem ofCoordinate_add (left right : Rational) :
    CoordinateTaylor.ofCoordinate (left + right) = CoordinateTaylor.ofCoordinate left + CoordinateTaylor.ofCoordinate
      right := by
  apply Gaussian.Basic.ext
  · rfl
  · change (0 : Rational) = 0 + 0
    rw [_root_.zero_add]

/-- Real-axis inclusion preserves rational multiplication. -/
@[simp] theorem ofCoordinate_mul (left right : Rational) :
    CoordinateTaylor.ofCoordinate (left * right) = CoordinateTaylor.ofCoordinate left * CoordinateTaylor.ofCoordinate
      right := by
  apply Gaussian.Basic.ext <;>
    simp only [CoordinateTaylor.ofCoordinate, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- Real-axis inclusion preserves rational subtraction. -/
@[simp] theorem ofCoordinate_sub (left right : Rational) :
    CoordinateTaylor.ofCoordinate (left - right) = CoordinateTaylor.ofCoordinate left - CoordinateTaylor.ofCoordinate
      right := by
  apply Gaussian.Basic.ext
  · rfl
  · change (0 : Rational) = 0 - 0
    rw [Arithmetic.sub_eq_add_neg_direct, neg_zero,
      _root_.zero_add]

/-- The squared norm of a real-axis inclusion is the square of its rational coordinate. -/
@[simp] theorem ofCoordinate_normSq (value : Rational) :
    Canonical.normSq (CoordinateTaylor.ofCoordinate value) = value ^ 2 := by
  simp only [Canonical.normSq, CoordinateTaylor.ofCoordinate]
  ring1

/-- Embed the supplied rational coordinate on the real Gaussian axis. -/
@[expose] def Winding.verticalBase (x : Rational) : Canonical := ⟨x, 0⟩

open Purelib.Algebra.Ring
open Purelib.Data.Gaussian.Basic
open Purelib.Data.Rat

/-- An integer embedded in Gaussian rationals has zero imaginary coordinate.

Both natural and negative-successor casts use the original Gaussian ring operations. -/
public theorem intCast_im (value : Int) : ((value : Canonical)).im = 0 := by
  cases value with
  | ofNat number =>
      change (((number : Nat) : Int) : Canonical).im = 0
      rw [Int.cast_natCast, natCast_im]
  | negSucc number => rw [IntCast.cast_negSucc, Basic.neg_im, natCast_im, _root_.neg_zero]

/-- Gaussian conjugation fixes embedded integers.

The cast lies on the real axis, so conjugation preserves its two retained coordinates. -/
public theorem conj_intCast (value : Int) : Basic.conj ((value : Canonical)) = (value : Canonical) := by
  apply Basic.ext
  · rfl
  · show -((value : Canonical)).im = ((value : Canonical)).im
    rw [intCast_im, _root_.neg_zero]

/-- The real coordinate of a Gaussian integer cast equals its rational integer cast.

The natural and negative-successor branches use the same original integer cast data in both carriers. -/
public theorem gaussian_int_re (value : Int) : (value : Canonical).re = (value : Fraction.Rational) := by
  cases value with
  | ofNat value =>
      change (((value : Nat) : Int) : Canonical).re = (((value : Nat) : Int) : Fraction.Rational)
      rw [Int.cast_natCast, natCast_re, Int.cast_natCast]
  | negSucc value => rw [IntCast.cast_negSucc, Basic.neg_re, natCast_re, IntCast.cast_negSucc]

end Purelib.Data.Gaussian.Cast
