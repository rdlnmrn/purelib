module
import Purelib.Algebra.NatCast

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Fraction.NaturalDenominator
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Data.Nat.Cast.Basic

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Gaussian.Fraction.NaturalDenominator.Norm
open Purelib.Data Purelib.Data.Rat
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt
open Purelib.Algebra

/-- Clearing the positive natural denominator gives the exact numerator quadrance.

The retained numerator and positive denominator represent the same Gaussian
fraction; taking quadrance of their clearing equation gives the identity. -/
theorem commonFraction_numerator_norm_identity (fraction :
  Basic.Canonical.Fraction.NaturalDenominator) :
    (GaussianInt.normNat fraction.numerator : Fraction.Rational) =
      (fraction.denominator : Fraction.Rational) ^ 2 * Data.Gaussian.Norm.Basic.normSq fraction.value := by
  have cleared := congrArg Data.Gaussian.Norm.Basic.normSq fraction.value_mul_denominator
  rw [Norm.Basic.normSq_mul, normSq_toGaussian, normNat_ofNat,
    normSq_toGaussian] at cleared
  change Data.Gaussian.Norm.Basic.normSq fraction.value *
    (((1 * fraction.denominator) * fraction.denominator : Nat) :
      Fraction.Rational) = _ at cleared
  rw [Nat.one_mul, NatCast.mul] at cleared
  rw [pow_two]
  calc
    (GaussianInt.normNat fraction.numerator : Fraction.Rational) =
        Data.Gaussian.Norm.Basic.normSq fraction.value *
          ((fraction.denominator : Fraction.Rational) * fraction.denominator) :=
      cleared.symm
    _ = ((fraction.denominator : Fraction.Rational) * fraction.denominator) *
        Data.Gaussian.Norm.Basic.normSq fraction.value := mul_comm _ _
end Purelib.Data.Gaussian.Fraction.NaturalDenominator.Norm

end
