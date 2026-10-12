module
import Purelib.Data.Nat.Multiplication
import Purelib.Algebra.NatCast

public import Purelib.Data.CCL.Encoding.Block.Integral
public import Purelib.Data.CCL.Encoding.Encoder.Annulus
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Cancellation
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.Nat.BinaryNormalization
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix

import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Constants.Power
import Purelib.Data.GaussianInt.Power
import Purelib.Data.GaussianInt.Constants
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Field.Defs
meta import Purelib.Elab.ConstructiveInjectivity

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Normalization

open Purelib.Algebra

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.List in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
set_option genInjectivity false in
/-- Retain an initial normalization header, integral radial matrix and exact annulus with reconstruction evidence.

The radial matrix sends the annulus's original displayed pair to a point equivalent to the input pair. Its retained
denominator coordinate is nonzero, preserving the same numerator, denominator and normalization witnesses. -/
structure InitialResult (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias) where
  /-- The exact initial high or low unary normalization word. -/ header :
    BinaryPrefix.Basic.SourceEncodingEncoderWordAlias
  /-- The retained integral radial normalization matrix. -/ radial : Matrix2.SourceEncodingEncoderIntegralMat2Alias
  /-- The exact normalized displayed fraction and closed annulus witness. -/ annulus : Annulus
  /-- The retained radial matrix maps this annulus pair to a point equivalent to the original source pair. -/
    radial_reconstruct :
    Line.Proj.Equivalent
      (Line.Matrix.act radial
        ⟨annulus.frac.numerator, annulus.frac.denominator⟩)
      ⟨fraction.numerator, fraction.denominator⟩
  /-- The denominator coordinate of that exact radial matrix image is nonzero. -/ radial_den_ne :
    (Line.Matrix.act radial
      ⟨annulus.frac.numerator, annulus.frac.denominator⟩).q ≠ 0

constructive_injectivity InitialResult

end Purelib.Data.CCL.Encoding.Encoder.Normalization

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Normalization

open Purelib.Algebra

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Nat in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Normalize a high-norm displayed fraction by scaling only its denominator by the retained integer gamma power.

The exact binary high scan chooses the exponent from the numerator and denominator norms. Store its unary header, scale
matrix, normalized annulus and reconstruction witnesses; the original numerator is unchanged. -/
@[expose] def initialHigh (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias) (_numeratorNonzero :
  fraction.numerator ≠ 0)
    (highBranch : 2 * GaussianInt.normNat fraction.denominator ≤ GaussianInt.normNat fraction.numerator) :
    Encoder.Normalization.InitialResult fraction := by
  let scan := BinaryNormalization.high
    (GaussianInt.normNat fraction.numerator) (GaussianInt.normNat fraction.denominator)
    (GaussianInt.normNat_pos fraction.denominatorNonzero) highBranch
  let denominator := GaussianInt.natPow GaussianInt.gammaInt scan.exponent * fraction.denominator
  have denominatorNonzero : denominator ≠ 0 :=
    GaussianInt.mul_ne_zero
      (GaussianInt.natPow_ne_zero GaussianInt.gammaInt (by decide) scan.exponent)
      fraction.denominatorNonzero
  let normalized : GaussianInt.Fraction := ⟨fraction.numerator, denominator, denominatorNonzero⟩
  have denominatorNorm :
      GaussianInt.normNat denominator = 2 ^ scan.exponent * GaussianInt.normNat fraction.denominator := by
    rw [show denominator = _ from rfl, GaussianInt.normNat_mul, GaussianInt.normNat_gammaInt_pow]
  have lower : GaussianInt.normNat normalized.denominator ≤ GaussianInt.normNat normalized.numerator := by
    dsimp only [normalized]
    rw [denominatorNorm]
    exact scan.lower
  have upper : GaussianInt.normNat normalized.numerator < 2 * GaussianInt.normNat normalized.denominator := by
    dsimp only [normalized]
    rw [denominatorNorm]
    calc
      GaussianInt.normNat fraction.numerator <
          2 ^ (scan.exponent + 1) * GaussianInt.normNat fraction.denominator := scan.upper
      _ = 2 * (2 ^ scan.exponent * GaussianInt.normNat fraction.denominator) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ scan.exponent) 2, Multiplication.mul_assoc]
  let entry : ComplexContinuedFraction.Encoding.Sector.Entry normalized.value := by
    rw [ComplexContinuedFraction.Encoding.Sector.Entry,
      ← Norm.Basic.normSq_eq_canonical, GaussianInt.Fraction.normSq_value]
    have denominatorPositive :
        (0 : Fraction.Basic.Rational) < (GaussianInt.normNat normalized.denominator : Nat) :=
      Fraction.Cast.Order.natCast_pos_direct
        (GaussianInt.normNat_pos normalized.denominatorNonzero)
    constructor
    · apply (Fraction.Order.Field.le_div_iff_pos denominatorPositive).2
      rw [Fraction.Field.one_mul]
      exact Fraction.Cast.Order.natCast_le_direct lower
    · apply (Fraction.Order.Field.div_lt_iff_pos denominatorPositive).2
      have castUpper := Fraction.Cast.Order.natCast_lt_direct upper
      simpa only [NatCast.mul, Nat.cast_ofNat] using castUpper
  refine
    ⟨List.replicate scan.exponent true ++ [false],
      Line.Matrix.scale (GaussianInt.natPow GaussianInt.gammaInt scan.exponent),
      ⟨normalized, ⟨entry.1, entry.2.le⟩⟩, ?_, ?_⟩
  · dsimp only [normalized, denominator, Line.Proj.Equivalent,
      Line.Matrix.act, Line.Matrix.scale]
    ring1
  · dsimp only [normalized, Line.Matrix.act, Line.Matrix.scale]
    rw [GaussianInt.zero_mul, GaussianInt.one_mul, GaussianInt.zero_add]
    exact denominatorNonzero
end Purelib.Data.CCL.Encoding.Encoder.Normalization

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Normalization

open Purelib.Algebra

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Nat in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Normalize a nonzero low-norm displayed fraction by scaling only its numerator by the retained integer gamma power.

The exact binary low scan chooses the exponent. Store the leading-false unary header, initial-low radial matrix and
normalized annulus with their original reconstruction and denominator witnesses. -/
@[expose] def initialLow (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias) (numeratorNonzero :
  fraction.numerator ≠ 0)
    (lowBranch : GaussianInt.normNat fraction.numerator < 2 * GaussianInt.normNat fraction.denominator) :
    Encoder.Normalization.InitialResult fraction := by
  let scan := BinaryNormalization.low
    (GaussianInt.normNat fraction.numerator) (GaussianInt.normNat fraction.denominator)
    (GaussianInt.normNat_pos numeratorNonzero) (GaussianInt.normNat_pos fraction.denominatorNonzero) lowBranch
  let numerator := GaussianInt.natPow GaussianInt.gammaInt scan.exponent * fraction.numerator
  let normalized : GaussianInt.Fraction := ⟨numerator, fraction.denominator, fraction.denominatorNonzero⟩
  have numeratorNorm :
      GaussianInt.normNat numerator = 2 ^ scan.exponent * GaussianInt.normNat fraction.numerator := by
    rw [show numerator = _ from rfl, GaussianInt.normNat_mul, GaussianInt.normNat_gammaInt_pow]
  have lower : GaussianInt.normNat normalized.denominator ≤ GaussianInt.normNat normalized.numerator := by
    dsimp only [normalized]
    rw [numeratorNorm]
    exact scan.lower
  have upper : GaussianInt.normNat normalized.numerator < 2 * GaussianInt.normNat normalized.denominator := by
    dsimp only [normalized]
    rw [numeratorNorm]
    exact scan.upper
  let entry : ComplexContinuedFraction.Encoding.Sector.Entry normalized.value := by
    rw [ComplexContinuedFraction.Encoding.Sector.Entry,
      ← Norm.Basic.normSq_eq_canonical, GaussianInt.Fraction.normSq_value]
    have denominatorPositive :
        (0 : Fraction.Basic.Rational) < (GaussianInt.normNat normalized.denominator : Nat) :=
      Fraction.Cast.Order.natCast_pos_direct
        (GaussianInt.normNat_pos normalized.denominatorNonzero)
    constructor
    · apply (Fraction.Order.Field.le_div_iff_pos denominatorPositive).2
      rw [Fraction.Field.one_mul]
      exact Fraction.Cast.Order.natCast_le_direct lower
    · apply (Fraction.Order.Field.div_lt_iff_pos denominatorPositive).2
      have castUpper := Fraction.Cast.Order.natCast_lt_direct upper
      simpa only [NatCast.mul, Nat.cast_ofNat] using castUpper
  refine
    ⟨false :: List.replicate scan.exponent true ++ [false],
      Block.Integral.lowScaleInt scan.exponent,
      ⟨normalized, ⟨entry.1, entry.2.le⟩⟩, ?_, ?_⟩
  · dsimp only [normalized, numerator, Block.Integral.lowScaleInt,
      Line.Proj.Equivalent, Line.Matrix.act]
    ring1
  · dsimp only [normalized, Block.Integral.lowScaleInt, Line.Matrix.act]
    rw [GaussianInt.zero_mul, GaussianInt.zero_add]
    exact GaussianInt.mul_ne_zero
      (GaussianInt.natPow_ne_zero GaussianInt.gammaInt (by decide) scan.exponent) fraction.denominatorNonzero
end Purelib.Data.CCL.Encoding.Encoder.Normalization

end
