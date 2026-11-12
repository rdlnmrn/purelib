module

public import Purelib.Data.Gaussian.Field
public import Purelib.Data.Rat.Fraction.Square
import Purelib.Data.Rat.Fraction.Field

public section

namespace Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat

/-- Retain the exact original Gaussian norm square using its already reduced coordinate squares.

The original Gaussian is the certificate's source. Direct rational squaring
consumes its retained coprimality witnesses, and the complete rational value
agrees with the original norm-square computation at every source, including zero.
-/
@[expose] def prepareNorm (source : Canonical) : { value : Rational // value = normSq source } :=
  ⟨Fraction.square source.re + Fraction.square source.im, by
    change Fraction.square source.re + Fraction.square source.im =
      source.re * source.re + source.im * source.im
    rewrite [Fraction.square_eq_mul source.re, Fraction.square_eq_mul source.im]
    rfl⟩

/-- The retained prepared norm is the complete original norm-square rational. -/
theorem prepareNorm_eq (source : Canonical) : (prepareNorm source).val = normSq source :=
  (prepareNorm source).property

/-- Construct the original total Gaussian inverse from an exact retained norm-square certificate.

Both coordinate divisions consume that same retained rational. The source
and complete norm equality remain explicit, so no separate nonzero hypothesis
or alternate behavior at zero is introduced.
-/
@[expose] def inverseFromNorm (source : Canonical)
    (norm : { value : Rational // value = normSq source }) : Canonical :=
  ⟨source.re / norm.val, -source.im / norm.val⟩

/-- Inversion from the exact retained norm returns the complete original Gaussian reciprocal. -/
theorem inverseFromNorm_eq (source : Canonical)
    (norm : { value : Rational // value = normSq source }) :
    inverseFromNorm source norm = source⁻¹ := by
  change (⟨source.re / norm.val, -source.im / norm.val⟩ : Canonical) =
    ⟨source.re / normSq source, -source.im / normSq source⟩
  exact congrArg (fun value : Rational =>
    (⟨source.re / value, -source.im / value⟩ : Canonical)) norm.property

/-- Compute the total inverse with direct axis reciprocals and a retained norm for nonaxis inputs.

Real and purely imaginary inputs use their one nonzero coordinate directly,
including the original zero convention. Other inputs consume the same exact
prepared norm in both coordinate divisions.
-/
@[expose] def preparedInverse (source : Canonical) : Canonical :=
  if source.im = 0 then ⟨source.re⁻¹, 0⟩
  else if source.re = 0 then ⟨0, -(source.im⁻¹)⟩
  else inverseFromNorm source (prepareNorm source)

/-- The prepared inverse preserves the complete original reciprocal for every Gaussian, including zero. -/
theorem preparedInverse_eq (source : Canonical) : preparedInverse source = source⁻¹ := by
  have coordinate (value : Rational) : value / (value * value) = value⁻¹ := by
    by_cases zero : value = 0
    · rewrite [zero, Fraction.Field.zero_div_direct, Fraction.Field.inv_zero]
      rfl
    · rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.inv_mul_direct,
        ← Fraction.Field.mul_assoc, Fraction.Field.mul_inv_cancel value zero, Fraction.Field.one_mul]
      rfl
  unfold preparedInverse
  split
  next imaginaryZero =>
    apply Basic.ext
    · change source.re⁻¹ = source.re / (source.re * source.re + source.im * source.im)
      rewrite [imaginaryZero, Fraction.Field.zero_mul_direct, _root_.add_zero]
      exact (coordinate source.re).symm
    · change 0 = -source.im / (source.re * source.re + source.im * source.im)
      rewrite [imaginaryZero, show -(0 : Rational) = 0 from rfl, Fraction.Field.zero_div_direct]
      rfl
  next =>
    split
    next realZero =>
      apply Basic.ext
      · change 0 = source.re / (source.re * source.re + source.im * source.im)
        rewrite [realZero, Fraction.Field.zero_div_direct]
        rfl
      · change -(source.im⁻¹) = -source.im / (source.re * source.re + source.im * source.im)
        rewrite [realZero, Fraction.Field.zero_mul_direct, Fraction.Field.zero_add,
          Fraction.Field.div_eq_mul_inv_direct, _root_.neg_mul]
        exact (congrArg (fun value : Rational => -value) (coordinate source.im)).symm
    next => exact inverseFromNorm_eq source (prepareNorm source)

end Purelib.Data.Gaussian.Basic.Canonical

end
