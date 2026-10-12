module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Constants.Power
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Power
import Purelib.Data.Gaussian.Power
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Basic

open Purelib.Data.GaussianInt.Fraction.Basic

section
@[expose] public section
namespace Purelib.Data.GaussianInt.Fraction.Scale

/-- Scaling only a displayed Gaussian denominator by a power of gamma scales its exact
value inversely.

The original numerator equality and exact denominator identity retain both
presentations; cross-multiplication proves the corresponding Gaussian-rational power
relation. -/
private theorem value_of_scaled_den
    (source normalized : SourceEncodingEncoderFracAlias) (exponent : Nat)
    (numeratorIdentity : normalized.numerator = source.numerator)
    (denominatorIdentity : normalized.denominator =
      GaussianInt.natPow GaussianInt.gammaInt exponent * source.denominator) :
    Power.natPow
        Canonical.gamma exponent *
      normalized.value = source.value := by
  apply Field.mul_right_cancel_of_ne
    source.denominatorGaussianNonzero
  calc
    (Power.natPow
          Canonical.gamma exponent *
        normalized.value) * GaussianInt.toGaussian source.denominator =
        normalized.value *
          (Power.natPow
            Canonical.gamma exponent *
              GaussianInt.toGaussian source.denominator) := by
      apply Basic.ext <;>
        simp only [Basic.mul_re,
          Basic.mul_im] <;>
        ring1
    _ = normalized.value * GaussianInt.toGaussian normalized.denominator := by
      rw [denominatorIdentity, GaussianInt.toGaussian_mul, GaussianInt.toGaussian_gammaInt_pow]
    _ = GaussianInt.toGaussian normalized.numerator := normalized.value_mul_denominator
    _ = GaussianInt.toGaussian source.numerator := by rw [numeratorIdentity]
    _ = source.value * GaussianInt.toGaussian source.denominator :=
      source.value_mul_denominator.symm
end Purelib.Data.GaussianInt.Fraction.Scale

end

section
@[expose] public section
namespace Purelib.Data.GaussianInt.Fraction.Scale

/-- Scaling only a displayed Gaussian numerator by a power of gamma scales its exact
value by that power. -/
private theorem value_of_scaled_num
    (source normalized : SourceEncodingEncoderFracAlias) (exponent : Nat)
    (numeratorIdentity : normalized.numerator =
      GaussianInt.natPow GaussianInt.gammaInt exponent * source.numerator)
    (denominatorIdentity : normalized.denominator = source.denominator) :
    normalized.value =
      Power.natPow
        Canonical.gamma exponent * source.value := by
  apply Field.mul_right_cancel_of_ne
    source.denominatorGaussianNonzero
  calc
    normalized.value * GaussianInt.toGaussian source.denominator =
        normalized.value * GaussianInt.toGaussian normalized.denominator := by
      rw [denominatorIdentity]
    _ = GaussianInt.toGaussian normalized.numerator := normalized.value_mul_denominator
    _ = GaussianInt.toGaussian (GaussianInt.natPow GaussianInt.gammaInt exponent * source.numerator) := by
      rw [numeratorIdentity]
    _ = Power.natPow
          Canonical.gamma exponent *
        GaussianInt.toGaussian source.numerator := by
      rw [GaussianInt.toGaussian_mul, GaussianInt.toGaussian_gammaInt_pow]
    _ = Power.natPow
          Canonical.gamma exponent *
        (source.value * GaussianInt.toGaussian source.denominator) := by
      rw [source.value_mul_denominator]
    _ = (Power.natPow
          Canonical.gamma exponent * source.value) *
        GaussianInt.toGaussian source.denominator := by
      apply Basic.ext <;>
        simp only [Basic.mul_re,
          Basic.mul_im] <;>
        ring1
end Purelib.Data.GaussianInt.Fraction.Scale

end
