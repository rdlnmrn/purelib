module
public import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Gaussian.Sequence.Geometric.Channel.Reciprocal

/-! # Geometric reciprocals under original all-index lower quadrance -/

public section

namespace Purelib.Approximation.Gaussian.Geometric.GeometricApproximation

open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

/-- Invert every original sample under a positive lower quadrance valid at every finite index.

The original sample program supplies the retained geometric movement and
magnitude data. The existing reciprocal channel computes the new bounds
once, before any inverse sample is requested.
-/
@[expose] def inverse (source : GeometricApproximation) (lower : Rational) (positive : 0 < lower)
    (bound : ∀ index, lower ≤ Norm.Basic.normSq (source.sample index)) : GeometricApproximation :=
  let channel : Sequence.Geometric.Channel source.sample :=
    ⟨source.errorScale, source.errorScale_nonneg, source.later_close,
      source.centerBound, source.centerBound_nonneg, source.sample_bounded⟩
  let reciprocal := channel.reciprocal lower positive bound
  ⟨fun index => Field.inv (source.sample index), reciprocal.errorScale, reciprocal.errorScale_nonneg,
    reciprocal.later_close, reciprocal.centerBound, reciprocal.centerBound_nonneg, reciprocal.bounded⟩

/-- Each geometric inverse sample is the reciprocal of the same original finite sample. -/
theorem inverse_sample (source : GeometricApproximation) (lower : Rational) (positive : 0 < lower)
    (bound : ∀ index, lower ≤ Norm.Basic.normSq (source.sample index)) (index : Nat) :
    (source.inverse lower positive bound).sample index = (source.sample index)⁻¹ :=
  (Field.inv_eq (source.sample index)).symm

/-- Each geometric inverse sample is the unit divided by the same original finite sample. -/
theorem inverse_sample_div (source : GeometricApproximation) (lower : Rational) (positive : 0 < lower)
    (bound : ∀ index, lower ≤ Norm.Basic.normSq (source.sample index)) (index : Nat) :
    (source.inverse lower positive bound).sample index = 1 / source.sample index := by
  rewrite [inverse_sample]
  exact (Basic.one_mul ((source.sample index)⁻¹)).symm

/-- The reciprocal movement scale is computed from the original scale and the same positive lower quadrance. -/
theorem inverse_errorScale (source : GeometricApproximation) (lower : Rational) (positive : 0 < lower)
    (bound : ∀ index, lower ≤ Norm.Basic.normSq (source.sample index)) :
    (source.inverse lower positive bound).errorScale = source.errorScale * (lower⁻¹ * lower⁻¹) := rfl

/-- The reciprocal magnitude bound is the inverse of the same original lower quadrance. -/
theorem inverse_centerBound (source : GeometricApproximation) (lower : Rational) (positive : 0 < lower)
    (bound : ∀ index, lower ≤ Norm.Basic.normSq (source.sample index)) :
    (source.inverse lower positive bound).centerBound = lower⁻¹ := rfl

end Purelib.Approximation.Gaussian.Geometric.GeometricApproximation

end
