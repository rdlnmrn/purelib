module

public import Purelib.Polynomial.Approximation.Gaussian.Residual
public import Purelib.Approximation.Gaussian.Geometric.SamplePrefix

/-! # Original polynomial residuals consuming checked saved observations -/

public section

namespace Purelib.Polynomial.Approximation.Gaussian.Residual

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian

/-- Consume saved original samples while retaining the polynomial, channel, scale and original comparison indices.

The exact scalar readback transfers the original residual bound. The original
comparison is reused at identical requests and indices; no extra synchronization
budget or equality of changed functions is introduced.
-/
@[expose] def withSamples {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (original : Residual polynomial channel) (cache : Sequence.SamplePrefix original.source.toApproximation) :
    Residual polynomial channel where
  degreePositive := original.degreePositive
  source := original.source.withSamples cache
  equivalent := by
    rewrite [Geometric.GeometricApproximation.withSamples_approximation]
    exact cache.comparisonRight original.equivalent
  scale := original.scale
  scale_nonnegative := original.scale_nonnegative
  bound := by
    intro index
    rewrite [Geometric.GeometricApproximation.withSamples_sample]
    exact original.bound index

/-- The cached residual reads the exact original scalar observation at every original finite index. -/
theorem withSamples_sample {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (original : Residual polynomial channel) (cache : Sequence.SamplePrefix original.source.toApproximation)
    (index : Nat) : (original.withSamples cache).source.sample index = original.source.sample index :=
  original.source.withSamples_sample cache index

/-- Saved observation lookup preserves the actual original residual scale. -/
theorem withSamples_scale {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (original : Residual polynomial channel) (cache : Sequence.SamplePrefix original.source.toApproximation) :
    (original.withSamples cache).scale = original.scale := rfl

end Purelib.Polynomial.Approximation.Gaussian.Residual

end
