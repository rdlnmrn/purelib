module

public import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Gaussian.Sequence.SamplePrefix

/-! # Saved observations of original geometric programs -/

public section

namespace Purelib.Approximation.Gaussian.Geometric.GeometricApproximation

open Purelib.Approximation.Gaussian

/-- Consume checked same-index saved samples while retaining the original geometric scale and uniform bound. -/
@[expose] def withSamples (source : GeometricApproximation)
    (cache : Sequence.SamplePrefix source.toApproximation) : GeometricApproximation where
  sample := cache.sample
  errorScale := source.errorScale
  errorScale_nonneg := source.errorScale_nonneg
  later_close := by
    intro earlier later order
    rewrite [cache.sample_eq later, cache.sample_eq earlier]
    exact source.later_close order
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := by
    intro index
    rewrite [cache.sample_eq index]
    exact source.sample_bounded index

/-- The saved geometric execution view retains each exact original scalar sample at its original index. -/
theorem withSamples_sample (source : GeometricApproximation)
    (cache : Sequence.SamplePrefix source.toApproximation) (index : Nat) :
    (source.withSamples cache).sample index = source.sample index := cache.sample_eq index

/-- The saved geometric view and ordinary saved approximation view execute the same sample and refinement programs. -/
theorem withSamples_approximation (source : GeometricApproximation)
    (cache : Sequence.SamplePrefix source.toApproximation) :
    (source.withSamples cache).toApproximation = cache.view := rfl

end Purelib.Approximation.Gaussian.Geometric.GeometricApproximation

end
