module

public import Purelib.Integration.Program.Gaussian.Cached.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Scale
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Scaling certified original integration caches -/

public section
namespace Purelib.Integration.Program.Gaussian.Cached.Basic

open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction

namespace CachedModel

/-- Scale the actual retained path, sample and allowance without invoking its producer again. -/
@[expose] def scale (factor : Basic.Canonical) (cache : CachedModel) : CachedModel where
  model := cache.model.scale factor
  sample := factor * cache.sample
  sample_eq := by
    change factor * cache.sample = (cache.model.scale factor).integralSample
    rw [cache.model.scale_integralSample, cache.sample_eq]
  allowance := Basic.Canonical.normSq factor * cache.allowance
  allowance_eq := by
    change Basic.Canonical.normSq factor * cache.allowance = (cache.model.scale factor).aggregateAllowance
    rw [cache.model.scale_aggregateAllowance, cache.allowance_eq]

end CachedModel

namespace CachedProgram

/-- Scale every original integration cache and derive its coefficient-weighted error and center bounds. -/
@[expose] def scale (factor : Basic.Canonical) (program : CachedProgram) : CachedProgram where
  stage index := CachedModel.scale factor (program.stage index)
  errorScale := Basic.Canonical.normSq factor * program.errorScale
  errorScale_nonneg := Order.Arithmetic.mul_nonneg_direct
    (Basic.Canonical.normSq_nonneg factor) program.errorScale_nonneg
  modelAllowance_le := by
    intro index
    change Basic.Canonical.normSq factor * (program.stage index).allowance ≤
      Geometric.Basic.quarterRadius (Basic.Canonical.normSq factor * program.errorScale) index
    exact (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (program.modelAllowance_le index)
      (Basic.Canonical.normSq_nonneg factor)).trans_eq (by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1)
  later_close := by
    intro earlier later order
    change Norm.Basic.normSq
      (factor * (program.stage later).sample - factor * (program.stage earlier).sample) ≤ _
    have difference : factor * (program.stage later).sample - factor * (program.stage earlier).sample =
        factor * ((program.stage later).sample - (program.stage earlier).sample) := by ring1
    rw [difference, Norm.Basic.normSq_mul,
      Norm.Basic.normSq_eq_canonical factor]
    exact (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (program.later_close order)
      (Basic.Canonical.normSq_nonneg factor)).trans_eq (by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1)
  centerBound := Basic.Canonical.normSq factor * program.centerBound
  centerBound_nonneg := Order.Arithmetic.mul_nonneg_direct
    (Basic.Canonical.normSq_nonneg factor) program.centerBound_nonneg
  sample_bounded := by
    intro index
    change Norm.Basic.normSq (factor * (program.stage index).sample) ≤ _
    rw [Norm.Basic.normSq_mul,
      Norm.Basic.normSq_eq_canonical factor]
    exact Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (program.sample_bounded index)
      (Basic.Canonical.normSq_nonneg factor)

/-- The scaled program reads the same original cache sample multiplied by the coefficient. -/
theorem scale_sample (factor : Basic.Canonical) (program : CachedProgram) (index : Nat) :
    ((program.scale factor).stage index).sample = factor * (program.stage index).sample := rfl

/-- The scaled program retains the scaled original path model at the same stage. -/
theorem scale_model (factor : Basic.Canonical) (program : CachedProgram) (index : Nat) :
    ((program.scale factor).stage index).model = (program.stage index).model.scale factor := rfl

end CachedProgram
end Purelib.Integration.Program.Gaussian.Cached.Basic
end
