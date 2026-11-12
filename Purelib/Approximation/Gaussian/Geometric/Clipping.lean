module

public import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Data.Rat.Interval.Unit.Clamp
import Purelib.Data.Gaussian.Components.Projection
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Unit-interval clipping of geometric Gaussian streams

Project each original sample to its real coordinate and clip to the rational
unit interval. The original movement scale is retained, and the new samples
have squared norm at most one. No completed value or comparison is selected.
-/

namespace Purelib.Approximation.Gaussian.Geometric.GeometricApproximation

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

/-- Squared real-coordinate displacement is bounded by the SAME Gaussian displacement. -/
private theorem real_difference_le (first last : Canonical) :
    (first.re - last.re) ^ 2 ≤ Norm.Basic.normSq (first - last) := by
  have actual := Components.Projection.normSq_realPart_le (first - last)
  have scalar : Norm.Basic.normSq (Components.Projection.realPart (first - last)) =
      (first.re - last.re) ^ 2 := by
    change (first.re - last.re) ^ 2 + (0 : Fraction.Rational) ^ 2 = _
    ring1
  exact scalar.symm.trans_le actual

public section

/-- Project the original samples to the unit real interval, preserving their geometric movement scale. -/
def clipReal (source : GeometricApproximation) : GeometricApproximation where
  sample := fun index => ⟨Interval.Unit.clamp (source.sample index).re, 0⟩
  errorScale := source.errorScale
  errorScale_nonneg := source.errorScale_nonneg
  later_close := by
    intro earlier later order
    have scalar : Norm.Basic.normSq
        ((⟨Interval.Unit.clamp (source.sample later).re, 0⟩ : Canonical) -
          ⟨Interval.Unit.clamp (source.sample earlier).re, 0⟩) =
        (Interval.Unit.clamp (source.sample later).re - Interval.Unit.clamp (source.sample earlier).re) ^ 2 := by
      change (_ - _) ^ 2 + (0 - 0 : Fraction.Rational) ^ 2 = _
      ring1
    exact scalar.trans_le ((Interval.Unit.clamp_distance_le (source.sample later).re
      (source.sample earlier).re).trans ((real_difference_le _ _).trans (source.later_close order)))
  centerBound := 1
  centerBound_nonneg := by decide +kernel
  sample_bounded := by
    intro index
    have inside := Interval.Unit.clamp_inside (source.sample index).re
    have bounded := Fraction.Order.Arithmetic.pow_le_pow_direct inside.1 inside.2 2
    have scalar : Norm.Basic.normSq (⟨Interval.Unit.clamp (source.sample index).re, 0⟩ : Canonical) =
        Interval.Unit.clamp (source.sample index).re ^ 2 := by
      change _ ^ 2 + (0 : Fraction.Rational) ^ 2 = _
      ring1
    exact scalar.trans_le (bounded.trans_eq (by decide +kernel))

/-- Each clipped sample retains the original real coordinate and its finite unit-interval projection. -/
theorem clipReal_sample (source : GeometricApproximation) (index : Nat) :
    (clipReal source).sample index = (⟨Interval.Unit.clamp (source.sample index).re, 0⟩ : Canonical) := by
  unfold clipReal
  rfl

end

end Purelib.Approximation.Gaussian.Geometric.GeometricApproximation
