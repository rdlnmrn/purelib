module

public import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Comparison
public import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached finite observations of independently scheduled original cursors

The schedule comparison retains its two actual output machines, prefixes and
own parser origins. A separate finite Euclidean sample request computes its
indices and caches those actual original-name readings. The Euclidean sample
bound and each cursor's projective cylinder certificate stay distinct.
-/

public section
namespace Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic.ChannelCursor.ScheduleComparison

open Purelib.Approximation.Gaussian.Equivalence (Comparison)
open Purelib.Approximation.Gaussian.Name
open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- The actual sampled approximation owner of the retained left output channel. -/
@[expose] def leftApproximation {left right : ChannelCursor} {leftSchedule rightSchedule : List RequestStep}
    (result : ScheduleComparison left right leftSchedule rightSchedule) :=
  Sampling.approximation result.outputLeft.channel.name

/-- The actual sampled approximation owner of the retained right output channel. -/
@[expose] def rightApproximation {left right : ChannelCursor} {leftSchedule rightSchedule : List RequestStep}
    (result : ScheduleComparison left right leftSchedule rightSchedule) :=
  Sampling.approximation result.outputRight.channel.name

set_option genInjectivity false in
/-- Actual cached samples of one finite comparison between the two retained original output channels. -/
structure Observation {left right : ChannelCursor} {leftSchedule rightSchedule : List RequestStep}
    (result : ScheduleComparison left right leftSchedule rightSchedule)
    (leftStart rightStart : Nat) (target : Fraction.Rational) where
  /-- The computed all-later comparison with its original starts and Euclidean squared tolerance. -/
  comparison : Comparison result.leftApproximation result.rightApproximation leftStart rightStart target
  /-- The actual retained left sample at its computed original-name index. -/
  first : Basic.Canonical
  /-- The actual retained right sample at its computed original-name index. -/
  second : Basic.Canonical
  /-- The first reading comes from the exact left owner and selected index. -/
  first_eq : first = result.leftApproximation.sample comparison.leftIndex
  /-- The second reading comes from the exact right owner and selected index. -/
  second_eq : second = result.rightApproximation.sample comparison.rightIndex
  /-- The retained squared separation of these same actual sample readings. -/
  residual : Fraction.Rational
  /-- The stored separation is the exact Euclidean squared sample difference. -/
  residual_eq : residual = Norm.Basic.normSq (first - second)
  /-- These retained readings satisfy the original requested Euclidean tolerance. -/
  accurate : residual < target

constructive_injectivity Observation

/-- Compute one comparison request from the retained law and cache its actual original sample readings once. -/
@[expose] def observe {left right : ChannelCursor} {leftSchedule rightSchedule : List RequestStep}
    (result : ScheduleComparison left right leftSchedule rightSchedule)
    (leftStart rightStart : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    Observation result leftStart rightStart target :=
  let comparison := result.law.equivalent.compare leftStart rightStart target positive
  let first := result.leftApproximation.sample comparison.leftIndex
  let second := result.rightApproximation.sample comparison.rightIndex
  let residual := Norm.Basic.normSq (first - second)
  ⟨comparison, first, second, rfl, rfl, residual, rfl, comparison.close (Nat.le_refl _) (Nat.le_refl _)⟩

end Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic.ChannelCursor.ScheduleComparison
end
