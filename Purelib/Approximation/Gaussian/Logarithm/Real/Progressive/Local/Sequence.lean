module

import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Domain
public import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Sampling
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local

open Purelib.Approximation.Rational

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Local logarithm as a CCL computation

This is the local core of logarithm as a CCL-to-CCL computation.  The input is
an arithmetic CCL name carrying an explicit overlapping chart certificate.
Every candidate is a displayed real Gaussian rational whose coordinate lies
in `[1/2,2]`.  The output synchronizes later finite input witnesses with later
finite Horner depths, packages the result as an accuracy sidechannel, and
starts the unchanged productive CCL controller on it.  It does not assert a
completed positive real input or a completed logarithm.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Sequence

set_option genInjectivity false in
/-- A rational sample sequence inside the real local-logarithm chart.

Each displayed sample lies between one half and two, and later samples have squared movement within the earlier index's
scale-four quarter-radius allowance. -/
structure ChartSamples where
  /-- The rational real sample at each finite index. -/ value : Nat → Fraction.Rational
  /-- Every sample is at least one half. -/ half : ∀ index, 1 / 2 ≤ value index
  /-- Every sample is at most two. -/ two : ∀ index, value index ≤ 2
  /-- Later samples have squared difference within the earlier index's scale-four quarter-radius allowance. -/ close : ∀
    {oldIndex newIndex : Nat}, oldIndex ≤ newIndex →
    (value newIndex - value oldIndex) ^ 2 ≤
      Geometric.Basic.quarterRadius 4 oldIndex

constructive_injectivity ChartSamples

/-- Package the original chart-certified name's canonical real samples with their chart bounds and geometric movement
certificate. -/
def chartSamples (input :
  Gaussian.Name.Basic.Named) (chart : Domain.Chart input) :
  ChartSamples :=
  { value := Sampling.inputSample input
    half := Sampling.inputSample_half chart
    two := Sampling.inputSample_two chart
    close := Sampling.inputSample_later_close chart }
end Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Sequence

end
