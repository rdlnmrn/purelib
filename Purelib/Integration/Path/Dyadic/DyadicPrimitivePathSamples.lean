module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.IncrementArea
public import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Tactic.Ring

@[expose] public section

/-! Certified dyadic paths evaluate each internal vertex once and compose
cached totals and areas. Retained endpoint values may be shared across blocks. -/
namespace Purelib.Integration.Path.Dyadic.DyadicPrimitivePathSamples

open Purelib.Data.Gaussian in
/-- The canonical Gaussian carrier for retained dyadic increments. -/
private abbrev Gaussian := Basic.Canonical

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
set_option genInjectivity false in
/-- A retained dyadic increment list with its exact defining equation and cached original summary.

The value function, depth and endpoint parameters remain indexed, linking both cached total and area to this precise
subdivision. -/
structure DyadicSample (value : Fraction.Rational → Basic.Canonical) (depth : Nat) (first last : Fraction.Rational)
  where
  /-- The cached ordered original dyadic increment list. -/ increments : List Basic.Canonical
  /-- The cache is exactly the subdivision of the original function at its retained depth and endpoints. -/
    increments_eq : increments = DyadicPrimitivePaths.dyadicIncrements value depth first last
  /-- The cached total and area summary indexed by these exact retained increments. -/ summary : IncrementArea.Summary
    increments

constructive_injectivity DyadicSample

namespace DyadicSample

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
/-- Build a dyadic sample from retained exact endpoint values, sharing each computed midpoint value between the two
recursive children.

The original value function and endpoint equalities remain attached to both children; their summaries are combined from
cached totals and areas. -/
def buildFrom (value : Fraction.Rational → Basic.Canonical) : (depth : Nat) → (first last : Fraction.Rational) →
    (firstValue lastValue : Basic.Canonical) → firstValue = value first → lastValue = value last →
    DyadicPrimitivePathSamples.DyadicSample value depth first last
  | 0, first, last, firstValue, lastValue, firstEq, lastEq =>
      ⟨[lastValue - firstValue], by rw [firstEq, lastEq]; rfl, IncrementArea.Summary.build [lastValue - firstValue]⟩
  | depth + 1, first, last, firstValue, lastValue, firstEq, lastEq =>
      let middle := PreparedBoxPartitions.midpoint first last
      let middleValue := value middle
      let left := Purelib.Integration.Path.Dyadic.DyadicPrimitivePathSamples.DyadicSample.buildFrom value depth first
        middle firstValue middleValue firstEq rfl
      let right := Purelib.Integration.Path.Dyadic.DyadicPrimitivePathSamples.DyadicSample.buildFrom value depth middle
        last middleValue lastValue rfl lastEq
      ⟨left.increments ++ right.increments, by rw [left.increments_eq, right.increments_eq]; rfl,
        left.summary.append right.summary⟩

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Path.Dyadic
/-- Evaluate the original endpoint values and construct their retained dyadic increment sample. -/
def build (value : Fraction.Rational → Basic.Canonical) (depth : Nat) (first last : Fraction.Rational) :
    DyadicPrimitivePathSamples.DyadicSample value depth first last :=
  DyadicPrimitivePathSamples.DyadicSample.buildFrom value depth first last (value first) (value last) rfl rfl

/-- The retained sample summary's total is the exact original endpoint displacement. -/
theorem total {value : Fraction.Rational → Basic.Canonical} {depth : Nat} {first last : Fraction.Rational}
    (sample : DyadicPrimitivePathSamples.DyadicSample value depth first last) : sample.summary.total = value last -
      value first := by
  rw [sample.summary.total_eq, sample.increments_eq, DyadicPrimitivePaths.dyadicIncrements_sum]

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
/-- The retained sample summary's area is its original dyadic area minus the endpoint chord area. -/
theorem area {value : Fraction.Rational → Basic.Canonical} {depth : Nat} {first last : Fraction.Rational}
    (sample : DyadicPrimitivePathSamples.DyadicSample value depth first last) :
    sample.summary.area = DyadicBoundaryRibbon.dyadicArea value depth first last - BoundaryRibbon.area (value first)
      (value last) := by
  have traced := DyadicPrimitivePaths.traceArea_dyadicIncrements value depth first last
  rw [IncrementArea.traceArea_eq, DyadicPrimitivePaths.dyadicIncrements_sum,
    BoundaryRibbon.area_sub_self_right] at traced
  rw [sample.summary.area_eq, sample.increments_eq, ← traced]
  ring1

end DyadicSample
end Purelib.Integration.Path.Dyadic.DyadicPrimitivePathSamples
