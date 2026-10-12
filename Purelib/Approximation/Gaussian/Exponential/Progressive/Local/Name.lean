module
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
public import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Bounds
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Budget
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Sample
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Sampling
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.UnitDisk
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Sequence.UnitDisk
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name (UnitDisk)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Exponential.Horner

open Purelib.Approximation.Gaussian.Exponential.Progressive

open Purelib.Approximation.Gaussian.Exponential.Progressive.Local

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

section
@[expose] public section

/-!
# Progressive finite exponential

This is the local core of exponential as a CCL-to-CCL computation.  The input
is an existing arithmetic CCL name together with a finite domain certificate
for its candidates.  At natural index `n`, the output evaluates the depth-`n`
Horner program at the input's depth-`n` displayed rational witness, packages
those samples as a progressive enclosure process, and starts the unchanged
productive raw CCL controller on that process.  Thus neither side names a
completed point, while every requested finite output prefix is genuinely a
CCL prefix for the calculated exponential enclosure.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Name

/-- Evaluate the finite exponential Horner program at the certified input's canonical sample and matching depth. -/
def domainSample (input :
  Named) (domain : UnitDisk input) (index : Nat) :
    Data.Gaussian.Basic.Canonical :=
  Sample.sampleFrom (Sampling.unitDiskSamples input domain).value index

/-- Simultaneous input refinement and Horner-depth refinement have one explicit quarter-power squared-error bound. -/
theorem sample_later_close {input :
  Named} (domain : UnitDisk input)
    {earlier later : Nat} (order : earlier ≤ later) :
    Data.Gaussian.Norm.Basic.normSq
      (Sample.sampleFrom (Sampling.unitDiskSamples input domain).value later -
        Sample.sampleFrom (Sampling.unitDiskSamples input domain).value earlier) ≤
      Geometric.Basic.quarterRadius Budget.errorScale earlier := by
  exact Local.Bounds.sampleFrom_later_close (Sampling.unitDiskSamples input domain) order

/-- Every finite exponential sample of the unit-disk input has squared norm at most ten. -/
theorem sample_bounded {input :
  Named} (domain : UnitDisk input)
    (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (domainSample
      input domain index) ≤ 10 :=
  Sample.sample_bounded _ (Sampling.inputSample_unit domain index) index

/-- The accuracy sidechannel for the local CCL exponential transform. Its `Possible` predicate contains only later
displayed output samples. -/
def approximation (input :
  Named) (domain : UnitDisk input) : ApproximationData where
  sample := domainSample input domain
  radiusSq := Geometric.Basic.quarterRadius Budget.errorScale
  radiusSq_nonneg index :=
    Geometric.Basic.quarterRadius_nonneg Budget.errorScale_nonneg index
  later_close := sample_later_close domain
  refineIndex current target _ :=
    Search.firstQuarterBelow Budget.errorScale current target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge Budget.errorScale current target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate Budget.errorScale
      Budget.errorScale_nonneg
  centerBound := 10
  centerBound_nonneg := by decide
  sample_bounded := sample_bounded domain

/-- Convert a unit-disk arithmetic CCL name into the corresponding productive local exponential CCL name. -/
def named (input : Named)
  (domain : UnitDisk input) : Named :=
  (approximation input domain).toNamed
end Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Name

end
