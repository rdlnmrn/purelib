module
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence.Process
public import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Sample
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Sampling
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Name.Basic (Named)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local

open Purelib.Approximation.Gaussian.Logarithm.Local.Horner

open Purelib.Approximation.Gaussian.Name.Sampling

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

section
@[expose] public section

/-!
# Local complex logarithm as a CCL computation

The input to this module is a progressive name for the reduced argument
`z = (u - 1) / (u + 1)`, together with the finite chart certificate that every
currently possible Gaussian-rational candidate has quadrance at most `1/9`.
Finite input refinement and finite Horner depth advance together.  No
completed complex value, infinite series, or global branch is introduced.
The resulting approximation is used as the accuracy sidechannel of a
productive CCL output name; a separate explicit chart supplies the global
branch correction.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Name

attribute [local irreducible] Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample.sample

/-- Evaluate the finite local-logarithm program on the certified input's canonical witness at the same depth. -/
def domainSample (input :
  Named) (disk : Domain.Disk input) (index : Nat) : Data.Gaussian.Basic.Canonical :=
  Sample.sampleFrom (Sampling.diskSamples input disk) index

/-- Later certified local-logarithm samples stay within the earlier index's combined geometric error allowance. -/
theorem domainSample_later_close {input :
  Named} (disk : Domain.Disk input)
    {oldIndex newIndex : Nat} (order : oldIndex ≤ newIndex) :
    Data.Gaussian.Norm.Basic.normSq
      (domainSample input disk newIndex -
      domainSample input disk oldIndex) ≤
      Geometric.Basic.quarterRadius Sample.errorScale oldIndex :=
  by
    change Data.Gaussian.Norm.Basic.normSq
        (Sample.sampleFrom (Sampling.diskSamples input disk) newIndex -
          Sample.sampleFrom (Sampling.diskSamples input disk) oldIndex) ≤
      Geometric.Basic.quarterRadius Sample.errorScale oldIndex
    exact @Sample.sampleFrom_later_close (Sampling.diskSamples input disk)
      oldIndex newIndex order

/-- Every certified local-logarithm sample has squared norm at most four. -/
theorem domainSample_bounded {input :
  Named} (disk : Domain.Disk input)
    (index : Nat) : Data.Gaussian.Norm.Basic.normSq
      (domainSample input disk index) ≤ 4 :=
  @Sample.sample_bounded
    (ComplexLog.inputSample input index) (Sampling.inputSample_bound disk index) index

/-- Package the certified local-logarithm samples with their explicit geometric error modulus.

The retained approximation carries terminating index refinement and a uniform squared-norm bound four for the original
disk-certified input. -/
def approximation (input :
  Named) (disk : Domain.Disk input) : ApproximationData where
  sample := domainSample input disk
  radiusSq := Geometric.Basic.quarterRadius Sample.errorScale
  radiusSq_nonneg index :=
    Geometric.Basic.quarterRadius_nonneg Sample.errorScale_nonneg index
  later_close := domainSample_later_close disk
  refineIndex current target _ :=
    Search.firstQuarterBelow Sample.errorScale current target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge Sample.errorScale current target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate Sample.errorScale
      Sample.errorScale_nonneg
  centerBound := 4
  centerBound_nonneg := by decide
  sample_bounded := domainSample_bounded disk

/-- Turn the certified local-logarithm approximation into a productive Gaussian process name. -/
def named (input :
  Named) (disk : Domain.Disk input) : Named :=
  (approximation input disk).toNamed
end Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Name

end
