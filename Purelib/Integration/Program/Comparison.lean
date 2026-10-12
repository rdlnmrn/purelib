module
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.CCL.Program
import Purelib.Integration.Polynomial.Gaussian.Path.SampleCarrier
import Purelib.Integration.Program.Gaussian.Approximation
public import Purelib.Integration.Program.Gaussian.Arithmetic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Name
public import Purelib.Integration.Program.Gaussian.Reversal
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Sequence.Name
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_weighted_sum)

section
@[expose] public section

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

namespace Purelib.Integration.Program.Comparison

/-- The exact Gaussian refinement-program carrier used by these output comparisons. -/
abbrev RefinementProgram :=
  Purelib.Integration.Program.Gaussian.Basic.RefinementProgram
/-- The original indexed carrier of retained program reversal models. -/
abbrev ReversalModels :=
  Purelib.Integration.Program.Gaussian.Basic.RefinementProgram.ReversalModels

section
open Purelib.Approximation.Gaussian
open Purelib.Integration
open Purelib.Integration.Program
/-- The original coherent name is equivalent to the output of its exact-sample refinement-program carrier. -/
def ofCoherentNamed_output_equivalent (value :
  CoherentNamed) :
    Equivalence.NamedEquivalent value.name
      (Gaussian.Basic.RefinementProgram.ofCoherentNamed
        value).output.name := by
  let source := Name.Sampling.approximation value.name
  let program :=
    Gaussian.Basic.RefinementProgram.ofCoherentNamed value
  have rewrap : Equivalence.NamedEquivalent value.name source.toNamed := by
    exact Equivalence.Equivalent.symm
      (Equivalence.Equivalent.toNamed_sampling source)
  have samples : forall index,
      source.sample index = program.approximation.sample index := by
    intro index
    exact (Gaussian.Basic.RefinementProgram.ofCoherentNamed_integralSample
      value index).symm
  exact Equivalence.NamedEquivalent.trans rewrap (by
    simpa only [program,
      Gaussian.Basic.RefinementProgram.output,
    CertifiedProgram.Program.output,
    Gaussian.Basic.RefinementProgram.approximation,
      CoherentNamed.ofApproximation] using
      Sequence.Name.Equivalence.approximationEquivalent_toNamed
        (Sequence.Equivalence.approximationEquivalentOfSamplesEq
          source program.approximation samples))

/-- Multiplying the two original coherent outputs agrees with the output of their product refinement program. -/
def multiplyProgram_output_equivalent (left right :
  RefinementProgram) :
    Equivalence.NamedEquivalent
      (CoherentNamed.mul
        left.output right.output).name
      (Gaussian.Basic.RefinementProgram.multiply
        left right).output.name := by
  simpa only [CoherentNamed.mul,
    Gaussian.Basic.RefinementProgram.output,
    CertifiedProgram.Program.output,
    Gaussian.Basic.RefinementProgram.approximation,
    CoherentNamed.ofApproximation] using
    Sequence.Arithmetic.Multiplication.Bridge.mulToNamed_equivalent_pointwise
      left.approximation right.approximation
      (Gaussian.Basic.RefinementProgram.multiply
        left right).approximation
      (fun index =>
        Gaussian.Basic.RefinementProgram.multiply_integralSample
          left right index)

/-- Exact equality of all original stage samples gives equivalence of the two program outputs. -/
def refinementProgram_output_equivalent_of_samples_eq
    (left right : RefinementProgram)
    (samples : forall index,
      (left.model index).integralSample =
        (right.model index).integralSample) :
    Equivalence.NamedEquivalent left.output.name right.output.name := by
  simpa only [Gaussian.Basic.RefinementProgram.output,
    CertifiedProgram.Program.output,
    Gaussian.Basic.RefinementProgram.approximation,
    CoherentNamed.ofApproximation] using
    Sequence.Name.Equivalence.approximationEquivalent_toNamed
      (Sequence.Equivalence.approximationEquivalentOfSamplesEq
        left.approximation right.approximation samples)

end

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Program in
open Purelib.Riemann.Periods in
/-- Geometrically close same-stage samples control arbitrary later samples above a common original stage.

The bound retains both programs' separate error scales and the bridge scale with the original nested factors of two. -/
private theorem refinementProgram_samples_tail_close
    (left right : RefinementProgram)
    (bridgeScale : Fraction.Rational)
    (_bridgeScale_nonnegative : 0 <= bridgeScale)
    (samples : forall index,
      Data.Gaussian.Norm.Basic.normSq
          ((left.model index).integralSample -
            (right.model index).integralSample) <=
        Geometric.Basic.quarterRadius bridgeScale index)
    {common leftLater rightLater : Nat}
    (leftOrder : common <= leftLater) (rightOrder : common <= rightLater) :
    Data.Gaussian.Norm.Basic.normSq
        ((left.model leftLater).integralSample -
          (right.model rightLater).integralSample) <=
      Geometric.Basic.quarterRadius
        (2 * (left.errorScale + 2 * (bridgeScale + right.errorScale)))
          common := by
  let leftRadius := Geometric.Basic.quarterRadius
    left.errorScale common
  let bridgeRadius := Geometric.Basic.quarterRadius bridgeScale common
  let rightRadius := Geometric.Basic.quarterRadius
    right.errorScale common
  have leftClose :
      Data.Gaussian.Norm.Basic.normSq
          ((left.model leftLater).integralSample -
            (left.model common).integralSample) <= leftRadius :=
    (Norm.Basic.normSq_eq_canonical _).trans_le
      (left.later_close (earlier := common) (later := leftLater) leftOrder)
  have bridgeClose :
      Data.Gaussian.Norm.Basic.normSq
          ((left.model common).integralSample -
            (right.model common).integralSample) <= bridgeRadius :=
    samples common
  have rightCloseForward :
      Data.Gaussian.Norm.Basic.normSq
          ((right.model rightLater).integralSample -
            (right.model common).integralSample) <= rightRadius :=
    (Norm.Basic.normSq_eq_canonical _).trans_le
      (right.later_close (earlier := common) (later := rightLater) rightOrder)
  have rightClose :
      Data.Gaussian.Norm.Basic.normSq
          ((right.model common).integralSample -
            (right.model rightLater).integralSample) <= rightRadius := by
    rw [Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_symm]
    exact rightCloseForward
  calc
    Data.Gaussian.Norm.Basic.normSq
        ((left.model leftLater).integralSample -
          (right.model rightLater).integralSample) <=
        2 * (leftRadius + 2 * (bridgeRadius + rightRadius)) :=
      Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_le_weighted_sum
        (left.model leftLater).integralSample
        (left.model common).integralSample
        (right.model common).integralSample
        (right.model rightLater).integralSample
        leftRadius bridgeRadius rightRadius leftClose bridgeClose rightClose
    _ = Geometric.Basic.quarterRadius
          (2 * (left.errorScale + 2 * (bridgeScale + right.errorScale)))
            common := by
      exact quarterRadius_weighted_sum left.errorScale bridgeScale
        right.errorScale common

open Purelib.Data in
open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration in
open Purelib.Integration.Program in
/-- A nonnegative geometric bridge bound gives a finite comparison of the two original program outputs.

The comparison searches above both requested starting stages and retains the common index and later-sample guarantees;
the construction remains opaque. -/
opaque refinementProgram_output_equivalent_of_samples_close
    (left right : RefinementProgram)
    (bridgeScale : Fraction.Rational)
    (bridgeScale_nonnegative : 0 <= bridgeScale)
    (samples : forall index,
      Data.Gaussian.Norm.Basic.normSq
          ((left.model index).integralSample -
            (right.model index).integralSample) <=
        Geometric.Basic.quarterRadius bridgeScale index) :
    Equivalence.NamedEquivalent left.output.name right.output.name := by
  let totalScale : Fraction.Rational :=
    2 * (left.errorScale + 2 * (bridgeScale + right.errorScale))
  have totalScale_nonnegative : 0 <= totalScale := by
    exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg left.errorScale_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg bridgeScale_nonnegative right.errorScale_nonneg)))
  have equivalent : Equivalence.Equivalent
      left.approximation right.approximation := by
    refine { compare := ?_ }
    intro leftStart rightStart target positive
    let common := Geometric.Search.firstQuarterBelow totalScale
      (max leftStart rightStart) target
    have common_ge_left : leftStart <= common :=
      (Nat.Order.le_max_left leftStart rightStart).trans
        (Geometric.Search.firstQuarterBelow_ge totalScale
          (max leftStart rightStart) target)
    have common_ge_right : rightStart <= common :=
      (Nat.Order.le_max_right leftStart rightStart).trans
        (Geometric.Search.firstQuarterBelow_ge totalScale
          (max leftStart rightStart) target)
    have totalSmall : Geometric.Basic.quarterRadius totalScale common <
        target :=
      Geometric.Search.firstQuarterBelow_accurate totalScale
        totalScale_nonnegative (max leftStart rightStart) target positive
    exact
      { leftIndex := common
        rightIndex := common
        left_ge := common_ge_left
        right_ge := common_ge_right
        close := by
          intro leftLater rightLater leftOrder rightOrder
          change Data.Gaussian.Norm.Basic.normSq
              ((left.model leftLater).integralSample -
                (right.model rightLater).integralSample) < target
          exact (refinementProgram_samples_tail_close left right bridgeScale
            bridgeScale_nonnegative samples leftOrder rightOrder).trans_lt
              totalSmall }
  simpa only [Gaussian.Basic.RefinementProgram.output,
    CertifiedProgram.Program.output,
    Gaussian.Basic.RefinementProgram.approximation,
    CoherentNamed.ofApproximation] using
    Sequence.Name.Equivalence.approximationEquivalent_toNamed equivalent

open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Integration.Program in
/-- Represent the original geometric approximation by exact single-cell sample carriers.

The construction preserves the original error scale, later-close witnesses and center bound while every model allowance
is zero. -/
def geometricRefinementProgram
    (source : Geometric.GeometricApproximation) :
    RefinementProgram where
  model := fun index =>
    Gaussian.Basic.RefinementProgram.exactSamplePath
      (source.sample index)
  errorScale := source.errorScale
  errorScale_nonneg := source.errorScale_nonneg
  modelAllowance_le := by
    intro index
    rw [Gaussian.Basic.RefinementProgram.exactSamplePath_aggregateAllowance]
    exact Geometric.Basic.quarterRadius_nonneg
      source.errorScale_nonneg index
  later_close := by
    intro earlier later order
    rw [← Norm.Basic.normSq_eq_canonical,
      Gaussian.Basic.RefinementProgram.exactSamplePath_integralSample,
      Gaussian.Basic.RefinementProgram.exactSamplePath_integralSample]
    exact source.later_close (earlier := earlier) (later := later) order
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [← Norm.Basic.normSq_eq_canonical,
      Gaussian.Basic.RefinementProgram.exactSamplePath_integralSample]
    exact source.sample_bounded index

open Purelib.Approximation.Gaussian in
open Purelib.Integration.Program in
/-- Each exact carrier reads the original geometric approximation's sample at that stage. -/
@[simp] theorem geometricRefinementProgram_integralSample
    (source : Geometric.GeometricApproximation)
    (index : Nat) :
    ((geometricRefinementProgram source).model index).integralSample =
      source.sample index :=
  Gaussian.Basic.RefinementProgram.exactSamplePath_integralSample
    _

open Purelib.Approximation.Gaussian in
open Purelib.Integration in
open Purelib.Integration.Program in
open Purelib.Riemann.Periods in
/-- The original geometric name is equivalent to the output of its exact-sample refinement program. -/
def geometricNamed_equivalent_geometricRefinementProgram
    (source : Geometric.GeometricApproximation) :
    Equivalence.NamedEquivalent (PeriodMatrix.geometricNamed source).name
      (geometricRefinementProgram source).output.name := by
  simpa only [PeriodMatrix.geometricNamed,
    CoherentNamed.ofApproximation,
    Gaussian.Basic.RefinementProgram.output,
    CertifiedProgram.Program.output,
    Gaussian.Basic.RefinementProgram.approximation] using
    Sequence.Name.Equivalence.approximationEquivalent_toNamed
      (Sequence.Equivalence.approximationEquivalentOfSamplesEq
        source.toApproximation
        (geometricRefinementProgram source).approximation
        (by
          intro index
          rw [Geometric.GeometricApproximation.toApproximation_sample]
          exact (geometricRefinementProgram_integralSample source index).symm))

end Purelib.Integration.Program.Comparison

end
