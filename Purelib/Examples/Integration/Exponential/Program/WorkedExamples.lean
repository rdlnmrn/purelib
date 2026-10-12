module
public import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Schedule.PositiveStride
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Integration.Exponential.Cached
public import Purelib.Integration.Exponential.Equivalence.Policy
import Purelib.Integration.Exponential.Geometry.Policy
import Purelib.Integration.Exponential.Program
import Purelib.Integration.Exponential.Selection
import Purelib.Integration.Partition.QuadraticWeight

import Purelib.Data.Rat.Fraction.Order
public import Purelib.Integration.Exponential.Equivalence.Existing
import Purelib.Integration.Exponential.Equivalence.Reference
import Purelib.Integration.Exponential.Uniform
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.CCL.Program
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Exponential.Polynomial.Source
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Segment.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic

@[expose] public section

/-!
# Automatically deepened exponential integration regressions

The coefficient tables are generated and integrated by the shared partition
kernel.  These examples exercise the degree selector and the actual CCL
output/replay path, not a constant cell containing the expected answer.
-/

namespace Purelib.Examples.Integration.Exponential.Program.WorkedExamples

open Purelib.Data.Nat.Schedule (PositiveStride)

open Purelib.Integration
open Purelib.Approximation
open Purelib.Data
open Purelib
open Purelib.Data.Rat
open Purelib.Examples

/-- The positive stride encoded by zero initial offset and zero extra step. -/
def unitStride :
  PositiveStride := ⟨0, 0⟩
/-- The positive stride encoded by initial offset two and extra step one. -/
def offsetStride :
  PositiveStride := ⟨2, 1⟩
/-- The fixed exponential partition policy cut at one third. -/
def fixedPolicy :
  Exponential.Geometry.Policy := Exponential.Geometry.Policy.fixedCuts
  [1 / 3]
/-- The alternating exponential partition policy combining a growing uniform partition with a fixed quarter cut. -/
def varyingPolicy :
  Exponential.Geometry.Policy := .alternating (.uniform 1 1)
  (Exponential.Geometry.Policy.fixedCuts [1 / 4])

/-- The automatically deepened exponential integration program with fixed third cut and unit stride. -/
def fixedProgram := Exponential.Program.program
  fixedPolicy unitStride 0
/-- The automatically deepened exponential program using the alternating policy, offset stride and one extra depth. -/
def varyingProgram := Exponential.Program.program
  varyingPolicy
  offsetStride 1

/-- The fixed-policy selector first chooses depth one. -/
theorem first_selected_depth :
  (Exponential.Selection.selection fixedPolicy
  unitStride 0).depth = 1 := by decide
/-- The alternating-policy selector first chooses depth two. -/
theorem other_first_depth :
  (Exponential.Selection.selection varyingPolicy
  offsetStride 0).depth = 2 := by decide

/-- The first fixed-policy integral sample is five thirds. -/
theorem fixed_first_sample :
  fixedProgram.approximation.sample 0 = ⟨5 / 3, 0⟩ := by
  rw [fixedProgram, Exponential.Program.program_sample,
    first_selected_depth]
  decide

/-- The first alternating-policy integral sample is 41/24. -/
theorem varying_first_sample :
  varyingProgram.approximation.sample 0 = ⟨41 / 24, 0⟩ := by
  rw [varyingProgram, Exponential.Program.program_sample,
    other_first_depth]
  decide +kernel

/-- The two policies produce different first integral samples. -/
theorem distinct_coarse_samples :
  fixedProgram.approximation.sample 0 ≠
  varyingProgram.approximation.sample 0 := by
  rw [fixed_first_sample,
    varying_first_sample]
  decide +kernel

/-- The actual fixed-program cell allowance is bounded by the requested stage quarter-radius. -/
theorem actual_model_allowances (stage : Nat) :
    (fixedProgram.stage stage).model.aggregateAllowance ≤
      Rational.Geometric.Basic.quarterRadius 10 stage := by
  have allowance := (fixedProgram.stage stage).allowance_eq
  change (fixedProgram.stage stage).allowance =
    (fixedProgram.stage stage).model.aggregateAllowance at allowance
  rw [← allowance]
  exact fixedProgram.modelAllowance_le stage

/-- Six tiny intervals and one interval 1,018 times as wide force the
selector to absorb an amplification greater than four. -/
def highlyUnevenPolicy :
  Exponential.Geometry.Policy :=
  Exponential.Geometry.Policy.fixedCuts [1 / 1024, 2 / 1024, 3 / 1024, 4 / 1024, 5 / 1024, 6 / 1024]

/-- The automatically deepened program retaining the seven-cell highly unequal partition policy. -/
def highlyUnevenProgram :=
  Exponential.Program.program highlyUnevenPolicy
  unitStride 0

/-- The highly unequal partition has exact amplification 3627155/524288. -/
theorem highly_uneven_amplification :
    Partition.QuadraticWeight.amplification
      (Exponential.Geometry.Policy.partitions highlyUnevenPolicy 0) =
        Fraction.Cast.fromInt 3627155 /
          Fraction.Cast.fromInt 524288 := by
  decide +kernel

/-- The highly unequal policy first selects depth two. -/
theorem highly_uneven_selected_depth :
    (Exponential.Selection.selection highlyUnevenPolicy
      unitStride 0).depth = 2 := by
  decide +kernel

/-- Even one ordinary degree increment is insufficient here.  The actual
constructor supplies the additional depth without a caller's error bound. -/
theorem highly_uneven_one_increment_insufficient
  :
    Rational.Geometric.Basic.quarterRadius 10 0 <
      (Exponential.Cached.compile 1
        (Exponential.Geometry.Policy.partitions highlyUnevenPolicy 0)
          0).allowance := by
  rw [Exponential.Cached.compile_allowance,
    highly_uneven_amplification]
  decide +kernel

/-- The actual highly unequal model allowance meets the requested stage quarter-radius. -/
theorem highly_uneven_actual_model_allowances
  (stage : Nat) :
    (highlyUnevenProgram.stage stage).model.aggregateAllowance ≤
      Rational.Geometric.Basic.quarterRadius 10 stage := by
  have allowance := (highlyUnevenProgram.stage stage).allowance_eq
  change (highlyUnevenProgram.stage stage).allowance =
    (highlyUnevenProgram.stage
      stage).model.aggregateAllowance at allowance
  rw [← allowance]
  exact highlyUnevenProgram.modelAllowance_le stage

/-- A retained finite equivalence comparison between the fixed and alternating integration programs. -/
def agreement : Gaussian.Equivalence.Equivalent
    fixedProgram.approximation
      varyingProgram.approximation :=
  Exponential.Equivalence.Policy.programs_equivalent fixedPolicy
    varyingPolicy
    unitStride
    offsetStride 0 1

/-- Compare the retained programs with unit tolerance and initial floors zero. -/
def compareOne :=
  agreement.compare 0 0 1 (by decide)
/-- Compare the retained programs with tolerance one hundredth and floors one and two. -/
def compareHundredth :=
  agreement.compare 1 2 (1 / 100)
    (by
      apply Fraction.Order.Field.div_pos_direct
      · decide
      · exact Fraction.Cast.Order.natCast_pos_direct (n := 100) (by decide))
/-- Compare the retained programs with tolerance one ten-thousandth and floors two and three. -/
def compareTenThousandth :=
  agreement.compare 2 3 (1 / 10000)
    (by
      apply Fraction.Order.Field.div_pos_direct
      · decide
      · exact Fraction.Cast.Order.natCast_pos_direct (n := 10000) (by decide))

/-- The displayed requests execute the finite synchronizer. -/
theorem synchronization_indices :
    [(compareOne.leftIndex,
      compareOne.rightIndex),
      (compareHundredth.leftIndex,
        compareHundredth.rightIndex),
      (compareTenThousandth.leftIndex,
        compareTenThousandth.rightIndex)] =
        [(3, 3), (6, 6), (10, 10)] := by decide +kernel

/-- Independently later samples remain within the paid one-hundredth squared-norm bound. -/
theorem independently_later_integrals {leftLater
  rightLater : Nat}
    (leftOrder : compareHundredth.leftIndex ≤ leftLater)
    (rightOrder : compareHundredth.rightIndex ≤ rightLater) :
    Data.Gaussian.Norm.Basic.normSq
      (fixedProgram.approximation.sample leftLater -
        varyingProgram.approximation.sample rightLater) < 1 / 100 :=
  compareHundredth.close leftOrder rightOrder

/-- The fixed and alternating program output names are equivalent. -/
def output_agreement :
  Gaussian.Equivalence.NamedEquivalent
    fixedProgram.output.name
      varyingProgram.output.name :=
  Exponential.Equivalence.Policy.outputs_equivalent fixedPolicy
    varyingPolicy
    unitStride
    offsetStride 0 1

/-- The fixed integration output is equivalent to the existing exponential-minus-one name. -/
def existing_exponential_minus_one_agreement :
  Gaussian.Equivalence.NamedEquivalent
    fixedProgram.output.name
      Exponential.Equivalence.Reference.exponentialMinusOne :=
  Exponential.Equivalence.Existing.output_equivalent_existing fixedPolicy
    unitStride 0

/-- The first two reference subtraction samples use source indices three and four. -/
theorem existing_subtraction_sampler_indices :
    [Exponential.Equivalence.Reference.referenceSourceIndex 0,
      Exponential.Equivalence.Reference.referenceSourceIndex 1] = [3, 4] := by decide +kernel

/-- Every stage of every displayed uniform policy has quadratic-weight amplification one. -/
theorem arbitrary_uniform_policy_factor
  (initialExtra growth stage : Nat) :
    Partition.QuadraticWeight.amplification (Exponential.Geometry.Policy.partitions (.uniform initialExtra growth)
      stage) = 1 :=
  Exponential.Uniform.uniform_policy_amplification initialExtra growth stage

end Purelib.Examples.Integration.Exponential.Program.WorkedExamples

end
