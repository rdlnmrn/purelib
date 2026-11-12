module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Nat.Schedule.PositiveStride
public import Purelib.Examples.Integration.Polynomial.Gaussian.Partition.WorkedExamples
import Purelib.Integration.Program.Gaussian.Cached.Schedule
public import Purelib.Integration.Program.Gaussian.Polynomial.Schedule

import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.CCL.Program
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

@[expose] public section

/-!
Fixed and alternating polynomial policies under independent schedules.

Unit-stride and stride-five presentations retain equivalent integration
outputs for the same repeated curved path.
-/

namespace Purelib.Examples.Integration.Program.Gaussian.Schedule.WorkedExamples

open Purelib.Data.Nat.Schedule (PositiveStride)
open Purelib.Examples.Integration.Polynomial.Gaussian
open Purelib.Integration.Program.Gaussian.Cached

open Purelib.Approximation
open Purelib.Data
open Purelib
open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Integration
open Purelib.CCL.Progressive.IntegrationPrograms (polynomialProgram)

/-- The unit-stride schedule beginning at source index zero. -/
def slow :
  PositiveStride := ⟨0, 0⟩
/-- The stride-five schedule beginning at source index three. -/
def fast :
  PositiveStride := ⟨3, 4⟩

/-- The first three source indices of the stride-five schedule are 3, 8 and 13. -/
theorem positive_stride_indices :
    [fast.index 0,
      fast.index 1,
      fast.index 2] = [3, 8, 13] := by decide

/-- The retained fixed-policy polynomial program reindexed by the unit-stride schedule. -/
def fixed :=
  Schedule.reindexCached (polynomialProgram
  Partition.WorkedExamples.repeatedPath (.fixed
  Partition.WorkedExamples.repeatedRequest))
  slow
/-- The retained alternating-policy polynomial program reindexed by the stride-five schedule. -/
def alternating :=
  Schedule.reindexCached (polynomialProgram
  Partition.WorkedExamples.repeatedPath
  Partition.WorkedExamples.alternatingPolicy)
  fast

/-- The fixed and alternating polynomial policies produce equivalent names under their respective schedules. -/
def
  generated_policy_and_schedule_equivalence
  : Gaussian.Equivalence.NamedEquivalent
    fixed.output.name
      alternating.output.name :=
  Program.Gaussian.Polynomial.Schedule.polynomial_scheduled_outputs_equivalent
    Partition.WorkedExamples.repeatedPath _ _
    slow fast

end Purelib.Examples.Integration.Program.Gaussian.Schedule.WorkedExamples

end
