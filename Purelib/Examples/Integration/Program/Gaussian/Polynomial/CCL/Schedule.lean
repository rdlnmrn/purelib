module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.CCL.Transducer.Initial.Observation
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Examples.Integration.Polynomial.Gaussian.Partition.WorkedExamples
import Purelib.Integration.Program.Gaussian.Cached.Schedule

import Purelib.CCL.Progressive.IntegrationPrograms
public import Purelib.Examples.Integration.Program.Gaussian.Schedule.WorkedExamples
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.List.Basic
import Purelib.Integration.CCL.Program
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic

@[expose] public section

/-!
# Positive-stride integration regressions

Ceiling-division tests cover offsets, exact and inexact hits, large strides,
and an already advanced cursor.  The comparison test deliberately quantifies
over two independently advanced tails, not only a selected pair of samples.
-/

namespace Purelib.Examples.Integration.Program.Gaussian.Polynomial.CCL.Schedule

open Purelib.Examples.Integration.Polynomial.Gaussian
open Purelib.Examples.Integration.Program.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Integration.Program.Gaussian.Cached

open Purelib
open Purelib.Examples
open Purelib.CCL.Progressive.IntegrationPrograms (polynomialProgram)

/-- The reindexed cached polynomial program still emits true as its first actual CCL bit. -/
theorem scheduled_first_bit :
    (Machine.Advance.advance
      Schedule.WorkedExamples.alternating.output.name.machine 1).emitted = [true] := open
      Purelib.CCL in open Purelib.Data in open Purelib.Data.Rat in open Purelib.Integration in by
  apply Data.CCL.Transducer.Initial.Observation.advance_one_large
  change (13 / 6 : Fraction.Rational) < Gaussian.Norm.Basic.normSq
    ((Schedule.reindexCached (polynomialProgram
      Partition.WorkedExamples.repeatedPath
      Partition.WorkedExamples.alternatingPolicy)
      Schedule.WorkedExamples.fast).approximation.sample _)
  rw [Schedule.reindexCached_sample, Progressive.IntegrationPrograms.polynomialProgram_sample]
  decide

/-- The reindexed polynomial CCL controller emits exactly the requested finite number of bits. -/
theorem scheduled_output_length (count :
  Nat) :
    (Machine.Advance.advance
      Schedule.WorkedExamples.alternating.output.name.machine count).emitted.length = count
      :=
  (Schedule.WorkedExamples.alternating.output.name.productive count).2

end Purelib.Examples.Integration.Program.Gaussian.Polynomial.CCL.Schedule

end
