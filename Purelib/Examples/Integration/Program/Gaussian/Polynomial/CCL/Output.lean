module
import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Transducer.Initial.Observation
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Examples.Integration.Polynomial.Gaussian.Partition.WorkedExamples
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.List.Basic
import Purelib.Integration.CCL.Program
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic

@[expose] public section

/-!
# Generated polynomial partition regressions

All data are small; arithmetic examples use kernel decision at ordinary Lean
limits.  The symbolic results use the generic transport and partition proofs,
not a normalization of large concrete coefficient banks.
-/

namespace Purelib.Examples.Integration.Program.Gaussian.Polynomial.CCL.Output

open Purelib.Examples.Integration.Polynomial.Gaussian
open Purelib.Data.CCL.Transducer

open Purelib.CCL
open Purelib
open Purelib.Examples

/-- The cached repeated-path polynomial integration program actually emits true as its first bit. -/
theorem actual_first_bit :
    (Machine.Advance.advance
      (Progressive.IntegrationPrograms.polynomialProgram
        Partition.WorkedExamples.repeatedPath
        Partition.WorkedExamples.alternatingPolicy).output.name.machine 1).emitted =
        [true] := open Purelib.Data in open Purelib.Data.Rat in by
  apply Data.CCL.Transducer.Initial.Observation.advance_one_large
  change (13 / 6 : Fraction.Rational) < Data.Gaussian.Norm.Basic.normSq
    ((Progressive.IntegrationPrograms.polynomialProgram
      Partition.WorkedExamples.repeatedPath
      Partition.WorkedExamples.alternatingPolicy).approximation.sample _)
  rw [Progressive.IntegrationPrograms.polynomialProgram_sample]
  decide

/-- The retained polynomial integration cursor emits exactly the requested finite number of bits. -/
theorem actual_output_productive (count :
  Nat) :
    (Machine.Advance.advance
      (Progressive.IntegrationPrograms.polynomialProgram
        Partition.WorkedExamples.repeatedPath
        Partition.WorkedExamples.alternatingPolicy).output.name.machine
        count).emitted.length = count :=
  ((Progressive.IntegrationPrograms.polynomialProgram
    Partition.WorkedExamples.repeatedPath
    Partition.WorkedExamples.alternatingPolicy).output.name.productive count).2

end Purelib.Examples.Integration.Program.Gaussian.Polynomial.CCL.Output

end
