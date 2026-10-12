module
import Purelib.Approximation.Gaussian.Name.CCL.Contract
public import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Refinement
import Purelib.Data.CCL.Transducer.Machine.Advance
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic

public import Purelib.Integration.CertifiedProgram
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Name.Basic

@[expose] public section

namespace Purelib.Integration.CertifiedProgram.Program

variable {Model : Type u} {operations : ModelOperations Model}

open Purelib.Approximation.Gaussian in
/-- Read the coherent Gaussian name of the exact certified integration approximation. -/
def output (program : Program operations) : Name.Coherent.CoherentNamed :=
  Name.Coherent.CoherentNamed.ofApproximation program.approximation

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
/-- Refining the original output to a positive target gives its certified ball and an exact retained CCL bitstream
prefix.

Finite machine advancement preserves the refined prefix, emits the requested number of bits and keeps the exact original
process cursor semantics. -/
theorem output_bitstream_and_error (program : Program operations)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    let refined := Name.Refinement.refined program.output.name target positive
    (refined.process.ball refined.state).radiusSq < target ∧
      refined.machine.emitted.IsPrefix
        (Machine.Advance.advance refined.machine count).emitted ∧
      (Machine.Advance.advance refined.machine count).emitted.length = count ∧
      Machine.Semantics.Basic.ExactCursor refined.process refined.state
        (Machine.Advance.advance refined.machine count) :=
  Name.CCL.Contract.refined_bitstream_and_error program.output.name target positive count

end Purelib.Integration.CertifiedProgram.Program
