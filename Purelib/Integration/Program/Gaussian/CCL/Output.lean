module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.CCL.Contract
import Purelib.Approximation.Gaussian.Name.Refinement
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Integration.Program.Gaussian.Basic
public import Purelib.Integration.Program.Gaussian.Name
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Name.Basic

section
@[expose] public section

/-!
# Progressive finite integration with Gaussian coefficients

This is the period-facing integration kernel.  Every model is still a finite
list of rationally parameterized cells, but its local polynomial coefficients
are Gaussian rationals.  Hence a cell can approximate a genuinely complex
coefficient before multiplication by the complex path displacement.
-/

namespace Purelib.Integration.Program.Gaussian.Basic
namespace RefinementProgram

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
open Purelib.Integration.Program in
/-- The retained integration output supports a target-accurate refinement and exact finite CCL continuation.

The selected ball has radius below the positive target; advancing the retained machine preserves its emitted prefix,
produces the requested length and retains the exact process cursor. -/
theorem output_bitstream_and_error (program :
  Gaussian.Basic.RefinementProgram)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    let refined := Name.Refinement.refined
      program.output.name target positive
    (refined.process.ball refined.state).radiusSq < target ∧
      refined.machine.emitted.IsPrefix
        (Machine.Advance.advance refined.machine count).emitted ∧
      (Machine.Advance.advance
        refined.machine count).emitted.length = count ∧
      Machine.Semantics.Basic.ExactCursor
        refined.process refined.state
        (Machine.Advance.advance refined.machine count) :=
  Name.CCL.Contract.refined_bitstream_and_error
    program.output.name target positive count

end RefinementProgram

end Purelib.Integration.Program.Gaussian.Basic

end
