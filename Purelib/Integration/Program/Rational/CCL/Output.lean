module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.CCL.Contract
import Purelib.Approximation.Gaussian.Name.Refinement
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Integration.Program.Rational.Basic
public import Purelib.Integration.Program.Rational.Name
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic

section
@[expose] public section

/-!
# General certified integration by finite path refinements

An integrand is supplied operationally: at each natural refinement it returns
one finite path of rational polynomial cell models and finite rational sample
certificates.  The integration program sums the exact polynomial cell
integrals.  A rational geometric modulus and a finite later-refinement
certificate turn those displayed sums into an ordinary productive CCL name.

There is no measure, completed partition, function-as-an-infinite-set, or
infinitesimal.  The only universal refinements are natural-number calls to the
supplied finite program.
-/

namespace Purelib.Integration.Program.Rational.Basic
namespace RefinementProgram

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
open Purelib.Integration.Program.Rational in
/-- The original rational program output supports an accurate refinement and exact finite CCL continuation.

The positive target bounds the retained ball radius; machine advancement preserves its emitted prefix, reaches the
requested bit length and retains the exact original process cursor. -/
theorem output_bitstream_and_error (program :
  Basic.RefinementProgram)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    let refined := Name.Refinement.refined
      program.output.name target positive
    (refined.process.ball refined.state).radiusSq < target ∧
      refined.machine.emitted.IsPrefix
        (Machine.Advance.advance
          refined.machine count).emitted ∧
      (Machine.Advance.advance
        refined.machine count).emitted.length = count ∧
      Machine.Semantics.Basic.ExactCursor
        refined.process refined.state
        (Machine.Advance.advance refined.machine count) :=
  Name.CCL.Contract.refined_bitstream_and_error
    program.output.name target positive count

end RefinementProgram

end Purelib.Integration.Program.Rational.Basic

end
