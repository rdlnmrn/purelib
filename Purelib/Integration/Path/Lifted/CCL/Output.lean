module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Refinement
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
public import Purelib.Integration.Path.Lifted.Program
import Purelib.Integration.Program.Gaussian.CCL.Output
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
# Finite sheet-aware paths for period integration

A lifted path below is an inductive finite chain.  Every geometric edge
carries an explicit permutation of the labelled sheets and a proof that the
chosen endpoint sheet is the transported start sheet.  A separate inductive
relation verifies that a progressive integration model follows exactly the
same displayed geometric edges.  This separation lets several algebraic
differentials share one persistent lifted cycle while retaining their own
local polynomial integrand models.
-/

namespace Purelib.Integration.Path.Lifted.Program
namespace PeriodProgram

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Path.Lifted in
/-- The retained lifted-cycle output supports a target-accurate refinement and exact finite CCL continuation.

The refined ball remains tied to the original period program, and advancing its retained machine preserves the prefix
and exact cursor while producing the requested bit count. -/
theorem output_bitstream_and_error {sheets : Nat}
    {cycle : Lifted.Refinement.LiftedCycleRefinement sheets} (program : Program.PeriodProgram cycle)
    (target : Fraction.Rational)
    (positive : 0 < target)
    (count : Nat) :
    let refined := Name.Refinement.refined
      program.output.name target positive
    (refined.process.ball refined.state).radiusSq < target /\
      refined.machine.emitted.IsPrefix
        (Machine.Advance.advance
          refined.machine count).emitted /\
      (Machine.Advance.advance
        refined.machine count).emitted.length = count /\
      Machine.Semantics.Basic.ExactCursor
        refined.process refined.state
        (Machine.Advance.advance refined.machine count) :=
  program.integral.output_bitstream_and_error target positive count

end PeriodProgram
end Purelib.Integration.Path.Lifted.Program

end
