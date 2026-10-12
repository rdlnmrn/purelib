module
public import Purelib.Approximation.Gaussian.Arithmetic.Sampling
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Integration.CCL.Program
public import Purelib.Integration.Program.Gaussian.Approximation
public import Purelib.Integration.Program.Gaussian.Arithmetic
public import Purelib.Integration.Program.Gaussian.Name
import Purelib.Approximation.Gaussian.Process.Coherence.Addition
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
public import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)

section
@[expose] public section

/-!
# Operational linearity of finite period programs

This module records orientation reversal and path concatenation at the actual
finite `PeriodProgram` layer.  It also exposes the already constructive
cellular-boundary and exact-primitive cancellation theorems through one small
interface used by family transport.

The stronger `CertifiedPeriodProgram` contains local algebraic observations.
Reversing those observations requires a new parameter-reversal certificate;
it is intentionally not inferred merely from reversal of the geometric path.
-/

namespace Purelib.Integration.Program.Comparison.Add

open Purelib.Approximation.Gaussian in
open Purelib.Integration in
open Purelib.Integration.Program in
/-- Adding the original coherent program outputs is equivalent to the retained sum program's output.

The supplied sum models keep the exact original stage-sample addition and allowance bounds used to build the comparison
certificate. -/
def addProgram_output_equivalent (left right :
  RefinementProgram)
    (models : Gaussian.Basic.RefinementProgram.SumModels
      left right) :
    Equivalence.NamedEquivalent
      (CoherentNamed.add
        left.output right.output).name
      (RefinementProgram.add
        left right models).output.name := by
  simpa only [CoherentNamed.add,
    RefinementProgram.output,
    CertifiedProgram.Program.output,
    RefinementProgram.approximation,
    CoherentNamed.ofApproximation] using
    Arithmetic.Sampling.addToNamed_equivalent_pointwise
      left.approximation right.approximation
      (RefinementProgram.add
        left right models).approximation
      (fun index =>
        RefinementProgram.add_integralSample
        left right models index)
end Purelib.Integration.Program.Comparison.Add

end
