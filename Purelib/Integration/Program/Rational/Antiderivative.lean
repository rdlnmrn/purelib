module

import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
public import Purelib.Integration.Polynomial.Rational.Antiderivative
public import Purelib.Integration.Program.Rational.Basic
import Purelib.Integration.Polynomial.Rational.Path.Basic
import Purelib.Data.Gaussian.Basic
meta import Purelib.Elab.ConstructiveInjectivity

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

namespace Purelib.Integration.Program.Rational
section RefinementProgram

open Purelib.Integration.Polynomial in
open Purelib.Integration.Program.Rational in
set_option genInjectivity false in
/-- A retained antiderivative certificate at each exact original program stage.

The path equality ties every certificate to the original stage model, preserving the polynomial path used for
endpoint-difference readback. -/
structure Basic.RefinementProgram.AntiderivativeProcess (program :
  Basic.RefinementProgram) where
  /-- The retained rational-polynomial path antiderivative certificate at each stage. -/ certificate : Nat →
    Rational.Antiderivative.PathAntiderivative
  /-- Every retained certificate uses the exact original program stage model. -/ path_eq : ∀ index, (certificate
    index).path = program.model index

constructive_injectivity Basic.RefinementProgram.AntiderivativeProcess

namespace Antiderivative.RefinementProgram.AntiderivativeProcess

open Purelib.Integration.Polynomial in
open Purelib.Integration.Program.Rational in
/-- The retained antiderivative difference sample equals the exact original stage integral sample. -/
theorem
  differenceSample_eq
  (program : Basic.RefinementProgram)
    (antiderivative : Basic.RefinementProgram.AntiderivativeProcess program) (index : Nat) :
    (antiderivative.certificate index).differenceSample =
      (program.model index).integralSample := by
  rw [Rational.Antiderivative.PathAntiderivative.differenceSample_eq_integralSample,
    antiderivative.path_eq]

end Antiderivative.RefinementProgram.AntiderivativeProcess
end RefinementProgram

end Purelib.Integration.Program.Rational

end
