module
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Program.Rational.Basic
public import Purelib.Integration.Program.Rational.Cached.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Integration.Polynomial.Rational.Path.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Polynomial.Rational.Path.Allowance
import Purelib.Data.Rat.Fraction.Order.Basic

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
open Purelib.Integration.Program.Rational in
/-- Read the Gaussian approximation sequence from the original rational program's certified view. -/
def approximation (program :
  Basic.RefinementProgram) : Sequence.ApproximationData :=
  (program.certifiedView).program.approximation

open Purelib.Data.Rat in
open Purelib.Integration.Program.Rational in
/-- The retained refinement procedure selects an original model with allowance below the positive target.

The returned index is the exact one selected from the supplied current index and target by the original certified
approximation. -/
theorem subdivision_accurate (program :
  Basic.RefinementProgram)
    (current : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    let index := program.approximation.refineIndex current target positive
    (program.model index).aggregateAllowance < target := by
  let prepared := (program.certifiedView).program.prepare ⟨current, target, positive⟩
  exact prepared.allowance_accurate
end RefinementProgram

end Purelib.Integration.Program.Rational.Basic

end
