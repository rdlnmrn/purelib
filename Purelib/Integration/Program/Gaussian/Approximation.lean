module
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Program.Gaussian.Basic
public import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

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
open Purelib.Integration.Program.Gaussian in
/-- Read Gaussian approximation data from the exact original refinement program's certified view. -/
def approximation (program :
  Basic.RefinementProgram) : Sequence.ApproximationData :=
  (program.certifiedView).program.approximation

open Purelib.Data.Rat in
open Purelib.Integration.Program.Gaussian in
/-- The original program model at its requested refinement index has aggregate allowance below the positive target.

The request keeps its original current stage and target; the certified view supplies the retained selected-stage
accuracy witness. -/
theorem subdivision_accurate (program :
  Basic.RefinementProgram)
    (current : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    let index := program.approximation.refineIndex current target positive
    (program.model index).aggregateAllowance < target := by
  let prepared := (program.certifiedView).program.prepare ⟨current, target, positive⟩
  exact prepared.allowance_accurate
end RefinementProgram

end Purelib.Integration.Program.Gaussian.Basic

end
